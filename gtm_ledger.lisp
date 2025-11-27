(eval-when (:compile-toplevel :load-toplevel :execute)
  (ql:quickload '(:ironclad :usocket :babel :bordeaux-threads :split-sequence)))

;; ==================== ESTRUCTURAS (CORREGIDAS Y ESTABLES) ====================

(defstruct utxo-ref
  (tx-hash nil :type (or null (vector (unsigned-byte 8))))
  (output-index 0 :type integer))

(defstruct agente
  (clave-privada)
  ;; Usamos T para evitar el error de tipo en tiempo de compilación.
  (clave-publica nil :type (or null T)) 
  (utxos (make-hash-table :test 'equalp) :type hash-table) 
  (historial (make-hash-table :test 'equalp) :type hash-table) 
  (nonces-usados nil :type list)
  (utxos-gastados-conocidos (make-hash-table :test 'equalp))) 

(defstruct transaccion
  from
  to
  (inputs nil :type list)      
  (outputs nil :type list)     
  nonce
  signature
  sello)

(defstruct agente-remoto
  direccion
  puerto
  ;; Usamos T para evitar el error de tipo en tiempo de compilación.
  (clave-publica nil :type T)) 

(defvar *agentes-conocidos* (make-hash-table :test 'equal))
(defvar *host-default* "127.0.0.1")
(defvar *token-id-counter* 0)
(defvar *genesis-hash* (ironclad:digest-sequence :sha256 (babel:string-to-octets "GENESIS_TX_HASH")))

;; ==================== FUNCIONES CRÍTICAS CRIPTOGRÁFICAS ====================

(defun generar-par-de-claves-ed25519 ()
  (multiple-value-bind (priv pub) (ironclad:generate-key-pair :ed25519) (values priv pub)))

(defun firmar-mensaje-ed25519 (mensaje clave-privada)
  (let ((msg (if (stringp mensaje) (babel:string-to-octets mensaje) mensaje)))
    (ironclad:sign-message clave-privada msg)))

(defun verificar-firma-ed25519 (mensaje firma clave-publica)
  (let ((msg (if (stringp mensaje) (babel:string-to-octets mensaje) mensaje)))
    (ironclad:verify-signature clave-publica msg firma)))

(defun claves-iguales-p (clave1 clave2)
  (equalp (ironclad:ed25519-key-y clave1)
          (ironclad:ed25519-key-y clave2)))

(defun obtener-clave-publica-y (clave-publica-objeto)
  "Retorna el vector de bytes 'Y' de una clave pública de ironclad."
  (ironclad:ed25519-key-y clave-publica-objeto))

(defun obtener-id-a-partir-de-clave (clave-publica-objeto)
  "Retorna una versión corta (8 bytes) del hash de la clave pública Y como ID."
  (handler-case
      (subseq (ironclad:byte-array-to-hex-string (obtener-clave-publica-y clave-publica-objeto)) 0 16)
    (error (e)
      (format t "Error al obtener ID: ~a" e)
      "0000000000000000")))

(defun obtener-agente-id (agente-struct)
  "Retorna el ID del agente, independientemente de si es un AGENTE o AGENTE-REMOTO."
  (let ((clave-publica-objeto (if (typep agente-struct 'agente)
                                  (agente-clave-publica agente-struct)
                                  (agente-remoto-clave-publica agente-struct))))
    (obtener-id-a-partir-de-clave clave-publica-objeto)))
    
(defun serializar-utxo-ref (utxo-ref)
  "Convierte un UTXO-REF a una cadena para hashing/firma."
  (format nil "~a:~a" (ironclad:byte-array-to-hex-string (utxo-ref-tx-hash utxo-ref)) (utxo-ref-output-index utxo-ref)))

(defun serializar-transaccion-outputs (outputs)
  "Serializa una lista de outputs [clave-publica, monto] a [clave-publica-bytes, monto]."
  (mapcar (lambda (out)
            (list (ironclad:byte-array-to-hex-string (obtener-clave-publica-y (first out)))
                  (second out)))
          outputs))

(defun serializar-para-firma (trans)
  "Serializa los datos importantes de la transacción (incluyendo inputs y outputs) para firmar."
  (let ((inputs-str (format nil "~{~a~^|~}" (mapcar #'serializar-utxo-ref (transaccion-inputs trans))))
        (outputs-str (format nil "~a" (serializar-transaccion-outputs (transaccion-outputs trans)))))
    (babel:string-to-octets
     (format nil "~a:~a:~a:~a:~a"
             (ironclad:byte-array-to-hex-string (obtener-clave-publica-y (transaccion-from trans)))
             inputs-str
             outputs-str
             (transaccion-nonce trans)
             (transaccion-sello trans)))))

;; ==================== LÓGICA DEL AGENTE Y UTXOs ====================

(defun crear-agente (&optional (initial-value 1000))
  "Inicializa un agente con par de claves y un UTXO de Génesis."
  (multiple-value-bind (priv pub) (generar-par-de-claves-ed25519)
    (let ((agente (make-agente :clave-privada priv :clave-publica pub)))
      (let* ((utxo-ref (make-utxo-ref :tx-hash *genesis-hash* :output-index *token-id-counter*)))
        (incf *token-id-counter*)
        (setf (gethash utxo-ref (agente-utxos agente)) initial-value))
      agente)))

(defun obtener-balance (agente)
  "Calcula el balance del agente sumando todos sus UTXOs disponibles."
  (loop for valor being the hash-values of (agente-utxos agente)
        sum valor))

(defun seleccionar-utxos-para-gasto (agente monto)
  "Selecciona UTXO-Refs que sumen al menos el monto requerido."
  (let ((utxos-seleccionados '())
        (suma-actual 0))
    (when (< (obtener-balance agente) monto)
      (error "Balance insuficiente para gastar ~a" monto))
      
    (loop for utxo-ref being the hash-keys of (agente-utxos agente)
          for valor being the hash-values of (agente-utxos agente)
          until (>= suma-actual monto)
          do (push utxo-ref utxos-seleccionados)
             (incf suma-actual valor))
    
    (values utxos-seleccionados suma-actual)))

(defun capturar-contexto-local ()
  (list :timestamp (get-universal-time)))

(defun crear-transaccion (from-agente to-public-key monto nonce)
  "Crea, firma, y registra localmente el UTXO de cambio (flujo normal)."
  (multiple-value-bind (utxos-a-gastar suma-inputs) (seleccionar-utxos-para-gasto from-agente monto)
    (let* ((cambio (- suma-inputs monto))
           (contexto (capturar-contexto-local))
           (sello (ironclad:byte-array-to-hex-string (ironclad:digest-sequence :sha256 (babel:string-to-octets (prin1-to-string contexto)))))
           (outputs (list (list to-public-key monto)))
           (trans nil))
      
      (when (> cambio 0)
        (push (list (agente-clave-publica from-agente) cambio) outputs))
      
      (setf trans (make-transaccion
                   :from (agente-clave-publica from-agente)
                   :to to-public-key
                   :inputs utxos-a-gastar
                   :outputs (reverse outputs)
                   :nonce nonce
                   :sello sello))
                   
      (setf (transaccion-signature trans)
            (firmar-mensaje-ed25519 (serializar-para-firma trans)
                                    (agente-clave-privada from-agente)))
      
      ;; AUTOCONTROL CRIPTOGRÁFICO: Registra los UTXOs de cambio y marca los gastados.
      (format t "Info: Agente ~a registrando transacción (y cambio) localmente.~%" 
              (obtener-agente-id from-agente))
      
      (let ((tx-hash-original (ironclad:digest-sequence :sha256 (serializar-para-firma trans))))
          
          ;; 1. Registrar la TX en el historial (necesario para la cadena de propiedad)
          (setf (gethash tx-hash-original (agente-historial from-agente)) trans)
          
          ;; 2. Eliminar el UTXO viejo y registrar el UTXO de Cambio
          (dolist (utxo-ref utxos-a-gastar)
              (remhash utxo-ref (agente-utxos from-agente)))
              
          (loop for output in (transaccion-outputs trans)
                for index from 0 do
                (let ((receptor-key (first output))
                      (monto-out (second output)))
                  
                  (when (claves-iguales-p receptor-key (agente-clave-publica from-agente))
                    (let ((new-utxo-ref (make-utxo-ref :tx-hash tx-hash-original :output-index index)))
                      (setf (gethash new-utxo-ref (agente-utxos from-agente)) monto-out)
                      (format t "    -> UTXO de cambio registrado: ~a, Monto: ~a~%" (serializar-utxo-ref new-utxo-ref) monto-out)))))
          
          ;; 3. Marcar los inputs como gastados (para prevenir que A los use de nuevo)
          (dolist (utxo-ref utxos-a-gastar)
              (setf (gethash utxo-ref (agente-utxos-gastados-conocidos from-agente)) t))
          
          (push nonce (agente-nonces-usados from-agente)))
      
      trans)))

(defun validar-cadena-de-propiedad (receptor trans)
  "Verifica que los inputs de la transacción (UTXO-Refs) realmente existan y pertenezcan al emisor."
  (dolist (utxo-ref (transaccion-inputs trans))
    (let* ((tx-hash-previo (utxo-ref-tx-hash utxo-ref)))
      
      ;; Manejo del UTXO de Génesis
      (when (equalp tx-hash-previo *genesis-hash*)
        (format t "Info: Input es una UTXO Génesis. Confianza implícita.~%")
        (unless (>= (utxo-ref-output-index utxo-ref) 0) 
            (format t "Error: UTXO Génesis con índice inválido.~%")
            (return-from validar-cadena-de-propiedad nil))
        (go :siguiente-utxo)) 

      ;; Lógica de UTXO normal: Buscar la transacción previa en el historial.
      (let ((tx-previo (gethash tx-hash-previo (agente-historial receptor))))
        
        (unless tx-previo
          (format t "Error: NO SE PUDO RECUPERAR la transacción previa (~a). Posible UTXO ya gastado en otro lugar.~%" 
                  (ironclad:byte-array-to-hex-string tx-hash-previo))
          (return-from validar-cadena-de-propiedad nil))
        
        (unless (verificar-firma-ed25519 (serializar-para-firma tx-previo)
                                         (transaccion-signature tx-previo)
                                         (transaccion-from tx-previo))
          (format t "Error: La firma de la transacción previa es inválida.~%")
          (return-from validar-cadena-de-propiedad nil))
          
        (let ((output-previo (nth (utxo-ref-output-index utxo-ref) (transaccion-outputs tx-previo))))
          (unless (and output-previo
                       (claves-iguales-p (first output-previo) (transaccion-from trans)))
            (format t "Error: La salida en la TX previa no asigna el valor al emisor de esta transacción.~%")
            (return-from validar-cadena-de-propiedad nil)))))
  :siguiente-utxo) 
  t)

(defun procesar-transaccion (agente trans)
  "Procesa y valida la transacción recibida con la Cadena de Propiedad."
  (format t "=== INICIANDO PROCESAMIENTO DE TRANSACCIÓN en Agente ~a (UTXO Encadenado) ===~%"
          (obtener-agente-id agente))

  (when (member (transaccion-nonce trans) (agente-nonces-usados agente))
    (format t "Transacción rechazada: Nonce ~a ya usado.~%" (transaccion-nonce trans))
    (return-from procesar-transaccion nil))

  ;; DEFENSA CRÍTICA: DOBLE GASTO
  (dolist (utxo-ref (transaccion-inputs trans))
    (when (gethash utxo-ref (agente-utxos-gastados-conocidos agente))
        (format t "Transacción rechazada: UTXO ~a ya fue GASTADA en una transacción previa conocida (Doble Gasto).~%"
                (serializar-utxo-ref utxo-ref))
        (return-from procesar-transaccion nil)))

  (if (and
         (verificar-firma-ed25519 (serializar-para-firma trans) (transaccion-signature trans) (transaccion-from trans))
         (validar-cadena-de-propiedad agente trans))
         
      (progn
        (format t "=== TRANSACCIÓN ACEPTADA. NUEVOS UTXOs CREADOS. ===~%")
        
        ;; MARCAR INPUTS COMO GASTADOS
        (dolist (utxo-ref (transaccion-inputs trans))
            (setf (gethash utxo-ref (agente-utxos-gastados-conocidos agente)) t))
        
        ;; Eliminar UTXOs gastados (si los inputs le pertenecían)
        (dolist (utxo-ref (transaccion-inputs trans))
            (remhash utxo-ref (agente-utxos agente))) 
        
        (let ((tx-hash (ironclad:digest-sequence :sha256 (serializar-para-firma trans))))
            (setf (gethash tx-hash (agente-historial agente)) trans)
            
            ;; Registrar los nuevos UTXOs si son para ESTE agente
            (loop for output in (transaccion-outputs trans)
                  for index from 0 do
                  (let ((receptor-key (first output))
                        (monto-out (second output)))
                    
                    (when (claves-iguales-p receptor-key (agente-clave-publica agente))
                      (let ((new-utxo-ref (make-utxo-ref :tx-hash tx-hash :output-index index)))
                        (setf (gethash new-utxo-ref (agente-utxos agente)) monto-out)
                        (format t "-> UTXO creado: ~a, Monto: ~a~%" (serializar-utxo-ref new-utxo-ref) monto-out)))))
            
            (push (transaccion-nonce trans) (agente-nonces-usados agente))
            t))
      
      (progn
        (format t "Transacción rechazada por alguna validación.~%")
        nil)))

;; ==================== SERIALIZACIÓN Y COMUNICACIÓN (TCP FRAMING) ====================

(defun serializar-utxo-inputs (utxos)
  "Serializa una lista de UTXO-REF en una lista de listas [[hex_hash, index], ...]."
  (mapcar (lambda (u) 
            (list (ironclad:byte-array-to-hex-string (utxo-ref-tx-hash u)) 
                  (utxo-ref-output-index u))) 
          utxos))
          
(defun deserializar-transaccion-outputs (raw-outputs)
  "Deserializa la lista de outputs de [clave-publica-bytes, monto] a [clave-publica, monto]."
  (mapcar (lambda (out)
            (list (ironclad:make-public-key :ed25519 :y (ironclad:hex-string-to-byte-array (first out)))
                  (second out)))
          raw-outputs))

(defun serializar-transaccion (trans)
  "Serializa una transacción completa para enviar por red (en 7 partes)."
  (list (obtener-clave-publica-y (transaccion-from trans))
        (obtener-clave-publica-y (transaccion-to trans))
        (babel:string-to-octets (prin1-to-string (serializar-utxo-inputs (transaccion-inputs trans))))
        (babel:string-to-octets (prin1-to-string (serializar-transaccion-outputs (transaccion-outputs trans))))
        (babel:string-to-octets (princ-to-string (transaccion-nonce trans)))
        (ironclad:hex-string-to-byte-array (transaccion-sello trans))
        (transaccion-signature trans)))

(defun deserializar-transaccion (data-list)
  "Deserializa una lista de arreglos de bytes (7 partes) a una transacción."
  (when (= (length data-list) 7)
    (handler-case
        (let* ((raw-inputs (read-from-string (babel:octets-to-string (nth 2 data-list))))
               (reconstructed-inputs (mapcar (lambda (l) 
                                               (make-utxo-ref :tx-hash (ironclad:hex-string-to-byte-array (first l)) 
                                                              :output-index (second l))) 
                                             raw-inputs))
               (raw-outputs (read-from-string (babel:octets-to-string (nth 3 data-list))))
               (reconstructed-outputs (deserializar-transaccion-outputs raw-outputs))) 
          
          (make-transaccion
           :from (ironclad:make-public-key :ed25519 :y (nth 0 data-list))
           :to (ironclad:make-public-key :ed25519 :y (nth 1 data-list))
           :inputs reconstructed-inputs  
           :outputs reconstructed-outputs
           :nonce (parse-integer (babel:octets-to-string (nth 4 data-list)))
           :sello (ironclad:byte-array-to-hex-string (nth 5 data-list))
           :signature (nth 6 data-list)))
      (error (e)
        (format t "Error creando transacción desde bytes: ~a~%" e)
        nil))))

;; --- SERIALIZACIÓN DE AGENTES (PARA DESCUBRIMIENTO) ---

(defun serializar-agente-remoto (agente-remoto)
  "Serializa un AGENTE-REMOTO en una lista de valores atómicos, codificando la clave pública como cadena Hex."
  (list (agente-remoto-direccion agente-remoto)
        (agente-remoto-puerto agente-remoto)
        ;; CLAVE: Enviamos la clave como cadena hexadecimal (la corrección clave)
        (ironclad:byte-array-to-hex-string (obtener-clave-publica-y (agente-remoto-clave-publica agente-remoto))))) 

(defun deserializar-agente-remoto (raw-list)
  "Deserializa una lista de valores a un AGENTE-REMOTO (la clave es una cadena Hex)."
  (make-agente-remoto
   :direccion (first raw-list)
   :puerto (second raw-list)
   ;; CLAVE: Recreamos el vector de bytes tipado a partir de la cadena Hex
   :clave-publica (ironclad:make-public-key :ed25519 :y (ironclad:hex-string-to-byte-array (third raw-list)))))

(defun serializar-lista-agentes (agentes-ht)
  "Serializa la tabla global de agentes para el envío en red."
  (let ((agentes-list (loop for ag being the hash-values of agentes-ht collect ag)))
    (babel:string-to-octets (prin1-to-string (mapcar #'serializar-agente-remoto agentes-list)))))

;; --- TCP FRAMING UTILITIES ---

(defun escribir-datos-a-socket (stream data)
  "Escribe la longitud (4 bytes) seguida del payload de datos al stream TCP."
  (let ((size (length data))
        (size-buffer (make-array 4 :element-type '(unsigned-byte 8))))
    (setf (aref size-buffer 0) (ldb (byte 8 24) size))
    (setf (aref size-buffer 1) (ldb (byte 8 16) size))
    (setf (aref size-buffer 2) (ldb (byte 8 8) size))
    (setf (aref size-buffer 3) (ldb (byte 8 0) size))
    (write-sequence size-buffer stream)
    (write-sequence data stream)
    (force-output stream)))

(defun leer-secuencia (stream num-bytes)
  "Lee una secuencia garantizada de N bytes del stream."
  (let ((buffer (make-array num-bytes :element-type '(unsigned-byte 8)))
        (total-leido 0))
    (loop while (< total-leido num-bytes) do
          (let ((leido (read-sequence buffer stream :start total-leido)))
            (when (= leido 0) 
              (format t "Advertencia: Fin de stream inesperado.~%")
              (return-from leer-secuencia nil))
            (incf total-leido leido)))
    buffer))

(defun leer-datos-de-socket (stream)
  "Lee la longitud del payload (4 bytes) y luego el payload de datos del stream TCP."
  (let ((size-buffer (leer-secuencia stream 4)))
    (when size-buffer
      (let* ((payload-size (logior (ash (aref size-buffer 0) 24)
                                   (ash (aref size-buffer 1) 16)
                                   (ash (aref size-buffer 2) 8)
                                   (aref size-buffer 3))))
        (leer-secuencia stream payload-size)))))

;; ==================== LÓGICA DE RED TCP (SERVIDOR) ====================

(defun handle-transaccion-recepcion (stream agente)
  (let ((trans-data '()))
    ;; Se esperan 7 partes para una transacción
    (loop for i from 1 to 7 do
          (let ((data (leer-datos-de-socket stream))) (if data (push data trans-data) (return nil))))
    (let ((transaccion (deserializar-transaccion (reverse trans-data))))
      (if transaccion
          (if (procesar-transaccion agente transaccion)
              (escribir-datos-a-socket stream (babel:string-to-octets "OK"))
              (escribir-datos-a-socket stream (babel:string-to-octets "ERROR")))
          (escribir-datos-a-socket stream (babel:string-to-octets "INVALID"))))))

(defun handle-solicitud-pares (stream agente)
  "Envía la lista global de agentes conocidos."
  (declare (ignore agente))
  (let* ((serial-pares (serializar-lista-agentes *agentes-conocidos*))
         (msg-type (babel:string-to-octets "3"))) ; Código de Respuesta de Pares
    (escribir-datos-a-socket stream msg-type)
    (escribir-datos-a-socket stream serial-pares)
    (format t "    -> Se envió la lista de ~a pares al solicitante.~%" (hash-table-count *agentes-conocidos*))))

(defun handle-cliente (client-socket agente)
  "Manejador principal del hilo del servidor, lee el tipo de mensaje y delega."
  (unwind-protect
       (handler-case
           (let* ((stream (usocket:socket-stream client-socket))
                  (msg-type-bytes (leer-datos-de-socket stream)))
             (unless msg-type-bytes (return-from handle-cliente))
             (let ((msg-type (parse-integer (babel:octets-to-string msg-type-bytes))))
               (case msg-type
                 (1 (handle-transaccion-recepcion stream agente)) ; Transacción
                 (2 (handle-solicitud-pares stream agente))       ; Solicitud de Pares
                 (otherwise (format t "Tipo de mensaje desconocido: ~a~%" msg-type)))))
         (error (e)
           (format t "Error manejando cliente: ~a~%" e)))
    (usocket:socket-close client-socket)))

(defun iniciar-servidor (puerto agente)
  (let ((socket (usocket:socket-listen *host-default* puerto :reuse-address t)))
    (format t "Agente escuchando en ~a:~a~%" *host-default* puerto)
    (unwind-protect
         (loop
           (handler-case
               (let ((client-socket (usocket:socket-accept socket :element-type '(unsigned-byte 8))))
                 (bt:make-thread (lambda () (handle-cliente client-socket agente)))
                 (sleep 0.001)) ; Pequeño sleep para evitar saturación de CPU/SO
             (error (e) (format t "Error en servidor: ~a~%" e))))
      (usocket:socket-close socket))))

;; ==================== LÓGICA DE RED TCP (CLIENTE) ====================

(defun enviar-transaccion-red (transaccion host puerto)
  "Envía la transacción (Tipo 1) al host:puerto y espera respuesta 'OK'."
  (handler-case
      (let ((socket (usocket:socket-connect host puerto :element-type '(unsigned-byte 8) :timeout 15)))
        (unwind-protect
             (let* ((stream (usocket:socket-stream socket))
                    (msg-type-tx (babel:string-to-octets "1")) ; Tipo 1: Transacción
                    (trans-data (serializar-transaccion transaccion)))
               
               (escribir-datos-a-socket stream msg-type-tx)
               
               (dolist (data-part trans-data)
                 (escribir-datos-a-socket stream data-part))
                 
               (let ((response-bytes (leer-datos-de-socket stream)))
                 (when response-bytes
                   (string= "OK" (babel:octets-to-string response-bytes)))))
          (usocket:socket-close socket)))
    (error (e)
      (format t "Error enviando transacción a ~a:~a: ~a~%" host puerto e)
      nil)))

(defun solicitar-pares (host puerto)
  "Conecta al nodo semilla y solicita su lista de agentes conocidos (Tipo 2, espera Tipo 3)."
  (handler-case
      (let ((socket (usocket:socket-connect host puerto :element-type '(unsigned-byte 8) :timeout 15)))
        (unwind-protect
             (let* ((stream (usocket:socket-stream socket))
                    (solicitud-type (babel:string-to-octets "2"))) ; Tipo 2: Solicitud de Pares
               
               (escribir-datos-a-socket stream solicitud-type)
               
               (let ((response-type-bytes (leer-datos-de-socket stream)))
                 (when (and response-type-bytes (string= "3" (babel:octets-to-string response-type-bytes))) ; Espera Tipo 3
                   (let ((agentes-bytes (leer-datos-de-socket stream)))
                     (when agentes-bytes
                       (let* ((raw-list (read-from-string (babel:octets-to-string agentes-bytes)))
                              (agentes-remotos (mapcar #'deserializar-agente-remoto raw-list)))
                         (return-from solicitar-pares agentes-remotos)))))))
          (usocket:socket-close socket)))
    (error (e)
      (format t "Error solicitando pares a ~a:~a: ~a~%" host puerto e)
      nil)))


;; ==================== FUNCIONES DE INICIALIZACIÓN Y PRUEBA ====================

(defun clave-a-objeto-publico (clave)
  "Convierte una clave pública (puede ser vector de bytes Y, hex string, o un objeto ironclad) a un objeto IRONCLAD:ED25519-PUBLIC-KEY."
  (cond ((typep clave 'ironclad:ed25519-public-key) clave)
        ((typep clave '(vector (unsigned-byte 8))) 
         (ironclad:make-public-key :ed25519 :y clave))
        ((stringp clave)
         (ironclad:make-public-key :ed25519 :y (ironclad:hex-string-to-byte-array clave)))
        (t (error "Tipo de clave pública desconocido para conversión: ~a" clave))))

(defun registrar-agente (clave-publica host puerto)
  "Registra un agente remoto o local. Asegura que la clave pública sea un objeto IRONCLAD::PUBLIC-KEY."
  (let* ((clave-objeto (clave-a-objeto-publico clave-publica))
         (key-y-bytes (obtener-clave-publica-y clave-objeto)))
    
    (setf (gethash (ironclad:byte-array-to-hex-string key-y-bytes) *agentes-conocidos*)
          (make-agente-remoto :direccion host :puerto puerto :clave-publica clave-objeto))))

(defun encontrar-puerto-disponible (puerto-base &optional (max-intentos 50))
  (dotimes (i max-intentos)
    (let ((puerto-test (+ puerto-base i)))
      (handler-case
          (let ((socket (usocket:socket-listen *host-default* puerto-test :reuse-address t)))
            (usocket:socket-close socket)
            (return-from encontrar-puerto-disponible puerto-test))
        (usocket:address-in-use-error () nil)
        (error (e) (format t "Error probando puerto ~a: ~a~%" puerto-test e)))))
  (error "No se pudo encontrar puerto disponible después de ~a intentos" max-intentos))

(defun propagar-transaccion (transaccion agente-emisor)
  "Envía la transacción a todos los agentes conocidos EXCEPTO al emisor en un HILO SEPARADO."
  (let ((emisor-key-y (obtener-clave-publica-y (agente-clave-publica agente-emisor)))
        (agentes-a-propagar (loop for ag being the hash-values of *agentes-conocidos* collect ag)))
    
    (bt:make-thread 
        (lambda ()
          (format t "Info: Iniciando propagación de TX T1 en hilo separado.~%")
          (loop for agente-remoto in agentes-a-propagar do
                (handler-case
                    (let ((receptor-key-y (obtener-clave-publica-y (agente-remoto-clave-publica agente-remoto))))
                      (unless (equalp emisor-key-y receptor-key-y) 
                        (format t "    -> Propagando a ~a:~a... " (agente-remoto-direccion agente-remoto) (agente-remoto-puerto agente-remoto))
                        (if (enviar-transaccion-red transaccion (agente-remoto-direccion agente-remoto) (agente-remoto-puerto agente-remoto))
                            (format t "OK.~%")
                            (format t "FALLÓ (respuesta no OK).~%"))))
                  (error (e)
                    (format t "Advertencia: Error de red o conexión al propagar a ~a:~a: ~a~%" 
                            (agente-remoto-direccion agente-remoto) (agente-remoto-puerto agente-remoto) e)))))
        :name "TX-PROPAGATOR")))


(defun iniciar-agente (puerto &key (host *host-default*) (initial-value 1000) (seed-host nil) (seed-port nil))
  "Inicia un agente, y opcionalmente contacta a un nodo semilla para descubrir pares."
  (let ((agente (crear-agente initial-value)))
    
    ;; 1. Registrar el agente local en el hash global
    (registrar-agente (agente-clave-publica agente) host puerto)
    
    (bt:make-thread (lambda () (iniciar-servidor puerto agente))
                    :name (format nil "TCP-SERVER-~a" puerto))

    ;; 2. Lógica de Descubrimiento (Cliente)
    (when (and seed-host seed-port)
      (let ((pares-descubiertos (solicitar-pares seed-host seed-port))
            (agente-public-key-y (obtener-clave-publica-y (agente-clave-publica agente))))
        (dolist (agente-remoto pares-descubiertos)
          (let ((remoto-public-key-y (obtener-clave-publica-y (agente-remoto-clave-publica agente-remoto))))
            
            (unless (equalp agente-public-key-y remoto-public-key-y)
              (registrar-agente (agente-remoto-clave-publica agente-remoto) 
                                (agente-remoto-direccion agente-remoto) 
                                (agente-remoto-puerto agente-remoto))
              (format t "    -> Pares nuevos: Registrando agente en ~a:~a.~%" 
                      (agente-remoto-direccion agente-remoto) (agente-remoto-puerto agente-remoto)))))))
    
    agente))

(defun prueba-de-uso-normal-con-descubrimiento ()
  "Inicializa A (Semilla), B, y C (Descubre a A y B) y simula A -> C."
  (format t "~%~%=== INICIANDO PRUEBA CON DESCUBRIMIENTO DE PARES (TCP) ===~%~%")
  
  (clrhash *agentes-conocidos*) ; Limpiar tabla para la prueba
  
  ;; Paso 1: Inicializar Agentes A y B (Serán conocidos por la Semilla)
  (let* ((puerto-a (encontrar-puerto-disponible 9700))
         (puerto-b (encontrar-puerto-disponible 9800))
         (puerto-c (encontrar-puerto-disponible 9900))
         (agente-a (iniciar-agente puerto-a :initial-value 2000)) ; Agente Semilla
         (agente-b (iniciar-agente puerto-b))) 

    (sleep 3) ;; Espera para que A y B se registren y sus servidores estén ON

    (format t "~%--- ESTADO INICIAL DE LA RED (A y B son conocidos globalmente) ---~%")
    (format t "Agente A (Semilla) ID: ~a. Puerto: ~a. Balance: ~a tokens.~%" 
            (obtener-agente-id agente-a) puerto-a (obtener-balance agente-a))
    (format t "Agente B ID: ~a. Puerto: ~a. Balance: ~a tokens.~%" 
            (obtener-agente-id agente-b) puerto-b (obtener-balance agente-b)) 
    (format t "Agentes Conocidos (Hash Global): ~a~%" (hash-table-count *agentes-conocidos*)) 

    ;; Paso 2: Inicializar Agente C y pedirle que descubra a través de A (Semilla)
    (format t "~%--- [3] AGENTE C SE INICIA Y CONTACTA A A (SEMILLA) ---~%")
    (let ((agente-c (iniciar-agente puerto-c :seed-host *host-default* :seed-port puerto-a)))
        
        (sleep 2) ;; Espera el hilo de descubrimiento
        
        (format t "~%-> Resultados del Descubrimiento en Agente C:~%")
        (format t "   Agente C ID: ~a. Balance: ~a tokens.~%" (obtener-agente-id agente-c) (obtener-balance agente-c))
        (format t "   Agentes Conocidos (Hash Global): ~a~%" (hash-table-count *agentes-conocidos*))

        ;; Paso 3: Simular una transacción de A a C
        (format t "~%--- [4] Transacción (A -> C): Enviando 100 tokens ---~%")
        (let* ((tx (crear-transaccion agente-a (agente-clave-publica agente-c) 100 1))
               (balance-a-antes (obtener-balance agente-a)) ; Debe ser 2000 - 100 = 1900
               (balance-c-antes (obtener-balance agente-c))) ; Debe ser 1000
            
            (format t "Info: Propagando T1 (A->C) a la red (A, B, C)... ~%")
            (propagar-transaccion tx agente-a)
            
            (sleep 4) ; Espera AUMENTADA para que los hilos de red y propagación terminen

            (format t "~%-> Resultados Finales:~%")
            ;; El balance de A debe ser 1900 (2000 inicial - 100 enviados = 1900). 
            ;; Ajustamos la etiqueta de "Esperado" para que coincida con la lógica:
            (format t "   Balance A: ~a (Esperado: ~a)~%" (obtener-balance agente-a) (- 2000 100)) 
            (format t "   Balance B: ~a (Sin cambios: ~a)~%" (obtener-balance agente-b) (obtener-balance agente-b))
            (format t "   Balance C: ~a (Esperado: ~a)~%" (obtener-balance agente-c) (+ balance-c-antes 100)))))
            
    (format t "~%=== PRUEBA DE USO FINALIZADA ===~%"))

(prueba-de-uso-normal-con-descubrimiento)