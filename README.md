# guantanamera-ledger-source
Private UTXO blockchain in Common Lisp – Born in Guantánamo, Cuba

# Guantanamera Ledger — PRUEBA REAL EN VIVO (3 nodos + transacción)

https://github.com/lhmolam-ai/guantanamera-ledger-source/blob/main/prueva-en-vivo.txt

Acabo de ejecutar el código y esto pasó en menos de 10 segundos:

- Nodo A (semilla) → puerto 9700  
- Nodo B → puerto 9800  
- Nodo C arranca y descubre automáticamente A y B  
- Transacción de 100 tokens de A → C  
- Propagada y aceptada en los 3 nodos  
- Balances finales correctos  
- Cambio devuelto  
- Doble gasto imposible

Todo con un solo archivo: gtm_ledger.lisp

¡Descárgalo y ejecútalo tú mismo ahora mismo!
