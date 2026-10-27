# Simulador de Gravador (POS)

Par do Simulador de PDV: recebe pela rede os dados do PDV e mostra o overlay de POS
como um gravador Intelbras faria.

## Pareamento dos modos

| Gravador    | PDV         |
|-------------|-------------|
| TCP         | TCP Cliente |
| TCP_CLIENT  | TCP Servidor|
| UDP         | UDP         |

## Executável

O `.exe` é gerado pelo GitHub Actions (aba **Actions** > *Build SimuladorGravador.exe* > *Run workflow*).
Para publicar uma versão: crie uma tag `v1.0.0`; o `.exe` é anexado ao Release.
