# QEMU-TI-DSP

This repository is trying to implement TI C2000 DSP in QEMU.

## Build

```bash
mkdir build
cd build
../configure --target-list=c28x-softmmu
```

## Run

```bash
qemu-system-c28x -M c28xexample-board -bios path/to/your/binary
```
