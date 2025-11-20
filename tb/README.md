# Testbenches

This directory contains the SystemVerilog testbenches used to verify the Booth multiplier cores.

## Files

- `tb_multipli.sv`  
  Main, feature-complete testbench.  
  Uses **program blocks, clocking blocks, interfaces, a golden model and queues** to:
  - generate stimulus
  - compare DUT outputs against the reference model
  - check corner cases and signed behaviour

- `tb_multipli_simple.sv`  
  Minimal functional testbench with **hand-picked test vectors**.  
  Useful as a first sanity check of the multiplier before running the full environment.

- `tb_mutipli_pipelined.sv`  
  Testbench for the **pipelined** Booth multiplier.  
  Reuses parts of `tb_multipli.sv` and uses **queues** to align expected and actual results according to the pipeline latency.

- `multipli_parallel.sv`  
  Parallel multiplier used as a **golden reference model** to validate the DUT.  
  This file was provided by the course instructors.

## Notes

All testbenches are written in SystemVerilog and target the same interface as the RTL cores.
