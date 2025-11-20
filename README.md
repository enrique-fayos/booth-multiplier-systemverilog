# booth-multiplier-systemverilog

Signed Booth multiplier in SystemVerilog with testbenches, pipelined version and FPGA implementation.

## Features

- Signed Booth multiplication (two's complement operands)
- Non-pipelined and pipelined implementations
- SystemVerilog testbenches for functional verification
- Synthesizable top-level for FPGA demo

## Repository structure

- `rtl/` – synthesizable SystemVerilog sources (Booth multiplier cores)
- `tb/` – SystemVerilog testbenches for the cores
- `fpga/` – FPGA top-level and pin assignments created with Quartus Pin Planner

## Tools

- Any SystemVerilog-compatible simulator (e.g. ModelSim / Questa)
- Quartus Prime for FPGA synthesis and pin planning

## Status

The design has been simulated and tested on FPGA.
