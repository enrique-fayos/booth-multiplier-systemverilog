# FPGA – DE2-115 top level

FPGA-specific modules used to run the Booth multiplier on an Intel/Altera DE2-115 board (EP4CE115F29C7).

## Files

- `multipli_EP4CE115F29C7.sv`  
  Top-level module. Instantiates the Booth multiplier and the 7-segment display logic.  
  The operands **A** and **B** are read from the switches. One push button is used to start the multiplication and another one to reset the design.  
  The 7-segment displays can show either the inputs or the result, selected using a switch.

- `bits_7seg_8.sv`  
  Converts an 8-bit binary value (operands A and B) to 7-segment digits using a shift/add (Double Dabble–style) algorithm together with `seg7_decoder`.

- `bits_7seg_16.sv`  
  Same conversion logic for a 16-bit binary value (multiplication result).

- `seg7_decoder.sv`  
  4-bit to 7-segment decoder used by the display modules.  
  The segment bit order is adapted to the custom DE2-115 pin mapping used in this project
  (it may look reversed compared to the official board documentation), but the same
  convention is applied in the Quartus Pin Planner, so the digits appear correctly on
  the physical 7-segment displays.

