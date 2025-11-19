// --------------------------------------------------------------------
// Universitat Politècnica de València
// Escuela Técnica Superior de Ingenieros de Telecomunicación
// --------------------------------------------------------------------
// Integración Sistemas Digitales
// Curso 2025-26
// --------------------------------------------------------------------
// Nombre del archivo: multipli_EP4CE115F29C7.sv
//
// Descripción: Top de integración para FPGA (EP4CE115F29C7) del
//              multiplicador secuencial 'multipli'. Lee operandos A y B
//              desde los switches, lanza la operación mediante un botón,
//              y muestra en los displays de 7 segmentos tanto los
//              operandos (modo A/B) como el resultado (modo S) en
//              representación decimal con signo.
//
// Interfaz (FPGA):
//   CLOCK       : Reloj de la placa.
//   BTN_RESET   : Botón de reset (se conecta al RESET del DUT).
//   BTN_START   : Botón de inicio de operación (invertido para generar START).
//   SW_AB_to_S  : Selector de modo visualización (0 = A/B, 1 = S).
//   SW_A[7:0]   : Switches para operando A (8 bits, firmado).
//   SW_B[7:0]   : Switches para operando B (8 bits, firmado).
//   HEX0..HEX7  : Displays de 7 segmentos activos a nivel bajo.
//
// Dependencias/instancias:
//   - multipli       : multiplicador secuencial firmado (N=8).
//   - bits_7seg_8    : conversor 8 bits signed → 4 displays (decimal).
//   - bits_7seg_16   : conversor 16 bits signed → 8 displays (decimal).
//   - seg7_decoder   : decodificador 4 bits → 7 segmentos (activo-bajo).
//
// Notas de implementación:
//   - BTN_START se invierte para generar START activo-alto hacia 'multipli'.
//   - En modo A/B (SW_AB_to_S=0) los 8 displays muestran A (HEX7..HEX4)
//     y B (HEX3..HEX0) en decimal con signo (8 bits).
//   - En modo S (SW_AB_to_S=1) los 8 displays muestran el resultado S
//     (16 bits signed) en decimal con signo.
//   - La lógica de multiplicación y formateo decimal está delegada en
//     los módulos instanciados; este top sólo realiza el “cableado”
//     y el multiplexado de las salidas de los displays.
//
// --------------------------------------------------------------------
// Versión: v1.0 | Fecha Modificación: 13/11/2025
//
// Autores: Enrique Fayos Gimeno y Jairo Gónzalez Ibáñez
//
// --------------------------------------------------------------------
module multipli_EP4CE115F29C7
(
  input  logic        CLOCK,
  input  logic        BTN_RESET,
  input  logic        BTN_START,
  input  logic        SW_AB_to_S,
  input  logic [7:0]  SW_A,
  input  logic [7:0]  SW_B,
  output logic [6:0]  HEX0, HEX1, HEX2, HEX3,
  output logic [6:0]  HEX4, HEX5, HEX6, HEX7
);
// -------------------- Señales internas --------------------
logic signed [15:0] S;
logic END_MULT;

// Salidas para el modo "A y B" (decimal 8 bits)
logic [6:0] HEX0_AB, HEX1_AB, HEX2_AB, HEX3_AB;
logic [6:0] HEX4_AB, HEX5_AB, HEX6_AB, HEX7_AB;

// Salidas para el modo "S" (decimal 16 bits)
logic [6:0] HEX0_S, HEX1_S, HEX2_S, HEX3_S;
logic [6:0] HEX4_S, HEX5_S, HEX6_S, HEX7_S;
// ---------------- Instancia del multiplicador ----------------
multipli #(.N(8)) uut (
  .CLOCK    (CLOCK),
  .RESET    (BTN_RESET), 
  .START    (!BTN_START),
  .A        (SW_A),
  .B        (SW_B),
  .S        (S),
  .END_MULT (END_MULT)
);
// -----------------------------------------------------------
// MODO 1: Mostrar A y B en decimal con bits_7seg (8 bits)
//   - Izquierda (HEX7..HEX4)  = A
//   - Derecha   (HEX3..HEX0)  = B
// -----------------------------------------------------------
bits_7seg_8 disp_A (
  .Svalue (SW_A),      
  .seg3   (HEX7_AB),
  .seg2   (HEX6_AB),
  .seg1   (HEX5_AB),
  .seg0   (HEX4_AB)
);
bits_7seg_8 disp_B (
  .Svalue (SW_B),
  .seg3   (HEX3_AB),
  .seg2   (HEX2_AB),
  .seg1   (HEX1_AB),
  .seg0   (HEX0_AB)
);
// -----------------------------------------------------------
// MODO 2: Mostrar S (16 bits signed) en decimal con bits_7seg_16
//  - Usa los 8 displays: HEX7..HEX0
// -----------------------------------------------------------
bits_7seg_16 disp_S (
  .Svalue (S),
  .seg7   (HEX7_S),
  .seg6   (HEX6_S),
  .seg5   (HEX5_S),
  .seg4   (HEX4_S),
  .seg3   (HEX3_S),
  .seg2   (HEX2_S),
  .seg1   (HEX1_S),
  .seg0   (HEX0_S)
);
// -----------------------------------------------------------
// MULTIPLEXOR FINAL DE LOS 8 DISPLAYS
//   SW_AB_to_S = 0 -> se ven A y B (decimal, 8 bits)
//   SW_AB_to_S = 1 -> se ve sólo S (decimal, 16 bits) en todos los HEX
// -----------------------------------------------------------
always_comb begin
  if (SW_AB_to_S == 1'b0) begin
    // Modo A/B
    HEX0 = HEX0_AB;
    HEX1 = HEX1_AB;
    HEX2 = HEX2_AB;
    HEX3 = HEX3_AB;
    HEX4 = HEX4_AB;
    HEX5 = HEX5_AB;
    HEX6 = HEX6_AB;
    HEX7 = HEX7_AB;
  end else begin
    // Modo resultado S
    HEX0 = HEX0_S;
    HEX1 = HEX1_S;
    HEX2 = HEX2_S;
    HEX3 = HEX3_S;
    HEX4 = HEX4_S;
    HEX5 = HEX5_S;
    HEX6 = HEX6_S;
    HEX7 = HEX7_S;

  end
end
endmodule
