// --------------------------------------------------------------------
// Universitat Politècnica de València
// Escuela Técnica Superior de Ingenieros de Telecomunicación
// --------------------------------------------------------------------
// Integración Sistemas Digitales
// Curso 2025-26
// --------------------------------------------------------------------
// Nombre del archivo: tb_multipli_simple.sv
//
// Descripción: Banco de pruebas sencillo para el módulo 'multipli'.
//              Genera un reloj, aplica un reset inicial y lanza un único
//              vector de prueba sobre A y B para verificar la operación
//              de multiplicación y la activación de END_MULT.
//
// Parámetros:
//   N : Ancho de palabra (bits) de los operandos A y B.
//   T : Período del reloj en nanosegundos.
//
// Entradas y salidas principales (vista TB):
//   CLOCK, RESET : Señales generadas en el TB y conectadas al DUT.
//   START        : Pulso de inicio de la operación de multiplicación.
//   A, B         : Operandos de entrada aplicados desde el TB.
//   S            : Resultado de la multiplicación (observado desde el TB).
//   END_MULT     : Flag de fin de operación generado por el DUT.
//
// Dependencias/instancias:
//   - multipli : DUT (multiplicador secuencial firmado).
//
// Notas de implementación:
//   - Reloj generado con un proceso always de período T.
//   - Tarea de reset 'apply_reset' que inicializa señales y libera RESET.
//   - Secuencia de estímulos única con espera a END_MULT.
//   - Se usa $stop al final para pausar la simulación en el simulador.
//
// --------------------------------------------------------------------
// Versión: v1.0 | Fecha Modificación: 13/11/2025
//
// Autores: Enrique Fayos Gimeno y Jairo Gónzalez Ibáñez
//
// --------------------------------------------------------------------
`timescale 1 ns/ 100 ps

module tb_multipli_simple();

// SIGNALS
localparam int N = 8;
localparam int T = 20;

logic	CLOCK;
logic	RESET;     
logic	START;
logic	[N-1:0]A,B;
logic	[2*N-1:0]S;
logic	END_MULT;

// CLOCK
initial CLOCK = 1'b0;
always #(T/2) CLOCK = ~CLOCK;

// UUT
  // UUT
  multipli #(.N(N)) uut (
    .CLOCK    (CLOCK),
    .RESET    (RESET),
    .START    (START),
    .A        (A),
    .B        (B),
    .S        (S),
    .END_MULT (END_MULT)
  );

// TASK RESET INICIALIZACION
task automatic apply_reset;
  begin
    RESET = 1'b0;                   
    A = '0; B = '0; START = 1'b0;
    repeat (2) @(negedge CLOCK);
    RESET = 1'b1;                   
    @(negedge CLOCK);
  end
endtask

// ESTIMULOS
initial begin
  apply_reset();
  
  A = 8'd120; B = -8'd128;
  @(negedge CLOCK); START = 1'b1;
  @(negedge CLOCK); START = 1'b0;
  wait (END_MULT);
  
  $stop;
end
endmodule

