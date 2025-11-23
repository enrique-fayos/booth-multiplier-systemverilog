// --------------------------------------------------------------------
// Universitat Politècnica de València
// Escuela Técnica Superior de Ingenieros de Telecomunicación
// --------------------------------------------------------------------
// Integración Sistemas Digitales
// Curso 2025-26
// --------------------------------------------------------------------
// Nombre del archivo: tb_multipli_pipelined.sv
//
// Descripción: Banco de pruebas para el multiplicador pipelined
//              'multipli_pipelined'. Utiliza una interface SystemVerilog
//              (bus_mult), generación aleatoria constrained de estímulos,
//              colas para comparar salidas (DUT vs. golden model aritmético
//              calculado en el propio testbench) y cobertura funcional sobre
//              los operandos A y B.
//
// Parámetros:
//   N : Ancho de palabra de los operandos A y B (bits).
//
// Entradas y salidas principales:
//   CLOCK, RESET : Señales de reloj y reset compartidas por DUT, generadas
//                  en el testbench.
//   A, B         : Operandos de entrada, conducidos a través de la
//                  interface bus_mult.
//   S, END_MULT   : Resultado y flag de fin de operación del DUT.
//
// Dependencias/instancias:
//   - multipli_pipelined                    : DUT (multiplicador pipelined).
//   - multipli_pipelined_bus_wrapper_*      : Wrappers que conectan el DUT a bus_mult.
//   - Clase Aleatorizar                      : Generador de operandos aleatorios con constraints.
//   - Programa estimulos                     : Generación de estímulos, cobertura y checks.
//
// Notas de implementación:
//   - Se usan clocking blocks (md/sd) para separar monitor y driver.
//   - Comparación mediante colas entre las salidas del DUT y el golden model
//     aritmético (A * B) calculado en el program (stimulus).
//   - Cobertura funcional cruzada sobre A y B.
//   - Testbench orientado a gate-level/RTL según wrapper instanciado.
//
// --------------------------------------------------------------------
// Versión: v1.0 | Fecha Modificación: 14/11/2025
//
// Autores: Enrique Fayos Gimeno y Jairo Gónzalez Ibáñez
//
// --------------------------------------------------------------------
`timescale 1 ns/ 100 ps
interface bus_mult #(parameter N = 8) 
(input logic CLOCK, input logic RESET);
  logic  START;
  logic  signed [N-1:0] A, B;
  logic  signed [2*N-1:0] S;
  logic  END_MULT;
  // Clocking block de MONITOR DOMAIN (solo lee)
  clocking md @(posedge CLOCK);
    input #1 START;
    input #1 A, B;
    input #1 S, END_MULT;
  endclocking
  // Clocking block de STIMULUS DOMAIN (driver)
  clocking sd @(posedge CLOCK);
    output #2 START;
    output #2 A, B;
    input  #2 S, END_MULT;
  endclocking
  //Seccion de modports
  modport tb( 
    clocking md,
    clocking sd,
    input RESET
  );
  modport dut( 
    input  CLOCK, RESET, START, A, B,
    output S, END_MULT
  );
endinterface

class Aleatorizar #(parameter int N = 8);
  randc logic signed [N-1:0] valorA;
  randc logic signed [N-1:0] valorB;  
  constraint pospos {valorA[N-1] == 1'b0 && valorB[N-1] == 1'b0; };
  constraint negneg {valorA[N-1] == 1'b1 && valorB[N-1] == 1'b1; };
  constraint posneg {valorA[N-1] == 1'b0 && valorB[N-1] == 1'b1; };
  constraint negpos {valorA[N-1] == 1'b1 && valorB[N-1] == 1'b0; };
endclass

program estimulos #( parameter int N = 8)(bus_mult.tb bus);
  logic signed [2*N-1:0] q_dut[$]; // Cola del dut
  logic signed [2*N-1:0] q_gm[$]; // Cola del ref
  logic signed [2*N-1:0] qS_dut_dbg[$]; // Cola de debug dut
  logic signed [2*N-1:0] qS_ref_dbg[$]; // Cola de debug ref

  covergroup cg_tb;
    covA: coverpoint bus.md.A{bins binsA[(1 << N)]={[-(1 << (N-1)):(1 << (N-1)) - 1]};} 
    covB: coverpoint bus.md.B{bins binsB[(1 << N)]={[-(1 << (N-1)):(1 << (N-1)) - 1]};}   
    crossAB: cross covA,covB;
  endgroup;

  Aleatorizar #(N) gen = new();
  cg_tb cov;
  // ------------------------------------------------------------- TASK
  // TASK COLAS
  task automatic almacenar_salidas_queues();
    forever begin
      @(bus.md);
      if (bus.md.END_MULT) begin
        q_dut.push_back(bus.md.S); // Cola DUT
        qS_dut_dbg.push_back(bus.md.S); 
      end
      if (bus.md.START) begin
        q_gm.push_back(bus.md.A*bus.md.B); // Cola REF
        qS_ref_dbg.push_back(bus.md.A*bus.md.B);
      end
    end
  endtask
  task automatic check_queues();
    logic signed [2*N-1:0] sd, sg;
    forever begin
      wait (q_dut.size() > 0 && q_gm.size() > 0);
      sd = q_dut.pop_front();
      sg = q_gm.pop_front();
      Check_Mediante_Colas: assert (sd === sg)  
      // $display("QUEUE OK     : DUT=%0d GM=%0d", sd, sg); //Usar para ver las comparaciones
      else $fatal(1, "QUEUE MISMATCH: DUT=%0d GM=%0d", sd, sg);
    end
  endtask
  // FIN TASK COLAS
  // Configura las constraints
  task automatic set_constraints(bit pospos_on,bit negneg_on,bit posneg_on,bit negpos_on);
    gen.pospos.constraint_mode(pospos_on);
    gen.negneg.constraint_mode(negneg_on);
    gen.posneg.constraint_mode(posneg_on);
    gen.negpos.constraint_mode(negpos_on);
  endtask
  // Configurar estimulos
  task automatic apply_and_check(input string label);
    @(bus.sd);
    check_Randomization: assert(gen.randomize()) else $fatal("Randomization failed");
    bus.sd.START <= 1'b1; bus.sd.A <= gen.valorA; bus.sd.B <= gen.valorB;
    cov.sample();
  endtask
  // Evaluar cobertura + configuraciones
  task automatic run_scenario(
    input string label,
    input real   target_cov,
    input bit    pospos_on,
    input bit    negneg_on,
    input bit    posneg_on,
    input bit    negpos_on);
    set_constraints(pospos_on, negneg_on, posneg_on, negpos_on);
    while (cov.crossAB.get_coverage() < target_cov) begin
      apply_and_check(label);
    end
    $display("Cobertura %s completa: %0.2f%%",label, cov.crossAB.get_coverage());
  endtask
  // ------------------------------------------------------------- START ZONA ESTIMULOS
  initial begin
    // TB mediante colas y comparador
    fork
      almacenar_salidas_queues();
      check_queues();
    join_none
    // TB golden model arithmetico
    @(bus.sd);
    bus.sd.A <= '0; bus.sd.B <= '0; bus.sd.START <= 1'b0;
    cov = new();
    repeat (5) @(bus.sd);
    cov.sample();
    // POS * POS  -> hasta 25%
    run_scenario("POS*POS", 25.0, 1, 0, 0, 0);

    // NEG * NEG  -> hasta 50%
    run_scenario("NEG*NEG", 50.0, 0, 1, 0, 0);

    // POS * NEG  -> hasta 75%
    run_scenario("POS*NEG", 75.0, 0, 0, 1, 0);

    // NEG * POS  -> hasta 100%
    run_scenario("NEG*POS",100.0, 0, 0, 0, 1);

    bus.sd.START <= 1'b0;
    repeat (10) @(bus.sd);
    $display("COBERTURA COMPLETA: %0.2f%%", cov.get_coverage());
    Check_Debug_Queues: assert (qS_dut_dbg == qS_ref_dbg)
    $display("Colas de debug OK al final de la simulacion");
    else $fatal(1,"Colas de debug DIFERENTES al final de la simulacion");
    $finish;
  end
  // ------------------------------------------------------------- END ZONA ESTIMULOS
endprogram

module tb_multipli_pipelined();
  // Parametro
  localparam int N = 8; //EL ALGORITMO SOLO FUNCIONA CON PARAES N=2,4,6,8...
  // Reloj y Reset
  logic RESET;
  logic CLOCK = 1'b0;
  always #10 CLOCK = ~CLOCK;
  // Interface
  bus_mult #(N) bus (CLOCK, RESET);

  initial begin
      RESET = 0;
      repeat (3) @(negedge CLOCK);
      RESET = 1;
  end

  // multipli_pipelined_bus_wrapper_RTL_Parametrizable #(.N(N)) uut (.bus(bus));
  multipli_pipelined_bus_wrapper_GateLevel uut (.bus(bus));

  estimulos #(.N(N)) u_estimulos (bus);

endmodule

module multipli_pipelined_bus_wrapper_RTL_Parametrizable #(parameter int N = 8)
(bus_mult.dut bus );
multipli_pipelined #(.N(N)) uut (
  .CLOCK    (bus.CLOCK),
  .RESET    (bus.RESET),
  .START    (bus.START),
  .A        (bus.A),
  .B        (bus.B),
  .S        (bus.S),
  .END_MULT (bus.END_MULT)
);
endmodule

module multipli_pipelined_bus_wrapper_GateLevel (bus_mult.dut bus );
multipli_pipelined uut (
  .CLOCK    (bus.CLOCK),
  .RESET    (bus.RESET),
  .START    (bus.START),
  .A        (bus.A),
  .B        (bus.B),
  .S        (bus.S),
  .END_MULT (bus.END_MULT)
);
endmodule