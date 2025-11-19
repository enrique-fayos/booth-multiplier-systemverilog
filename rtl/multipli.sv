// --------------------------------------------------------------------
// Universitat Politècnica de València
// Escuela Técnica Superior de Ingenieros de Telecomunicación
// --------------------------------------------------------------------
// Integración Sistemas Digitales
// Curso 2025-26
// --------------------------------------------------------------------
// Nombre del archivo: multipli.sv
//
// Descripción: Multiplicador secuencial firmado basado en el algoritmo
//              de Booth radix-4. Procesa 2 bits del multiplicador por
//              ciclo, acumulando el resultado parcial en ACCU y
//              desplazando aritméticamente el conjunto {ACCU, LO, X}.
//              Utiliza una FSM para controlar las fases de inicio,
//              operación, desplazamiento y notificación de fin.
//
// Parámetros:
//   N : Ancho de palabra (bits) de los operandos A y B.
//
// Entradas y salidas:
//
//   CLOCK        : Reloj, activo por flanco de subida.
//   RESET        : Reset asíncrono, activo a nivel bajo.
//   START        : Petición de inicio de multiplicación.
//   A, B         : Operandos firmados de N bits.
//   S[2*N-1:0]   : Resultado firmado de 2*N bits.
//   END_MULT     : Flag de finalización de la multiplicación.
//
// Notas de implementación:
//   - FSM con 5 estados: idle, init, op, shift, notify.
//   - Algoritmo de Booth radix-4 usando q = {LO[1:0], X}.
//   - Procesa 2 bits por iteración; contador COUNT acumula los bits
//     procesados hasta N.
//   - Se extiende el signo de M (Mext) y ACCU a N+2 bits para evitar pérdida
//     de signo en los desplazamientos y sumas.
//   - La salida S se forma concatenando ACCU (N bits bajos) y LO.
//
// --------------------------------------------------------------------
// Versión: v1.0 | Fecha Modificación: 13/11/2025
//
// Autores: Enrique Fayos Gimeno y Jairo Gónzalez Ibáñez
//
// --------------------------------------------------------------------
module multipli
#(parameter int N = 8)
(
	input  logic                        CLOCK,
	input  logic                        RESET,     
	input  logic                        START,
	input  logic signed [N-1:0]         A,B,
	output logic signed [2*N-1:0]       S,
	output logic                        END_MULT
);

// -------------------------------------------------------------
// FSM
// -------------------------------------------------------------
typedef enum logic [2:0] { idle, init, op, shift, notify } var_states;
var_states state;

// -------------------------------------------------------------
// Registros internos (datapath)
// -------------------------------------------------------------
logic signed [N+1:0]  ACCU;     // Acumulador {S1,S0,HI}      
logic signed [N-1:0]  LO,M;     // LO->multiplier M->multiplicand
logic                      X;		 // bit extra de Booth
logic [$clog2(N+2)-1:0] COUNT;  // cuenta bits procesados     

logic [2:0] q;                       // Variable para [q+,q,q-]       
assign q = {LO[1:0], X};             // algoritmo Booth parejas

// extension de signo de M para no perderlo (Peor caso M=-128 *-2M ; ***)
logic signed [N+1:0] Mext;
assign Mext = M; 

// -------------------------------------------------------------
// Secuencial (control + datapath)
// -------------------------------------------------------------
always_ff @(posedge CLOCK or negedge RESET) begin
    if (!RESET) begin
        state    <= idle;
        END_MULT <= 1'b0;
        ACCU     <= '0;
        LO       <= '0;
        M        <= '0;
        X        <= 1'b0;
        COUNT    <= '0;
    end else begin
        unique case (state)
            idle: begin
                END_MULT <= 1'b0;
                if (START) state <= init;
            end

            init: begin
                ACCU  <= '0;
                LO    <= $signed(A);      
                M     <= $signed(B);       
                X     <= 1'b0;
                COUNT <= '0;
                state <= op;
            end

            op: begin
                // Booth radix-4 
                unique case (q)
                    3'b000, 3'b111: ACCU <= ACCU;                 
                    3'b001, 3'b010: ACCU <= ACCU + Mext;         
                    3'b011:         ACCU <= ACCU + (Mext <<< 1);  
                    3'b100:         ACCU <= ACCU - (Mext <<< 1);  // Mas problematico ***
                    3'b101, 3'b110: ACCU <= ACCU - Mext;         
                    default:        ACCU <= ACCU;
                endcase
                COUNT <= COUNT + 2;
                state <= shift;
            end

            shift: begin
                // (ASR -> Arithmetic Shift Right) de 2 bits sobre {ACCU, LO, X}
				{ACCU, LO, X} <= $signed({ACCU, LO, X}) >>> 2;                     

                if (COUNT >= N)
                    state <= notify;
                else
                    state <= op;
            end

            notify: begin
                END_MULT <= 1'b1;                   
                if (!START) state <= idle;
            end

            default: state <= idle;
        endcase
    end
end

// -------------------------------------------------------------
// Salida (2*N). Se descarta el bit extra de signo de ACCU
// -------------------------------------------------------------
assign S = {ACCU[N-1:0], LO};

// -------------------------------------------------------------
// Assets Invarientes
// -------------------------------------------------------------
Check_fellReset: assert property (@(posedge CLOCK) ($fell(RESET) |=> (END_MULT == 1'b0 && state == idle)))
else $error("END_MULT debe ser 0 y state==idle mientras RESET está activo");
Check_contReset: assert property (@(posedge CLOCK) (!RESET |-> (state == idle && END_MULT == 1'b0)))
else $error("CHTA->END_MULT debe ser 0 y state==idle mientras RESET está activo");

Check_EndMult: assert property (@(posedge CLOCK) disable iff(!RESET) (state==notify |=> END_MULT == 1'b1))
else $error("La flag de END_MULT no se ha activado al finalizar");
Check_StateNotify: assert property (@(posedge CLOCK) disable iff (!RESET) (END_MULT == 1'b1 |-> $past(state) == notify))
else $error("END_MULT activo pero state no es notify");
endmodule
