// --------------------------------------------------------------------
// Universitat Politècnica de València
// Escuela Técnica Superior de Ingenieros de Telecomunicación
// --------------------------------------------------------------------
// Integración Sistemas Digitales
// Curso 2025-26
// --------------------------------------------------------------------
// Nombre del archivo: multipli_pipelined.sv
//
// Descripción: Multiplicador pipelined (algoritmo Booth / recodificación
//              por pares) parametrizable en ancho N. El módulo admite
//              entrada START y produce S y END_MULT al finalizar la
//              operación. Está pensado para usarse con el testbench que
//              emplea la interfaz 'bus_mult'.
//
// Parámetros:
//   N : ancho de palabra de A y B (bits). Debe ser par: N = 2,4,6,8,...
//
// Notas:
//  - El reset es activo en nivel 0 (negativo) — coincide con tus TBs.
//  - Si N no es par dará error ya que solo está pensado para pares.
//  - Salida S construida con la parte baja de ACCU concatenada con LO.
// --------------------------------------------------------------------
// Versión: v1.1 | Fecha Modificación: 15/11/2025
//
// Autor: Enrique Fayos Gimeno y Jairo Gónzalez Ibáñez
//
// --------------------------------------------------------------------
module multipli_pipelined
#(parameter int N = 8)
(
	input  logic                        CLOCK,
	input  logic                        RESET,     
	input  logic                        START,
	input  logic signed [N-1:0]         A,B,
	output logic signed [2*N-1:0]       S,
	output logic                        END_MULT
);

// Parametros
parameter int iteraciones = N/2; //{op,shift}
localparam int n_etapas = 1 + 2*iteraciones; //start+4*{op,shift}
// Registros
logic [n_etapas-1:0] start;
logic [n_etapas-1:0] X;
logic signed [n_etapas-1:0][N-1:0] LO,M;
logic signed [n_etapas-1:0][N+1:0] ACCU;

// -------------------------------------------------------------
// PIPELINE
// -------------------------------------------------------------
always_ff @(posedge CLOCK or negedge RESET) begin
    if (!RESET) begin
    // Zona de reset
        start    <= '0;
        X        <= '0;
        LO       <= '0;
        M        <= '0;  
        ACCU     <= '0;
    end else begin
    // Etapa de carga de datos
        start[0] <= START;
        if (START) begin
            ACCU[0] <= '0;
            LO[0]   <= $signed(A);
            M[0]    <= $signed(B);
            X[0]    <= 1'b0;
        end else begin
            ACCU[0] <= '0;
            LO[0]   <= '0;
            M[0]    <= '0;
            X[0]    <= 1'b0;            
        end
    // Etapas iterativas pipelining
    for (int i = 1; i < n_etapas; i++) begin
        start[i] <= start[i-1];
        if (start[i-1]) begin
            M[i] <= M[i-1];
            if((i%2)==1) begin 
                // OPERATION -.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                logic [2:0] q;
                logic signed [N+1:0] Mext;
                q    = {LO[i-1][1:0], X[i-1]};
                Mext = $signed(M[i-1]);
                ACCU[i] <= ACCU[i-1];
                LO[i]   <= LO[i-1];
                X[i]    <= X[i-1];
                unique case (q)
                    3'b000, 3'b111: ACCU[i] <= ACCU[i-1];                 
                    3'b001, 3'b010: ACCU[i] <= ACCU[i-1] + Mext;         
                    3'b011:         ACCU[i] <= ACCU[i-1] + (Mext <<< 1);  
                    3'b100:         ACCU[i] <= ACCU[i-1] - (Mext <<< 1);
                    3'b101, 3'b110: ACCU[i] <= ACCU[i-1] - Mext;         
                    default:        ACCU[i] <= ACCU[i-1];                    
                endcase
                end
                // -.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
            else begin
                // SHIFT -.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                {ACCU[i], LO[i], X[i]} <= $signed({ACCU[i-1], LO[i-1], X[i-1]}) >>> 2;
                end
                // -.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                end 
        else begin
            ACCU[i] <= '0;
            LO[i]   <= '0;
            M[i]    <= '0;
            X[i]    <= 1'b0;               
            end
        end 
        //END_MULT <= start[n_etapas-1];
    end
end
assign END_MULT = start[n_etapas-1];
assign S = {ACCU[n_etapas-1][N-1:0],LO[n_etapas-1]};

endmodule
