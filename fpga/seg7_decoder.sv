// --------------------------------------------------------------------
// Universitat Politècnica de València
// Escuela Técnica Superior de Ingenieros de Telecomunicación
// --------------------------------------------------------------------
// Integración Sistemas Digitales
// Curso 2025-26
// --------------------------------------------------------------------
// Nombre del archivo: seg7_decoder.sv
//
// Descripción: Decodificador de dígitos BCD/hex a display de 7 segmentos.
//              Genera el patrón de segmentos para los dígitos 0–9 y un
//              código especial (digit = 4'hA) para mostrar el signo '-',
//              dejando el resto de valores como BLANK.
//
// Entradas y salidas:
//
//   digit[3:0]  
//   seg[6:0]   
//
// Notas de implementación:
//   - Se usa un bloque always_comb con case único sobre 'digit'.
//   - Para 0–9 se asignan patrones de segmento específicos.
//   - Para digit = 4'hA se genera un patrón de signo '-'.
//   - Cualquier otro valor de 'digit' produce BLANK (todo apagado).
//   - Las asignaciones a los valores de seg han sido decididas en funcion
//     de las asignaciones del pin planner de forma que represente correctamente
//     los numeros y signo.
// --------------------------------------------------------------------
// Versión: v1.0 | Fecha Modificación: 13/11/2025
//
// Autores: Enrique Fayos Gimeno y Jairo Gónzalez Ibáñez
//
// --------------------------------------------------------------------
module seg7_decoder(
    input  logic [3:0] digit,
    output logic [6:0] seg
);
always_comb begin
    unique case (digit)
        4'd0: seg = 7'b1000000; // 0
        4'd1: seg = 7'b1111001; // 1
        4'd2: seg = 7'b0100100; // 2
        4'd3: seg = 7'b0110000; // 3
        4'd4: seg = 7'b0011001; // 4
        4'd5: seg = 7'b0010010; // 5
        4'd6: seg = 7'b0000010; // 6
        4'd7: seg = 7'b1111000; // 7
        4'd8: seg = 7'b0000000; // 8
        4'd9: seg = 7'b0010000; // 9
        4'hA: seg = 7'b0111111; // '-' (solo segmento central ON, invertido)
        default: seg = 7'b1111111; // BLANK (todo apagado)
    endcase
end
endmodule