// --------------------------------------------------------------------
// Universitat Politècnica de València
// Escuela Técnica Superior de Ingenieros de Telecomunicación
// --------------------------------------------------------------------
// Integración Sistemas Digitales
// Curso 2025-26
// --------------------------------------------------------------------
// Nombre del archivo: bits_7seg_16.sv
//
// Descripción: Conversor de un valor firmado de 16 bits (Svalue) a ocho
//              displays de 7 segmentos. Calcula el valor absoluto,
//              convierte el binario de 16 bits a BCD mediante el algoritmo
//              "sumar 3 y desplazar" (double dabble) generando 5 dígitos
//              decimales, y forma los dígitos finales con gestión de
//              signo y blanks para mostrarlos con seg7_decoder.
//
// Parámetros:
//   (No parametrizable en esta versión; entrada fija de 16 bits).
//
// Entradas y salidas:
//
//   Svalue[15:0] : Valor firmado en binario (-32768 .. +32767).
//   seg7..seg0   : Patrones de 7 segmentos activos a nivel bajo para
//                  ocho displays (signo, dígitos y blanks).
//
// Dependencias/instancias:
//   - seg7_decoder : decodificador 4 bits → 7 segmentos para cada dígito.
//
// Notas de implementación:
//   - Se extrae el signo y se calcula el valor absoluto en un always_comb.
//   - Conversión binario (16 bits) → BCD (5 dígitos) con double dabble.
//   - Convención de dígitos internos:
//       * 0..9  = dígitos decimales.
//       * 4'hA  = símbolo '-'.
//       * 4'hF  = BLANK (display apagado).
//   - Mapeo a displays:
//       * d7: signo ('-' o blank).
//       * d6..d2: decenas de millar, millar, centena, decena, unidad
//                 con supresión de ceros a la izquierda.
//       * d1, d0: siempre BLANK.
//
// --------------------------------------------------------------------
// Versión: v1.0 | Fecha Modificación: 13/11/2025
//
// Autores: Enrique Fayos Gimeno y Jairo Gónzalez Ibáñez
//
// --------------------------------------------------------------------
module bits_7seg_16
(
    input  logic signed [15:0] Svalue,
    output logic [6:0] seg7, seg6, seg5, seg4,
    output logic [6:0] seg3, seg2, seg1, seg0
);
// ---------------- Señales internas ----------------
logic neg;                // 1 si Svalue es negativo
logic [15:0] abs_value;         // valor absoluto (0..32768)

// Dígitos BCD: 0..32768 -> 5 dígitos decimales
logic [3:0] ten_thousands;      // decena de millar
logic [3:0] thousands;          // millar
logic [3:0] hundreds;           // centena
logic [3:0] tens;               // decena
logic [3:0] ones;               // unidad

// Dígitos finales que irán a cada display
// d7 es el más a la izquierda (seg7), d0 el más a la derecha (seg0)
logic [3:0] d7, d6, d5, d4, d3, d2, d1, d0;

// --------------------------------------------------
// 1) Sacar signo y valor absoluto de Svalue
// --------------------------------------------------
always_comb begin
    logic signed [16:0] ext;   // 17 bits para evitar lío con -32768
    ext = Svalue;
    if (ext < 0) begin
        neg = 1'b1;
        ext = -ext;
    end else begin
        neg = 1'b0;
    end
        abs_value = ext[15:0];     // rango 0..32768
end
// --------------------------------------------------
// 2) Binario (abs_value, 16 bits) -> BCD (5 dígitos)
//    usando double dabble (sumar 3 y desplazar)
// --------------------------------------------------
always_comb begin
    // shift_reg = [ten_thousands][thousands][hundreds][tens][ones][binario16]
    logic [35:0] shift_reg;
    shift_reg = '0;
    shift_reg[15:0]  = abs_value;
    // 16 iteraciones (16 bits de abs_value)
    for (int i = 0; i < 16; i++) begin
        if (shift_reg[35:32] >= 5) shift_reg[35:32] += 4'd3; // ten_thousands
        if (shift_reg[31:28] >= 5) shift_reg[31:28] += 4'd3; // thousands
        if (shift_reg[27:24] >= 5) shift_reg[27:24] += 4'd3; // hundreds
        if (shift_reg[23:20] >= 5) shift_reg[23:20] += 4'd3; // tens
        if (shift_reg[19:16] >= 5) shift_reg[19:16] += 4'd3; // ones
        shift_reg = shift_reg << 1;
    end
    ten_thousands = shift_reg[35:32];
    thousands     = shift_reg[31:28];
    hundreds      = shift_reg[27:24];
    tens          = shift_reg[23:20];
    ones          = shift_reg[19:16];
end
// --------------------------------------------------
// 3) Elegir qué se muestra en cada display (d7..d0)
//    Convención:
//    - 0..9  = dígitos
//    - 4'hA  = símbolo '-'
//    - 4'hF  = BLANK (apagado)
//
//    Usaremos:
//    d7: signo
//    d6: ten_thousands
//    d5: thousands
//    d4: hundreds
//    d3: tens
//    d2: ones
//    d1: BLANK
//    d0: BLANK
// --------------------------------------------------
always_comb begin
    // por defecto, los dos de la derecha en blanco
    d1 = 4'hF;
    d0 = 4'hF;
    if (neg) begin
        // número negativo: "-xxxxx"
        d7 = 4'hA; // '-'
        d6 = (ten_thousands == 0) ? 4'hF : ten_thousands;
        d5 = (ten_thousands == 0 && thousands == 0) ? 4'hF : thousands;
        d4 = (ten_thousands == 0 && thousands == 0 && hundreds == 0) ? 4'hF : hundreds;
        d3 = (ten_thousands == 0 && thousands == 0 && hundreds == 0 && tens == 0) ? 4'hF : tens;
        d2 = ones;
    end else begin
        // número positivo: " xxxxx"
        d7 = 4'hF; // sin signo
        d6 = (ten_thousands == 0) ? 4'hF : ten_thousands;
        d5 = (ten_thousands == 0 && thousands == 0) ? 4'hF : thousands;
        d4 = (ten_thousands == 0 && thousands == 0 && hundreds == 0) ? 4'hF : hundreds;
        d3 = (ten_thousands == 0 && thousands == 0 && hundreds == 0 && tens == 0) ? 4'hF : tens;
        d2 = ones;
    end
end
// --------------------------------------------------
// 4) Dígitos (d7..d0) -> segmentos (seg7..seg0)
//    Usa tu seg7_decoder ACTIVO BAJO
// --------------------------------------------------
seg7_decoder dec7 (.digit(d7), .seg(seg7));
seg7_decoder dec6 (.digit(d6), .seg(seg6));
seg7_decoder dec5 (.digit(d5), .seg(seg5));
seg7_decoder dec4 (.digit(d4), .seg(seg4));
seg7_decoder dec3 (.digit(d3), .seg(seg3));
seg7_decoder dec2 (.digit(d2), .seg(seg2));
seg7_decoder dec1 (.digit(d1), .seg(seg1));
seg7_decoder dec0 (.digit(d0), .seg(seg0));

endmodule
