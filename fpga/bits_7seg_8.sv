// --------------------------------------------------------------------
// Universitat Politècnica de València
// Escuela Técnica Superior de Ingenieros de Telecomunicación
// --------------------------------------------------------------------
// Integración Sistemas Digitales
// Curso 2025-26
// --------------------------------------------------------------------
// Nombre del archivo: bits_7seg_8.sv
//
// Descripción: Conversor de un valor firmado de 8 bits (Svalue) a cuatro
//              dígitos para display de 7 segmentos. Calcula el valor
//              absoluto, lo convierte a BCD (hundreds/tens/ones) mediante
//              el algoritmo "sumar 3 y desplazar" (double dabble) y
//              genera los dígitos finales con gestión de signo y blanks,
//              que se decodifican con seg7_decoder.
//              (No parametrizable en esta versión; entrada fija de 8 bits).
//
// Entradas y salidas:
//
//   Svalue[7:0] : Valor firmado en binario (-128 .. +127).
//   seg3..seg0  : Patrones de 7 segmentos activos a nivel bajo para
//                 cuatro displays (signo/blanks/dígitos).
//
// Dependencias/instancias:
//   - seg7_decoder : decodificador de 4 bits a 7 segmentos para cada dígito.
//
// Notas de implementación:
//   - Se extrae el signo y se calcula el valor absoluto en un always_comb.
//   - Conversión binario → BCD (hundreds/tens/ones) mediante doble dabble.
//   - Convención de dígitos:
//       * 0..9  = dígitos decimales.
//       * 4'hA  = símbolo '-'.
//       * 4'hF  = BLANK (display apagado).
//   - Se suprimen ceros no significativos en hundreds/tens, manteniendo
//     un formato compacto en el display.
//
// --------------------------------------------------------------------
// Versión: v1.0 | Fecha Modificación: 13/11/2025
//
// Autores: Enrique Fayos Gimeno y Jairo Gónzalez Ibáñez
//
// --------------------------------------------------------------------
module bits_7seg_8
(
    input  logic signed [7:0] Svalue,
    output logic [6:0] seg3, seg2, seg1, seg0
);
// ---------------- Señales internas ----------------
logic       neg;            // 1 si Svalue es negativo
logic [7:0] abs_value;      // valor absoluto en binario (0..128)
logic [3:0] hundreds;       // centenas (BCD)
logic [3:0] tens;           // decenas (BCD)
logic [3:0] ones;           // unidades (BCD)
logic [3:0] d3, d2, d1, d0; // dígitos finales que irán a cada display
// --------------------------------------------------
// 1) Sacar signo y valor absoluto de Svalue
// --------------------------------------------------
always_comb begin
    logic signed [8:0] ext;
    ext = Svalue;          
    if (ext < 0) begin
        neg = 1'b1;
        ext = -ext; 
    end else begin
        neg = 1'b0;
    end
    abs_value = ext[7:0];
end
// --------------------------------------------------
// 2) Convertir de binario (abs_value) a BCD (hundreds/tens/ones)
// usando el algoritmo "sumar 3 y desplazar" (double dabble)
// --------------------------------------------------
always_comb begin
    // shift_reg = [hundreds][tens][ones][binario]
    logic [19:0] shift_reg;
    // 2.1) Inicializamos: BCD a 0 y cargamos el binario abajo
    shift_reg      = '0;
    shift_reg[7:0] = abs_value;
    // 2.2) Recorremos los 8 bits del número
    for (int i = 0; i < 8; i++) begin
        // Si algún dígito BCD >= 5, le sumamos 3
        if (shift_reg[19:16] >= 5) shift_reg[19:16] += 4'd3; // hundreds
        if (shift_reg[15:12] >= 5) shift_reg[15:12] += 4'd3; // tens
        if (shift_reg[11:8]  >= 5) shift_reg[11:8]  += 4'd3; // ones
        // Desplazamos todo 1 bit a la izquierda
        shift_reg = shift_reg << 1;
    end
    // 2.3) Al final, los digitos BCD están en estas posiciones:
    hundreds = shift_reg[19:16];
    tens     = shift_reg[15:12];
    ones     = shift_reg[11:8];
end
// --------------------------------------------------
// 3) Elegir que se muestra en cada display (d3..d0)
//    Convención:
//    - 0..9  = dígitos
//    - 4'hA = simbolo '-'
//    - 4'hF = "BLANK" (apagado)
// --------------------------------------------------
always_comb begin
    if (neg) begin
        // Número negativo:
        d3 = 4'hA; // '-'
        d2 = (hundreds == 0) ? 4'hF : hundreds;
        d1 = (hundreds == 0 && tens == 0) ? 4'hF : tens;
        d0 = ones;
    end else begin
        // Número positivo:
        d3 = 4'hF; // en blanco (sin signo)
        d2 = (hundreds == 0) ? 4'hF : hundreds;
        d1 = (hundreds == 0 && tens == 0) ? 4'hF : tens;
        d0 = ones;
    end
end
// --------------------------------------------------
// 4) Pasar dígitos (d3..d0) a segmentos (seg3..seg0)
// Decoder activo-bajo (0 = LED encendido, 1 = apagado)
// --------------------------------------------------
seg7_decoder dec3 (.digit(d3), .seg(seg3));
seg7_decoder dec2 (.digit(d2), .seg(seg2));
seg7_decoder dec1 (.digit(d1), .seg(seg1));
seg7_decoder dec0 (.digit(d0), .seg(seg0));
endmodule