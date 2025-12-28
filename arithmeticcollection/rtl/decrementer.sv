module decrementer#(
  parameter int unsigned WIDTH      = 8,
  parameter int unsigned POWER_OF_2 = 0
) (
  input  logic [WIDTH - 1:0] data_i,
  output logic [WIDTH - 1:0] data_o
);

localparam int unsigned lsb_idx = 1 << POWER_OF_2;

generate
  for ( genvar i = lsb_idx + 1; i < WIDTH; i = i + 1 ) begin
    assign data_o[i]     = ~data_i[i] ^ (|data_i[i-1:lsb_idx]);
  end

  assign   data_o[lsb_idx] = ~data_i[lsb_idx];

  for ( genvar i = 0; i < lsb_idx; i = i + 1 ) begin
    assign data_o[i]     = data_i[i];
  end

endgenerate

endmodule
