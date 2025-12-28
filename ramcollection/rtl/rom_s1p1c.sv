module rom_s1p1c #(
  parameter  int unsigned WORD_WIDTH      = 8,
  parameter  int unsigned WORD_COUNT      = 256,
  parameter  bit          INIT_FILE_BIN   = 0,
  parameter  int unsigned INIT_FILE       = "",
  localparam int unsigned ADDR_WIDTH      = $clog2(WORD_COUNT)
) (
  input  logic                    clk_i,
  input  logic                    rstn_i,

  input  logic [ADDR_WIDTH - 1:0] addr_i,
  output logic [WORD_WIDTH - 1:0] data_o
);

logic [WORD_WIDTH - 1:0] rom [0:WORD_COUNT - 1];


always_ff @( posedge clk_i ) begin
  data_o <= rom[addr_i];
end


initial begin
  if (INIT_FILE != "") begin
    if (INIT_FILE_BIN) begin
      $display("Initializing ROM with bin file: %s...", INIT_FILE);
      $readmemb(INIT_FILE, rom);
    end
    else begin
      $display("Initializing ROM with hex file: %s...", INIT_FILE);
      $readmemh(INIT_FILE, rom);
    end
  end
end

endmodule
