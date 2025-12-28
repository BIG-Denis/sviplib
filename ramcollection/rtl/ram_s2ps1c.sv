module ram_s1p1c #(
  parameter  int unsigned WORD_WIDTH      = 8,
  parameter  int unsigned WORD_COUNT      = 256,
  parameter  bit          INIT_FILE_BIN   = 0,
  parameter  int unsigned INIT_FILE       = "",
  localparam int unsigned ADDR_WIDTH      = $clog2(WORD_COUNT)
) (
  input  logic                    clk_i,
  input  logic                    rstn_i,

  input  logic                    we_a_i,
  input  logic [ADDR_WIDTH - 1:0] addr_a_i,
  input  logic [WORD_WIDTH - 1:0] data_a_i,

  input  logic [ADDR_WIDTH - 1:0] addr_b_i,
  output logic [WORD_WIDTH - 1:0] data_b_o
);

logic [WORD_WIDTH - 1:0] ram [0:WORD_COUNT - 1];


// write port (a) driver
always_ff @( posedge clk ) begin
  if (we_a_i) begin
    ram[addr_a_i] <= data_a_i;
  end
end

// read port (b) driver
always_ff @( posedge clk_i ) begin
  data_b_o <= ram[addr_b_i];
end


initial begin
  if (INIT_FILE != "") begin
    if (INIT_FILE_BIN) begin
      $display("Initializing RAM with bin file: %s...", INIT_FILE);
      $readmemb(INIT_FILE, ram);
    end
    else begin
      $display("Initializing RAM with hex file: %s...", INIT_FILE);
      $readmemh(INIT_FILE, ram);
    end
  end
end

assert property (@(posedge clk) disable iff (!rstn_i) !$isunknown(we_a_i)) else $error("we_a_i must always be known");
assert property (@(posedge clk) disable iff (!rstn_i) we_a_i |-> !$isunknown(addr_a_i)) else $error("addr_a_i must be known when we_a_i is high");

endmodule
