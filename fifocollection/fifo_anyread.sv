module fifo_anyread #(
  parameter int unsigned WORD_WIDTH         = 8,
  parameter int unsigned WORD_CNT_PER_WRITE = 4,
  parameter int unsigned WORD_CNT_PER_READ  = 4,
  parameter int unsigned WORD_FIFO_DEPTH    = 16,
  parameter int unsigned WRITE_WIDTH        = $clog2( WORD_CNT_PER_WRITE + 1),
  parameter int unsigned READ_WIDTH         = $clog2( WORD_CNT_PER_READ + 1)
)
(
  input  logic                                               clk_i,
  input  logic                                               rstn_i,

  input  logic                                               flush_i,

  input  logic [WRITE_WIDTH - 1:0]                           write_i,
  input  logic [WORD_CNT_PER_WRITE - 1:0][WORD_WIDTH  - 1:0] data_i,
  output logic                                               ready_o,

  output logic                                               valid_o,
  output logic [WORD_CNT_PER_READ - 1:0][WORD_WIDTH - 1:0]   data_o,
  input  logic [READ_WIDTH - 1:0]                            read_i
);

localparam PTR_WIDTH = $clog2(WORD_FIFO_DEPTH);

logic [WORD_FIFO_DEPTH - 1:0][WORD_WIDTH - 1:0] ram;
logic [PTR_WIDTH - 1:0]           write_ptr;
logic [PTR_WIDTH - 1:0]           read_ptr;
logic [WORD_CNT_PER_WRITE - 1:0]  ram_we;

logic [PTR_WIDTH:0]           credits;
logic [PTR_WIDTH:0]           used_credits;

logic [WRITE_WIDTH:0]         write_count;
logic [ READ_WIDTH:0]         read_count;

logic [PTR_WIDTH - 1:0]           write_addr [WORD_CNT_PER_WRITE - 1:0];
logic [PTR_WIDTH - 1:0]           read_addr  [WORD_CNT_PER_READ - 1:0];

assign write_count = ( credits < write_i     ) ? ( credits      ) : ( write_i );
assign read_count  = ( used_credits < read_i ) ? ( used_credits ) : ( read_i  );

always_ff @( posedge clk_i ) begin
  if( ~rstn_i ) begin
    used_credits <= PTR_WIDTH'(0);
  end else begin
    if ( flush_i ) used_credits <= PTR_WIDTH'(0);
    else begin
      if ( ready_o ) used_credits <= used_credits + write_count;
      if ( valid_o ) used_credits <= used_credits - read_count;
    end
  end
end

assign credits = WORD_FIFO_DEPTH - used_credits;

always_ff @( posedge clk_i ) begin
  if ( ~rstn_i ) begin
    write_ptr <= PTR_WIDTH'(0);
  end else begin
    if ( flush_i ) write_ptr <= PTR_WIDTH'(0);
    else           write_ptr <= write_ptr + write_count;
  end
end

always_ff @( posedge clk_i ) begin
  if ( ~rstn_i ) begin
    read_ptr <= PTR_WIDTH'( 0 );
  end else begin
    if      ( flush_i ) read_ptr <= PTR_WIDTH'( 0 );
    else if ( valid_o ) read_ptr <= read_ptr + read_count;
  end
end

assign ready_o = ~( credits      < WORD_CNT_PER_WRITE );
assign valid_o = ~( used_credits < WORD_CNT_PER_READ  ) & |read_i;

generate
  for ( genvar i = 0; i <= WORD_CNT_PER_WRITE + 1; i++) begin
    assign write_addr[i] = write_ptr   + i;
    assign ram_we[i]     = write_count > i;
  end
endgenerate

always_ff @( posedge clk_i ) begin
  for (int i = 0; i <= WORD_CNT_PER_WRITE + 1 ; i++) begin
    if ( ram_we[i] ) ram[write_addr[i]] <= data_i[i];
  end
end


generate
  for ( genvar i = 0; i < WORD_CNT_PER_READ; i++) begin
    assign read_addr[i] = read_ptr + i;
    assign data_o[i]    = ram[read_addr[i]];
  end
endgenerate


endmodule
