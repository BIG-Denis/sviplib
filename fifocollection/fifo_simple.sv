module fifo_simple #(
  parameter int unsigned FIFO_DATA_WIDTH = 32,
  parameter int unsigned WORD_FIFO_DEPTH = 32,
  parameter bit          EGRESS          = 1
)(
  input  logic                         clk_i,
  input  logic                         rstn_i,
  input  logic                         flush_i,

  input  logic [FIFO_DATA_WIDTH - 1:0] data_i,
  input  logic                         push_i,

  input  logic                         pop_i,
  output logic [FIFO_DATA_WIDTH - 1:0] data_o
);

localparam PTR_WIDTH = $clog2( WORD_FIFO_DEPTH );

////   LOCAL VARIABLES   ////

logic [PTR_WIDTH:0] write_ptr;
logic [PTR_WIDTH:0] read_ptr;
logic write_ptr_circle, read_ptr_circle;

logic [FIFO_DATA_WIDTH - 1:0] fifo_mem [WORD_FIFO_DEPTH - 1:0];


////     INNER LOGIC     ////

assign write_ptr_circle = write_ptr[PTR_WIDTH];
assign read_ptr_circle  =  read_ptr[PTR_WIDTH];

always_ff @( posedge clk_i or negedge rstn_i ) begin : write_ptr_logic
  if ( ~rstn_i ) begin
    write_ptr <= PTR_WIDTH'('b0);
  end
  else begin
    if ( flush_i ) write_ptr <= PTR_WIDTH'('b0);
    else if ( push_i ) begin
      fifo_mem[write_ptr] <= data_i;
      write_ptr           <= write_ptr + 1'b1;
    end
  end
end

always_ff @( posedge clk_i or negedge rstn_i ) begin : read_ptr_logic
  if ( ~rstn_i ) begin
    read_ptr <= PTR_WIDTH'('b0);
  end
  else begin
    if    ( flush_i ) write_ptr <= PTR_WIDTH'('b0);
    else if ( pop_i ) read_ptr  <= read_ptr + 1'b1;
  end
end

////   OUTPUT  SIGNALS   ////

generate
  if ( EGRESS ) begin
    always_ff @( posedge clk_i ) data_o <= fifo_mem[read_ptr];
  end
  else assign                    data_o  = fifo_mem[read_ptr];
endgenerate


assign empty_o = ( write_ptr == read_ptr ) && ( write_ptr_circle == read_ptr_circle );
assign full_o  = ( write_ptr == read_ptr ) && ( write_ptr_circle != read_ptr_circle );

//// SIMULATION  ASSERTS ////

assert property( @( posedge clk_i ) disable iff ( !rstn_i )
  full_o |-> ~push_i)
else $error("Writing into full FIFO");

assert property( @( posedge clk_i ) disable iff ( !rstn_i )
  empty_o |-> ~pop_i)
else $error("Reading from empty FIFO");

endmodule