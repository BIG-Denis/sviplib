# FIFO collection

## About

Collection of multiple FIFO modules - from simplest to advanced ones.

> For easy of readability in instance example, for all parameters will be provided default value.

### Simple FIFO

Simplest canonical FIFO implementation with valid-ready interface and fixed read-write port widths.

Source located in `rtl/fifo_simple.sv`.

Instance:

```systemverilog

```

Additional comments.

### Reducing FIFO

Advanced FIFO with valid-ready interface and fixed yet different widths for read and write ports.

Source located in `rtl/fifo_reducing.sv`.

Instance:

```systemverilog

```

Additional comments.

### AnyRead FIFO

Advanced FIFO with valid-ready write interface, fixed write port width any read any word count at the time. Additional clear signal to flush FIFO.

Source located in `rtl/fifo_anyread.sv`.

Instance:

```systemverilog
fifo_anyread #(
  .WORD_WIDTH         (8 ),
  .WORD_CNT_PER_WRITE (8 ),
  .WORD_CNT_PER_READ  (4 ),
  .WORD_FIFO_DEPTH    (16)
) fifo_instance_name (
  .clk_i   (clk     ),
  .rstn_i  (rstn    ),

  .clear_i (clear   ),

  .valid_i (wr_valid),
  .data_i  (wr_data ),  // WORD_CNT_PER_WRITE * WORD_WIDTH
  .ready_o (wr_ready),

  .valid_o (rd_valid),
  .data_o  (rd_data ),  // WORD_CNT_PER_READ * WORD_WIDTH
  .read_i  (rd_words)   // $clog2(WORD_CNT_PER_READ)
);
```

To make no read at current clock cycle set `rd_words` to zero.

Keep in mind that this FIFO is likely to synthesize into register RAM, so avoid making it too deep as it can drastically increase utilization.
