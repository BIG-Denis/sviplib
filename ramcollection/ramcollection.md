# RAM collection

## About

Collection of multiple RAM (and one ROM) modules.

> For easy of readability in instance example, for all parameters will be provided default value.

### ROM - simple, single-port, 1-cycle

Read-only memory with syncronous read port with 1 cycle _addr2data_ trip. Can be initialized from memory file.

Source located in `rtl/rom_s1p1c.sv`.

Instance:

```systemverilog
rom_s1p1c #(
  .WORD_WIDTH    (8  ),
  .WORD_COUNT    (256),
  .INIT_FILE_BIN (0  ),
  .INIT_FILE     ("" )
) rom_instance_name (
  clk_i  (clk ),
  rstn_i (rstn),

  addr_i (addr),  // ADDR_WIDTH = $clog2(WORD_COUNT)
  data_o (data)
);
```

If no `INIT_FILE` provided, no memory initialization will be completed.

By default, hexadecimal memory file format is used, if `INIT_FILE_BIN` is set to 1, then `INIT_FILE` will be interprented as binary format.
