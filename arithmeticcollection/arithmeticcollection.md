# Arithmetic collection

## About

Collection of multiple arithmetical blocks.

> For easy of readability in instance example, for all parameters will be provided default value.

### Decrementer - simple decrement by a power of 2

Combinational-only arithmetical block to decrease number by a power of 2.

Source located in `rtl/decrementer.sv`.

Instance:

```systemverilog
decrementer #(
  .WIDTH      (      WIDTH ),
  .POWER_OF_2 ( POWER_OF_2 )
) decrementer_inst (
  .data_i     (     data_i ),
  .data_o     (     data_o )
);
```

Parameter `WIDTH`  used for setting data width of input number and `POWER_OF_2` used to set decrementing number i.e. $2^{POWER\_OF\_2}$ so 0 will decrement data_i by 1, 2 will decrement by 4 etc.

### Incrementer - simple increment by a power of 2

Combinational-only arithmetical block to increase number by a power of 2.

Source located in `rtl/incrementer.sv`.

Instance:

```systemverilog
incrementer #(
  .WIDTH      (      WIDTH ),
  .POWER_OF_2 ( POWER_OF_2 )
) incrementer_inst (
  .data_i     (     data_i ),
  .data_o     (     data_o )
);
```

Parameter `WIDTH`  used for setting data width of input number and `POWER_OF_2` used to set incrementing number i.e. $2^{POWER\_OF\_2}$ so 0 will increase data_i by 1, 2 will increase by 4 etc.