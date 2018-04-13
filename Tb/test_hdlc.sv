//////////////////////////////////////////////////
// Title:   test_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

module test_hdlc ();

  //Hdlc interface
  in_hdlc uin_hdlc();

  //Internal assignments
  assign uin_hdlc.Rx_FlagDetect      = u_dut.Rx_FlagDetect;
  assign uin_hdlc.Rx_AbortDetect     = u_dut.Rx_AbortDetect;
  assign uin_hdlc.Rx_StartZeroDetect = u_dut.Rx_StartZeroDetect;
  assign uin_hdlc.Rx_NewByte 		 = u_dut.Rx_NewByte;

  assign uin_hdlc.Tx_AbortedTrans    = u_dut.Tx_AbortedTrans;
  assign uin_hdlc.Rx_Data		     = u_dut.Rx_Data;


  //Clock
  always #250ns uin_hdlc.Clk = ~uin_hdlc.Clk;

  //Dut
  Hdlc u_dut(
  .Clk(         uin_hdlc.Clk         ),
  .Rst(         uin_hdlc.Rst         ),
  // Address
  .Address(uin_hdlc.Address),
  .WriteEnable(uin_hdlc.WriteEnable),
  .ReadEnable(uin_hdlc.ReadEnable),
  .DataIn(uin_hdlc.DataIn),
  .DataOut(uin_hdlc.DataOut),
  // TX
  .Tx(),
  .TxEN(),
  .Tx_Done(),
  // RX
  .Rx(          uin_hdlc.Rx          ),
  .RxEN(        uin_hdlc.RxEN        ),
  .Rx_Ready(uin_hdlc.Rx_Ready)
  );

  //Test program
  testPr_hdlc u_testPr(
    .uin_hdlc( uin_hdlc )
  );

endmodule
