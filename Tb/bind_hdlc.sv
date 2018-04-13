//////////////////////////////////////////////////
// Title:   bind_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

module bind_hdlc ();

  bind test_hdlc assertions_hdlc u_assertion_bind(
    .ErrCntAssertions(uin_hdlc.ErrCntAssertions),
    .Clk(uin_hdlc.Clk),
    .Rst(uin_hdlc.Rst),
    .Rx(uin_hdlc.Rx),
    .Rx_FlagDetect(uin_hdlc.Rx_FlagDetect),
    .Rx_AbortDetect(uin_hdlc.Rx_AbortDetect),
    .Rx_StartZeroDetect(uin_hdlc.Rx_StartZeroDetect),
    .Rx_NewByte(uin_hdlc.Rx_NewByte),
    .Rx_Data(uin_hdlc.Rx_Data),


    .Tx_AbortedTrans(uin_hdlc.Tx_AbortedTrans)
  );

endmodule
