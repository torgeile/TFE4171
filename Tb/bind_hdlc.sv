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
	.Rx_Overflow(uin_hdlc.Rx_Overflow),
	.Rx_EoF(uin_hdlc.Rx_EoF),
	.Rx_ValidFrame(uin_hdlc.Rx_ValidFrame),
	.Rx_FrameSize(uin_hdlc.Rx_FrameSize),
	.Rx_DataArray(uin_hdlc.Rx_DataArray),
	.Rx_FrameError(uin_hdlc.Rx_FrameError),
	.Rx_FCSen(uin_hdlc.Rx_FCSen),
	.Rx_DataBuffOut(uin_hdlc.Rx_DataBuffOut),
	.Address(uin_hdlc.Address),
	.ReadEnable(uin_hdlc.ReadEnable),
	.Rx_AbortSignal(uin_hdlc.Rx_AbortSignal),


	

    .Tx_AbortedTrans(uin_hdlc.Tx_AbortedTrans)
  );

endmodule
