//////////////////////////////////////////////////
// Title:   in_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

interface in_hdlc ();
  //Tb
  int ErrCntAssertions;

  //Clock and reset
  logic              Clk;
  logic              Rst;

  // Address
  logic        [2:0] Address;
  logic              WriteEnable;
  logic              ReadEnable;
  logic        [7:0] DataIn;
  logic        [7:0] DataOut;

  // TX
  logic              Tx;
  logic              TxEN;
  logic              Tx_Done;

  // RX
  logic              Rx;
  logic              RxEN;
  logic              Rx_Ready;

  // Tx - internal
  logic       Tx_AbortedTrans;
  logic 	  Tx_Full;
  logic 	  Tx_FCSDone;
  logic 	  Tx_AbortFrame;
  logic 	  Tx_NewByte;
  logic 	  Tx_Enable;
  logic 	  Tx_ValidFrame;
  logic 	  [7:0] Tx_FrameSize;
  logic 	  Tx_RdBuff;


  // Rx - internal
  logic     Rx_FlagDetect;
  logic     Rx_AbortDetect;
  logic 	Rx_StartZeroDetect;
  logic 	Rx_NewByte;
  logic [7:0] Rx_Data;
  logic 	Rx_Overflow;
  logic 	Rx_EoF;
  logic 	Rx_ValidFrame;
  logic [7:0] Rx_FrameSize;
  logic [127:0][7:0] Rx_DataArray;
  logic 	Rx_FrameError;
  logic 	Rx_FCSen;
  logic 	[7:0] Rx_DataBuffOut;
  logic 	Rx_AbortSignal;
  logic 	Rx_FCSerr;




endinterface
