//////////////////////////////////////////////////
// Title:   testPr_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

program testPr_hdlc(
  in_hdlc uin_hdlc
);

  parameter TX_SC   = 3'b000;
  parameter TX_BUFF = 3'b001;
  parameter RX_SC   = 3'b010;
  parameter RX_BUFF = 3'b011;
  parameter RX_LEN  = 3'b100;

  parameter TX_DONE         = 8'b0000_0001;
  parameter TX_ENABLE       = 8'b0000_0010;
  parameter TX_ABORTFRAME   = 8'b0000_0100;
  parameter TX_ABORTEDTRANS = 8'b0000_1000;
  parameter TX_FULL         = 8'b0001_0000;

  parameter RX_READY        = 8'b0000_0001;
  parameter RX_DROP         = 8'b0000_0010;
  parameter RX_FRAMEERROR   = 8'b0000_0100;
  parameter RX_ABORTSIGNAL  = 8'b0000_1000;
  parameter RX_OVERFLOW     = 8'b0001_0000;
  parameter RX_FCSEN        = 8'b0010_0000;

  parameter FLAG  = 8'b0111_1110;
  parameter ABORT = 8'b1111_1110;

  int TbErrorCnt;

  semaphore sema = new(1); // Create semaphore with 1 key.

  initial begin
    $display("*************************************************************");
    $display("%t - Starting Test Program", $time);
    $display("*************************************************************");

    init();

    //Tests:
    //Test(); // used to find bug described in ch4.1

  fork
      Receive();
      Transmit();
  join

    //Tx_sendOverflow;


    $display("*************************************************************");
    $display("%t - Finishing Test Program", $time);
    $display("*************************************************************");
    $stop;
  end

  final begin

    $display("*********************************");
    $display("*                               *");
    $display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
    $display("*                               *");
    $display("*********************************");

  end



  task init();
    uin_hdlc.Clk         =   1'b0;
    uin_hdlc.Rst         =   1'b0;
    uin_hdlc.Rx          =   1'b1;
    uin_hdlc.RxEN        =   1'b1;
    uin_hdlc.TxEN        =   1'b1;
    uin_hdlc.DataIn      =   '0;
    uin_hdlc.Address     =   '0;


    uin_hdlc.WriteEnable = 1'b0;
    uin_hdlc.ReadEnable  = 1'b0;

    TbErrorCnt = 0;

    #1000ns;
    uin_hdlc.Rst         =   1'b1;
  endtask

covergroup hdlc_cg() @(posedge uin_hdlc.Clk);
    // Coverpoints for Data in/out
    DataIn: coverpoint uin_hdlc.DataIn {
        //option.auto_bin_max = 256;
        bins DataIn_Address[] = {[0:255]};
    }
    DataOut: coverpoint uin_hdlc.DataOut {
        bins DataOut_Address[] = {[0:255]};
    }

    // Coverpoints for Tx
    Tx_DataIn: coverpoint uin_hdlc.Tx_Data {
        bins DataIn_Tx[] = {[0:255]};
    }
    Tx_Framesize: coverpoint uin_hdlc.Tx_FrameSize {
        bins tx_frameSize[] = {[3:126]};
    }
    Tx_ValidFrame: coverpoint uin_hdlc.Tx_ValidFrame {
        bins Tx_frame_valid = {1};
        bins Tx_frame_not_valid = {0};
    }
    Tx_AbortedTrans: coverpoint uin_hdlc.Tx_AbortedTrans {
        bins tx_trans_not_aborted = {0};
        bins tx_trans_abort = {1};
    }
    Tx_AbortFrame: coverpoint uin_hdlc.Tx_AbortFrame {
        bins tx_frame_aborted = {1};
        bins tx_frame_not_aborted = {0};
    }
    Tx_Done: coverpoint uin_hdlc.Tx_Done {
        bins tx_not_done = {0};
        bins tx_done = {1};
    }
    Tx_Full: coverpoint uin_hdlc.Tx_Full {
        bins tx_not_full = {0};
        bins tx_full = {1};
    }

    // Coverpoints for Rx
    Rx_DataIn: coverpoint uin_hdlc.Rx_Data {
        bins DataIn_Rx[] = {[0:255]};
    }
    Rx_FrameSize: coverpoint uin_hdlc.Rx_FrameSize {
        bins rx_frameSize[] = {[2:126]};
    }
    Rx_Overflow: coverpoint uin_hdlc.Rx_Overflow {
        bins rx_no_overflow = {0};
        bins rx_overflow = {1};
    }
    Rx_AbortSignal: coverpoint uin_hdlc.Rx_AbortSignal {
        bins rxsignal_not_aborted = {0};
        bins rxsignal_aborted = {1};
    }
    Rx_FrameError: coverpoint uin_hdlc.Rx_FrameError {
        bins rx_no_framerr = {0};
        bins rx_framerr = {1};
    }
    Rx_FCSerr: coverpoint uin_hdlc.Rx_FCSerr {
        bins rx_FCS_error = {1};
        bins rx_FCS_no_error = {0};
    }
    Rx_AbortDetect: coverpoint uin_hdlc.Rx_AbortDetect {
        bins rx_no_abort_detected = {0};
        bins rx_abort_detected = {1};
    }
endgroup

hdlc_cg hdlc_cg_inst = new();


task WriteAddress(input logic [2:0] Address ,input logic [7:0] Data);
  @(posedge uin_hdlc.Clk);
  uin_hdlc.Address     = Address;
  uin_hdlc.WriteEnable = 1'b1;
  uin_hdlc.DataIn      = Data;
  uin_hdlc.Rx          = uin_hdlc.Tx; //Added to keep transfering Tx to Rx during write.
  @(posedge uin_hdlc.Clk);
  uin_hdlc.Rx          = uin_hdlc.Tx; //Added to keep transfering Tx to Rx during write.
  uin_hdlc.WriteEnable = 1'b0;
endtask

task Test(); // used to find bug described in ch2.3.1

        WriteAddress_Rx(RX_SC,RX_FCSEN);
		WriteAddress_Tx(TX_BUFF,'h00);
		WriteAddress_Tx(TX_BUFF,'h71);
		WriteAddress_Tx(TX_BUFF,'h9B);
	    //WriteAddress_Tx(TX_BUFF,'h23);

		WriteAddress_Tx(TX_SC,TX_ENABLE);
    	repeat(8*20) begin
    		uin_hdlc.Rx = uin_hdlc.Tx;
  			@(posedge uin_hdlc.Clk);
  		end
endtask



  task Transmit();
    logic [7:0] ReadData;
    $display("Starting Tx test");

    repeat(10)
  		@(posedge uin_hdlc.Clk);

//	Tx_sendRandom();

	Tx_send(5);
	Tx_sendAbort();
    repeat(90)
  		@(posedge uin_hdlc.Clk);


/*
   WriteAddress(TX_SC,TX_ABORTFRAME);
    repeat(20)
  		@(posedge uin_hdlc.Clk);
*/
	Tx_sendOverflow();

    repeat(90)
  		@(posedge uin_hdlc.Clk);



  for (int i = 0; i < 500; i++) begin
	    $display("%t Tx New random message ================", $time);

		Tx_sendRandom();
    repeat($urandom_range(0, 20))
  		@(posedge uin_hdlc.Clk);

	    ReadAddress_Tx(TX_SC, ReadData);
	    $display("Tx_SC=%b", ReadData);

    repeat(90)
  		@(posedge uin_hdlc.Clk);


  end

    repeat(90)
  		@(posedge uin_hdlc.Clk);
	//Tx_send(5);
    repeat(90)
  		@(posedge uin_hdlc.Clk);

  endtask

  task Receive();
    logic [7:0] ReadData;
    logic [7:0] ReadLen;
  automatic logic [4:0][7:0] shortmessage = '0;

    $display("Starting Rx test");

   WriteAddress_Rx(RX_SC,RX_FCSEN);
    uin_hdlc.Rx = 1'b1;

	    repeat(20)
	      @(posedge uin_hdlc.Clk);

	$display("%t Rx New remove zero message ================", $time);

	shortmessage[0] = 'h71;
	shortmessage[1] = 'h9B;

	CalculateFCS(shortmessage, 2, {shortmessage[3],shortmessage[2]});
    Rx_Byte(FLAG);
    Rx_multisend(shortmessage,4);
    Rx_Byte(FLAG);
    uin_hdlc.Rx = 1'b1;


	    repeat(15)
	      @(posedge uin_hdlc.Clk);
Rx_sendCRCerror();
Rx_sendAbort();




	      @(posedge uin_hdlc.Clk);

	    ReadAddress_Rx(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);
	      @(posedge uin_hdlc.Clk);

	    ReadAddress_Rx(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);
	      @(posedge uin_hdlc.Clk);

	    ReadAddress_Rx(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);
	      @(posedge uin_hdlc.Clk);

	    ReadAddress_Rx(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);

	    //WriteAddress_Rx(RX_SC,RX_DROP);

Rx_sendoverflow();
Rx_sendNonAligned();


	    repeat(20)
	      @(posedge uin_hdlc.Clk);

  //Loop for reciving lots of valid random data
  for (int i = 0; i < 800; i++) begin
	    $display("%t Rx New random message ================", $time);

	    Rx_sendRandom();
	    uin_hdlc.Rx = 1'b1;

	    repeat(10)
	      @(posedge uin_hdlc.Clk);

	    ReadAddress_Rx(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);


	    ReadAddress_Rx(RX_LEN , ReadLen);
	    $display("Rx_Len=%d", ReadLen);

	  for (int i = 0; i < ReadLen; i++) begin
   		ReadAddress_Rx(RX_BUFF , ReadData);
	  end

  end

    uin_hdlc.Rx = 1'b1;

    repeat(16)
      @(posedge uin_hdlc.Clk);
    ReadAddress_Rx(RX_SC, ReadData);
    $display("Rx_SC=%b", ReadData);


    ReadAddress_Rx(RX_LEN , ReadData);
    $display("Rx_Len=%h", ReadData);

    ReadAddress_Rx(RX_BUFF , ReadData);
    $display("Rx_D =%h", ReadData);
    ReadAddress_Rx(RX_BUFF , ReadData);
    $display("Rx_D =%b", ReadData);

    ReadAddress_Rx(RX_BUFF , ReadData);
    $display("Rx_D =%b", ReadData);

  endtask


  task Tx_sendRandom();
  logic [7:0] size;
  automatic logic done = 1'b0;
  logic [7:0] ReadData;


  size = $urandom_range(3, 126);

  for (int i = 0; i < size; i++) begin
  	WriteAddress_Tx(TX_BUFF, $urandom());
  end

   WriteAddress_Tx(TX_SC,TX_ENABLE);

    while(!done)
    begin
   		ReadAddress_Tx(TX_SC,ReadData);
        done = ReadData[0];
    end

  endtask


  task Tx_sendAbort();
  automatic logic done = 1'b0;
  logic [7:0] ReadData;
  int size;
	    $display("%t Tx New abort message ================", $time);
  size = $urandom_range(50, 120);

  for (int i = 0; i < size; i++) begin
  	WriteAddress_Tx(TX_BUFF, $urandom());
  end

   WriteAddress_Tx(TX_SC,TX_ENABLE);

    repeat(1000)
  		@(posedge uin_hdlc.Clk);

   WriteAddress_Tx(TX_SC,TX_ABORTFRAME);


    while(!done)
    begin
   		ReadAddress_Tx(TX_SC,ReadData);
        done = ReadData[0];
    end
    repeat(2)
  		@(posedge uin_hdlc.Clk);

  endtask

  task Tx_send(input int size);
  automatic logic done = 1'b0;
  logic [7:0] ReadData;
	    $display("%t Tx New short message ================", $time);


  for (int i = 0; i < size; i++) begin
  	WriteAddress_Tx(TX_BUFF, $urandom());
  end

   WriteAddress_Tx(TX_SC,TX_ENABLE);

    while(!done)
    begin
   		ReadAddress_Tx(TX_SC,ReadData);
        done = ReadData[0];
    end
    repeat(2)
  		@(posedge uin_hdlc.Clk);

  endtask


  task Tx_sendOverflow();
  logic [7:0] size;
  automatic logic done = 1'b0;
  logic [7:0] ReadData;
	    $display("%t Tx New Overflow message ================", $time);


  size = 130;

  for (int i = 0; i < size; i++) begin
  	WriteAddress_Tx(TX_BUFF, $urandom());
  end

   WriteAddress_Tx(TX_SC,TX_ENABLE);

    while(!done)
    begin
   		ReadAddress_Tx(TX_SC,ReadData);
        done = ReadData[0];
    end
    repeat(2)
  		@(posedge uin_hdlc.Clk);

  endtask




  task Rx_Byte(input logic [7:0] Data);
  for (int i = 0; i < 8; i++) begin
        uin_hdlc.Rx = Data[i];
      @(posedge uin_hdlc.Clk);
  end
  endtask

  task Rx_sendRandom();
  automatic logic [127:0][7:0] Data = '0;
  logic [7:0] size;
  logic        [15:0] FCSbytes;

  size = $urandom_range(1, 126);

  for (int i = 0; i < size; i++) begin
  	Data[i] = $urandom();
  end

  CalculateFCS(Data, size, {Data[size+1],Data[size]});

  size = size + 2;
  Rx_Byte(FLAG);
  Rx_multisend(Data,size);
  Rx_Byte(FLAG);
  endtask

task Rx_sendAbort();
  automatic logic [127:0][7:0] Data = '0;
    logic [7:0] ReadData;
    logic [7:0] size;

	$display("%t Rx New Aborted message ================", $time);

  size = $urandom_range(1, 122);

  for (int i = 0; i < size; i++) begin
  	Data[i] = $urandom();
  end

    Rx_Byte(FLAG);
    Rx_multisend(Data,size);
	Rx_Byte(ABORT);

    uin_hdlc.Rx = 1'b1;

	ReadAddress_Rx(RX_SC, ReadData);
	$display("Rx_SC=%b", ReadData);
endtask

  task Rx_multisend(input logic [140:0][7:0] data,
                       input int             size);
    automatic logic      [4:0] zeroPadding  = '0;

    for (int i = 0; i < size; i++) begin
      for (int j = 0; j < 8; j++) begin
        if (&zeroPadding) begin
          uin_hdlc.Rx      = 1'b0;
          @(posedge uin_hdlc.Clk);
          zeroPadding      = zeroPadding >> 1;
          zeroPadding[4]   = 0;
        end
        zeroPadding      = zeroPadding >> 1;
        zeroPadding[4]   = data[i][j];
        uin_hdlc.Rx      = data[i][j];
        @(posedge uin_hdlc.Clk);
      end
    end
  endtask

  task Rx_sendoverflow();
  automatic logic [140:0][7:0] Data = '0;
    logic [7:0] ReadData;
    logic [7:0] ReadLen;
    logic [7:0] size;

	$display("%t Rx New Overflow message ================", $time);
  size = $urandom_range(130, 139);

  for (int i = 0; i < size; i++) begin
  	Data[i] = $urandom();
  end
   Rx_Byte(FLAG);
   Rx_multisend(Data,size);
   Rx_Byte(FLAG);
	    uin_hdlc.Rx = 1'b1;

	    repeat(10)
	      @(posedge uin_hdlc.Clk);

	    ReadAddress_Rx(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);


	    ReadAddress_Rx(RX_LEN , ReadLen);
	    $display("Rx_Len=%d", ReadLen);

  endtask

  task Rx_sendCRCerror();
   automatic logic [4:0][7:0] shortmessage = '0;
    logic [7:0] ReadData;
    logic [7:0] ReadLen;

	$display("%t Rx New CRC error message ================", $time);

	shortmessage[0] = 'h11;
	shortmessage[1] = 'h44;
	shortmessage[2] = 'h01;
	shortmessage[3] = 'h22;

    Rx_Byte(FLAG);
    Rx_multisend(shortmessage,4);

    Rx_Byte(FLAG);
    uin_hdlc.Rx = 1'b1;

	    repeat(10)
	      @(posedge uin_hdlc.Clk);

	    ReadAddress_Rx(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);


	    ReadAddress_Rx(RX_LEN , ReadLen);
	    $display("Rx_Len=%d", ReadLen);

  endtask

  task Rx_sendNonAligned();
   automatic logic [4:0][7:0] shortmessage = '0;
    logic [7:0] ReadData;
    logic [7:0] ReadLen;

	$display("%t Rx New non aligned message ================", $time);

	shortmessage[0] = 'h11;
	shortmessage[1] = 'h44;
	shortmessage[2] = 'h01;
	shortmessage[3] = 'h22;

    Rx_Byte(FLAG);
    Rx_multisend(shortmessage,4);
    uin_hdlc.Rx = 1'b0;
	repeat(4)
		@(posedge uin_hdlc.Clk);
	uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
	repeat(2)
		@(posedge uin_hdlc.Clk);

    Rx_Byte(FLAG);
    uin_hdlc.Rx = 1'b1;

	    repeat(10)
	      @(posedge uin_hdlc.Clk);

	    ReadAddress_Rx(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);


	    ReadAddress_Rx(RX_LEN , ReadLen);
	    $display("Rx_Len=%d", ReadLen);

      for (int i = 0; i < ReadLen; i++) begin
   		ReadAddress_Rx(RX_BUFF , ReadData);
	  end


  endtask


  task CalculateFCS(input  logic [127:0][7:0]  data,
                    input  logic [7:0]         size,
                    output logic [15:0]        FCSbytes );

    logic [23:0] tempStore;
    tempStore[7:0]  = data[0];
    tempStore[15:8] = data[1];

    for (int i = 2; i < size + 2; i++) begin
      tempStore[23:16] = data[i];
      for (int j = 0; j < 8; j++) begin
        tempStore[16] = tempStore[16] ^ tempStore[0];
        tempStore[14] = tempStore[14] ^ tempStore[0];
        tempStore[1]  = tempStore[1]  ^ tempStore[0];
        tempStore[0]  = tempStore[0]  ^ tempStore[0];
        tempStore = tempStore >> 1;
      end
    end
    FCSbytes = tempStore[15:0];
  endtask


  task WriteAddress_Tx(input logic [2:0] Address ,input logic [7:0] Data);
     sema.get(1);

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address     = Address;
    uin_hdlc.WriteEnable = 1'b1;
    uin_hdlc.DataIn      = Data;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.WriteEnable = 1'b0;

    sema.put(1);

  endtask

    task WriteAddress_Rx(input logic [2:0] Address ,input logic [7:0] Data);
     sema.get(1);

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address     = Address;
    uin_hdlc.WriteEnable = 1'b1;
    uin_hdlc.DataIn      = Data;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.WriteEnable = 1'b0;

    sema.put(1);

  endtask

  task ReadAddress_Tx(input logic [2:0] Address ,output logic [7:0] Data);
    sema.get(1);

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address    = Address;
    uin_hdlc.ReadEnable = 1'b1;
    #100ns;
    Data                = uin_hdlc.DataOut;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.ReadEnable = 1'b0;

    sema.put(1);

  endtask

  task ReadAddress_Rx(input logic [2:0] Address ,output logic [7:0] Data);
    sema.get(1);

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address    = Address;
    uin_hdlc.ReadEnable = 1'b1;
    #100ns;
    Data                = uin_hdlc.DataOut;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.ReadEnable = 1'b0;

    sema.put(1);

  endtask
endprogram
