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
  parameter ABORT = 8'b0111_1111;

  int TbErrorCnt;

  initial begin
    $display("*************************************************************");
    $display("%t - Starting Test Program", $time);
    $display("*************************************************************");

    init();

    //Tests:


    //Receive();
    Transmit();

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

  task WriteAddress(input logic [2:0] Address ,input logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address     = Address;
    uin_hdlc.WriteEnable = 1'b1;
    uin_hdlc.DataIn      = Data;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.WriteEnable = 1'b0;
  endtask

  task ReadAddress(input logic [2:0] Address ,output logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address    = Address;
    uin_hdlc.ReadEnable = 1'b1;
    #100ns;
    Data                = uin_hdlc.DataOut;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.ReadEnable = 1'b0;
  endtask


  task Transmit();
    logic [7:0] ReadData;
    repeat(10)
  		@(posedge uin_hdlc.Clk);

//	Tx_sendRandom();

	Tx_send(3);
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



  for (int i = 0; i < 0; i++) begin
	    $display("%t New random message ================", $time);

		Tx_sendRandom();
    repeat($urandom_range(0, 20))
  		@(posedge uin_hdlc.Clk);

	    ReadAddress(TX_SC, ReadData);
	    $display("Tx_SC=%b", ReadData);

    repeat(90)
  		@(posedge uin_hdlc.Clk);


  end

    repeat(90)
  		@(posedge uin_hdlc.Clk);

  endtask


  task Tx_sendRandom();
  logic [7:0] size;
  automatic logic done = 1'b0;
  logic [7:0] ReadData;


  size = $urandom_range(2, 126);

  for (int i = 0; i < size; i++) begin
  	WriteAddress(TX_BUFF, $urandom());
  end

   WriteAddress(TX_SC,TX_ENABLE);

    while(!done)
    begin
   		ReadAddress(TX_SC,ReadData);
        done = ReadData[0];
    end

  endtask


  task Tx_sendAbort();
  automatic logic done = 1'b0;
  logic [7:0] ReadData;
  int size;
	    $display("%t New abort message ================", $time);
  size = $urandom_range(50, 120);

  for (int i = 0; i < size; i++) begin
  	WriteAddress(TX_BUFF, $urandom());
  end

   WriteAddress(TX_SC,TX_ENABLE);

    repeat(700)
  		@(posedge uin_hdlc.Clk);

   WriteAddress(TX_SC,TX_ABORTFRAME);


    while(!done)
    begin
   		ReadAddress(TX_SC,ReadData);
        done = ReadData[0];
    end
    repeat(2)
  		@(posedge uin_hdlc.Clk);

  endtask

  task Tx_send(input int size);
  automatic logic done = 1'b0;
  logic [7:0] ReadData;
	    $display("%t New short message ================", $time);


  for (int i = 0; i < size; i++) begin
  	WriteAddress(TX_BUFF, $urandom());
  end

   WriteAddress(TX_SC,TX_ENABLE);

    while(!done)
    begin
   		ReadAddress(TX_SC,ReadData);
        done = ReadData[0];
    end
    repeat(2)
  		@(posedge uin_hdlc.Clk);

  endtask


  task Tx_sendOverflow();
  logic [7:0] size;
  automatic logic done = 1'b0;
  logic [7:0] ReadData;
	    $display("%t New Overflow message ================", $time);


  size = 130;

  for (int i = 0; i < size; i++) begin
  	WriteAddress(TX_BUFF, $urandom());
  end

   WriteAddress(TX_SC,TX_ENABLE);

    while(!done)
    begin
   		ReadAddress(TX_SC,ReadData);
        done = ReadData[0];
    end
    repeat(2)
  		@(posedge uin_hdlc.Clk);

  endtask



  task Receive();
    logic [7:0] ReadData;
    logic [7:0] ReadLen;
  automatic logic [4:0][7:0] shortmessage = '0;


   WriteAddress(RX_SC,RX_FCSEN);

	//Rx_Byte(FLAG);
	//Rx_Byte('h2D);

	//Rx_Byte(ABORT);


	$display("%t New remove zero message ================", $time);
    uin_hdlc.Rx = 1'b1;
	    repeat(2)
	      @(posedge uin_hdlc.Clk);
	Rx_Byte(FLAG);

/////////////////////////////////
//Data
//	Rx_Byte('h2D);
//	Rx_Byte('h2D);
//Checksum
//	Rx_Byte('hDD);
//	Rx_Byte('h4D);
////////////////////////////////

	//Data
	Rx_Byte('h2D);
	//7E
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;	//Will be removed
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
   // WriteAddress(RX_SC,RX_DROP);

	//Checksum
	Rx_Byte('h9D);
	Rx_Byte('h70);
	
	Rx_Byte(FLAG);
    uin_hdlc.Rx = 1'b1;
	    repeat(18)
	      @(posedge uin_hdlc.Clk);

	$display("%t New remove zero message ================", $time);

	shortmessage[0] = 'h71;
	shortmessage[1] = 'h9B;

	//shortmessage[0] = 8'b11111000;
	//shortmessage[1] = 8'b01001000;


	CalculateFCS(shortmessage, 2, {shortmessage[3],shortmessage[2]});
    Rx_Byte(FLAG);
    Rx_multisend(shortmessage,4);
    Rx_Byte(FLAG);
    uin_hdlc.Rx = 1'b1;


	    repeat(15)
	      @(posedge uin_hdlc.Clk);
Rx_sendCRCerror();

Rx_sendoverflow();
Rx_sendNonAligned();

/*
	$display("%t New Aborted message ================", $time);

	shortmessage[0] = 'h00;
	shortmessage[1] = 'h00;


    Rx_Byte(FLAG);
    Rx_multisend(shortmessage,2);
	Rx_Byte(ABORT);

    uin_hdlc.Rx = 1'b1;
	    repeat(10)
	      @(posedge uin_hdlc.Clk);

	    ReadAddress(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);
*/

  //Loop for reciving lots of valid random data
  for (int i = 0; i < 1; i++) begin
	    $display("%t New random message ================", $time);

	    Rx_sendRandom();
	    uin_hdlc.Rx = 1'b1;

	    repeat(10)
	      @(posedge uin_hdlc.Clk);

	    ReadAddress(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);


	    ReadAddress(RX_LEN , ReadLen);
	    $display("Rx_Len=%d", ReadLen);

	  for (int i = 0; i < ReadLen; i++) begin
   		ReadAddress(RX_BUFF , ReadData);
	  end

  end

    uin_hdlc.Rx = 1'b1;

    repeat(16)
      @(posedge uin_hdlc.Clk);
    ReadAddress(RX_SC, ReadData);
    $display("Rx_SC=%b", ReadData);


    ReadAddress(RX_LEN , ReadData);
    $display("Rx_Len=%h", ReadData);

    ReadAddress(RX_BUFF , ReadData);
    $display("Rx_D =%h", ReadData);
    ReadAddress(RX_BUFF , ReadData);
    $display("Rx_D =%b", ReadData);

    ReadAddress(RX_BUFF , ReadData);
    $display("Rx_D =%b", ReadData);

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

  task Rx_multisend(input logic [132:0][7:0] data,
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
  automatic logic [135:0][7:0] Data = '0;
    logic [7:0] ReadData;
    logic [7:0] ReadLen;

	$display("%t New Overflow message ================", $time);

  for (int i = 0; i < 134; i++) begin
  	Data[i] = $urandom();
  end
   Rx_Byte(FLAG);
   Rx_multisend(Data,130);
   Rx_Byte(FLAG);
	    uin_hdlc.Rx = 1'b1;

	    repeat(10)
	      @(posedge uin_hdlc.Clk);

	    ReadAddress(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);


	    ReadAddress(RX_LEN , ReadLen);
	    $display("Rx_Len=%d", ReadLen);

  endtask

  task Rx_sendCRCerror();
   automatic logic [4:0][7:0] shortmessage = '0;
    logic [7:0] ReadData;
    logic [7:0] ReadLen;

	$display("%t New CRC error message ================", $time);

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

	    ReadAddress(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);


	    ReadAddress(RX_LEN , ReadLen);
	    $display("Rx_Len=%d", ReadLen);

  endtask

  task Rx_sendNonAligned();
   automatic logic [4:0][7:0] shortmessage = '0;
    logic [7:0] ReadData;
    logic [7:0] ReadLen;

	$display("%t New non aligned message ================", $time);

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

	    ReadAddress(RX_SC, ReadData);
	    $display("Rx_SC=%b", ReadData);


	    ReadAddress(RX_LEN , ReadLen);
	    $display("Rx_Len=%d", ReadLen);

      for (int i = 0; i < ReadLen; i++) begin
   		ReadAddress(RX_BUFF , ReadData);
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





endprogram
