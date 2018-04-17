//////////////////////////////////////////////////
// Title:   assertions_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

module assertions_hdlc (
  output int  ErrCntAssertions,
  input logic Clk,
  input logic Rst,
  input logic Rx,
  input logic Rx_FlagDetect,
  input logic Rx_AbortDetect,
  input logic Rx_StartZeroDetect,
  input logic Rx_NewByte,
  input logic [7:0] Rx_Data,
  input logic Rx_Overflow,
  input logic Rx_EoF,
  input logic Rx_ValidFrame,
  input logic [7:0]Rx_FrameSize,
  input logic [127:0][7:0] Rx_DataArray,
  input logic Rx_FrameError,
  input logic Rx_FCSen,
  input logic [7:0]Rx_DataBuffOut,
  input logic Rx_AbortSignal,
  input logic Rx_Ready,
  input logic Rx_FCSerr,




  input logic Tx_AbortedTrans,
  input logic Tx,
  input logic Tx_Done,
  input logic Tx_Full,
  input logic Tx_FCSDone,
  input logic Tx_AbortFrame,
  input logic Tx_NewByte,
  input logic Tx_Enable,
  input logic Tx_ValidFrame,
  input logic [7:0]Tx_FrameSize,
  input logic Tx_RdBuff,


  input logic [2:0] Address,
  input logic ReadEnable,
  input logic WriteEnable,
  input logic [7:0]DataOut,
  input logic [7:0]DataIn


  );

  parameter RX_BUFF = 3'b011;

  initial begin
    ErrCntAssertions = 0;
  end

  sequence Rx_flag;
    !Rx ##1 Rx [*6] ##1 !Rx;
  endsequence

  // 
  property Receive_FlagDetect;
    @(posedge Clk) disable iff (!Rst) Rx_flag |-> ##2 $rose(Rx_FlagDetect);
  endproperty


  sequence Rx_abort; //TODO: Denne er feil, test med den riktige:   !Rx ##1 Rx [*7]
     Rx [*7] ##1 !Rx;
  endsequence

  //10
  property Receive_AbortDetect;
     @(posedge Clk) disable iff (!Rst || !Rx_ValidFrame) Rx_abort |-> ##1 $rose(Rx_AbortDetect);
  endproperty


  sequence Rx_Zero;
    !Rx ##1 Rx [*5] ##1 !Rx;
  endsequence

  // (6)B
  property Receive_RemoveZero;
    @(posedge Clk) disable iff (!Rst) Rx_Zero |-> first_match(##[9:19]Rx_NewByte)  ##1 
    (Rx_Data==Zeroremove({$past(Rx,25),$past(Rx,24),$past(Rx,23),$past(Rx,22),$past(Rx,21),$past(Rx,20),$past(Rx,19),$past(Rx,18),$past(Rx,17),$past(Rx,16),$past(Rx,15),$past(Rx,14),$past(Rx,13),$past(Rx,12),$past(Rx,11)}));
  endproperty



  // 13
  property Rx_Overflowed;
   @(posedge Clk) disable iff (!Rst)  Rx_flag ##[18:19] Rx_NewByte ##0 (##[7:9] Rx_NewByte) [*128] |-> ##1 $rose(Rx_Overflow);
  endproperty

  //12
  property Rx_Endoffile;
   @(posedge Clk) disable iff (!Rst) Rx_flag ##[18:19] Rx_NewByte ##0 Rx_ValidFrame [*1:$] ##1 !Rx_ValidFrame |-> ##1 $rose(Rx_EoF);
  endproperty


  // 14
  property Receive_FrameSize;
   int framesize = 1;
   @(posedge Clk) disable iff (!Rst) Rx_flag ##[18:19] Rx_NewByte ##0 (##[7:9] (Rx_NewByte, framesize++)) [*1:128]  ##0 Rx_FlagDetect
   |-> ##6 (framesize-2==Rx_FrameSize);
  endproperty

  // 1 //Stemmer pga. 6.B
  property Receive_Buffer;
  logic [127:0] [7:0] tempBuffer = '0;
  int framesize = 0;
   @(posedge Clk) disable iff (!Rst) Rx_flag ##[18:19] Rx_NewByte ##0 (##[7:9] (Rx_NewByte,tempBuffer[framesize]=Rx_Data, framesize++)) [*1:128] ##0 Rx_FlagDetect  
   |-> ##6 (1,tempBuffer[framesize]=Rx_Data, framesize++) ##0 compareArray(tempBuffer,Rx_DataArray,framesize);
  endproperty


  //11 B
  property Receive_CRC;
  logic [127:0] [7:0] tempBuffer = '0;
  int framesize = 0;
   @(posedge Clk) disable iff (!Rst) Rx_flag ##[18:19] Rx_NewByte ##0 (##[7:9] (Rx_NewByte,tempBuffer[framesize]=Rx_Data, framesize++)) [*1:128] ##0 Rx_FlagDetect  
   |-> ##6 (1,tempBuffer[framesize]=Rx_Data, framesize++) ##0 (Rx_FrameError == !checkCRC(tempBuffer,framesize,Rx_FCSen));
  endproperty

  //16
  property Receive_NonAligned;
   @(posedge Clk) disable iff (!Rst)  Rx_NewByte ##[1:7] Rx_FlagDetect
   |-> ##2 $rose(Rx_FrameError);
  endproperty


  //2
  property Receive_ReadAfterError;
    @(posedge Clk) disable iff (!Rst) (Rx_FrameError || Rx_Overflow || Rx_AbortSignal) && Address==RX_BUFF && ReadEnable  |-> ##0 (DataOut == '0); //Sjekk denne
  endproperty


  //15 //Mulig denne er for dårlig //Prøv å lag en sjekk for at ikke all data har blitt lest fra bufferet??
  property Receive_ReadyValid;
    @(posedge Clk) disable iff (!Rst) Rx_Ready |-> !(Rx_FrameError || Rx_Overflow || Rx_AbortSignal);
  endproperty



	//3 (disse er gyldige siden Rx_FrameError,Rx_AbortDetect og Rx_Overflow er sjekket andre steder)
  property Receive_FrameError_reg;
   @(posedge Clk) disable iff (!Rst) $rose(Rx_FrameError) |-> ##1 Rx_FrameError until_with first_match(##[0:$] Rx_FlagDetect) ##1 !Rx_FrameError;
  endproperty

  property Receive_Abort_reg;
    @(posedge Clk) disable iff (!Rst) $rose(Rx_AbortDetect && Rx_ValidFrame) |-> ##1 Rx_AbortSignal until_with first_match(##[0:$] Rx_FlagDetect) ##1 !Rx_AbortSignal;
  endproperty

  property Receive_Overflowed_reg;
   @(posedge Clk) disable iff (!Rst) $rose(Rx_Overflow) |-> ##1 Rx_Overflow until_with first_match(##[0:$] Rx_FlagDetect) ##1 !Rx_Overflow;
  endproperty

  sequence Tx_flag;
    !Tx ##1 Tx [*6] ##1 !Tx;
  endsequence

  //5
  property Transmit_startframe;
    @(posedge Clk) disable iff (!Rst || Tx_AbortedTrans) $rose(Tx_Enable) ##0 first_match(##[1:$] $rose(Tx_FCSDone)) ##0 first_match(##[0:$] !Tx_ValidFrame)|-> ##[1:7] Tx_flag;
  endproperty

  property Transmit_endframe;
    @(posedge Clk) disable iff (!Rst || Tx_AbortedTrans) 
  $rose(Tx_Enable) ##0 first_match(##[1:$] $rose(Tx_FCSDone)) ##0 first_match(##[0:$] !Tx_ValidFrame) ##0
    first_match(##[0:$] $fell(Tx_ValidFrame && Tx_FCSDone)) |-> ##[1:7] Tx_flag;
  endproperty



  //17 
  property Transmit_done;
  	int framesize = 0;
 /*   @(posedge Clk) disable iff (!Rst) $rose(Tx_Enable) ##1 (1,framesize=Tx_FrameSize-1,$display("SF %d %t",framesize,$time())) ##0 first_match(##[1:$] $rose(Tx_FCSDone)) 
    ##[0:1] (Tx_RdBuff, framesize--,$display("FS %d %t",framesize,$time())) ##0 (##[1:11] (Tx_RdBuff, framesize--,$display("FS %d %t",framesize,$time()))) [*0:128] ##0  (framesize <= 0) 
    |-> ##1 Tx_Done;
*/

    @(posedge Clk) disable iff (!Rst) $rose(Tx_Enable) ##1 (1,framesize=Tx_FrameSize-1) ##0 first_match(##[1:$] $rose(Tx_FCSDone)) 
    ##[0:1] (Tx_RdBuff, framesize--) ##0 (##[1:11] (Tx_RdBuff, framesize--)) [*0:128] ##0  (framesize <= 0) 
    |-> ##1 Tx_Done;
  endproperty

  //18
  property Transmit_overflow;                                                       //XXXXXX1X
    @(posedge Clk) disable iff (!Rst || ((Address == 0 && WriteEnable && DataIn == 8'b00000010))) $fell(Tx_Done) ##0 (Address == 1 && WriteEnable) [->127] |-> ##0 Tx_Full;
  
  endproperty


  //9
  property Transmit_aborted;
    @(posedge Clk) disable iff (!Rst) (Address == 0 && WriteEnable && DataIn == 8'b00000100 && !Tx_Done) |-> ##3 Tx_AbortedTrans;
  
  endproperty


//8

  sequence Tx_abort;
    !Tx ##1 Tx [*7];
  endsequence


  property Transmit_abort_gen;
    @(posedge Clk) disable iff (!Rst) $rose(Tx_AbortedTrans) |-> ##[2:4] Tx_abort;
  
  endproperty




function automatic logic checkCRC([127:0] [7:0] arrayA, int size, logic Rx_FCSen);
automatic logic noError = 1'b1;
    logic [15:0] tempCRC;
    logic [23:0] tempStore;

	tempCRC = {arrayA[size-1],arrayA[size-2]};
	arrayA[size-1] = '0;
	arrayA[size-2] = '0;

    tempStore[7:0]  = arrayA[0];
    tempStore[15:8] = arrayA[1];

    for (int i = 2; i < size; i++) begin
      tempStore[23:16] = arrayA[i];
      for (int j = 0; j < 8; j++) begin
        tempStore[16] = tempStore[16] ^ tempStore[0];
        tempStore[14] = tempStore[14] ^ tempStore[0];
        tempStore[1]  = tempStore[1]  ^ tempStore[0];
        tempStore[0]  = tempStore[0]  ^ tempStore[0];
        tempStore = tempStore >> 1;
      end
    end
//    $display("time = %t", $time);

//    $display("InArray =%h", arrayA[10:0]);

//    $display("tempCRC =%h", tempCRC);
//    $display("calcCRC =%h", tempStore[15:0]);

   if (Rx_FCSen) begin
//    $display("Return =%b", tempCRC == tempStore[15:0]);

   	return (tempCRC == tempStore[15:0]);

   end else begin
//    $display("Return force = 1");

   	return 1'b1;
   end
endfunction


function automatic logic compareArray([127:0] [7:0] arrayA, [127:0] [7:0] arrayB, int length);
automatic logic noError = 1'b1;

    for (int i = 0; i < length; i++) begin
    	if (arrayA[i] != arrayB[i]) begin
    		noError = 1'b0;
    	end 
        //$display("Rx_Data =%h", arrayA[i]);

    end
   return noError;
endfunction


function automatic logic[7:0] Zeroremove(logic [14:0] InData);
automatic   int oneCount = 0;
automatic   logic [15:0] tempdata;
automatic   logic  skipnext = 0;

//$display("Time= %d", $time);
//$display("Rx_Data =%b", Rx_Data);

    for (int i = 14; i >= 0; i--) begin
    	if (InData[i] == '0) begin
    		oneCount = 0;
    	end else begin
    		oneCount++;
    	end
		//$display("InData[i]  =%b", InData[i]);
		if (skipnext) begin end else begin
			tempdata = tempdata >> 1;
			tempdata[15] = InData[i];
		end

    	if (oneCount >= 5) begin
    		skipnext = 1;
    	end else begin
    		skipnext = 0;
    	end
    end
//$display("InData  =%b %h", InData, InData);
//$display("tempdata=%b %h", tempdata[return15:8],tempdata[15:8]);
   return (tempdata[15:8]);
  endfunction

   Receive_FCSerr_reg_Assert  :  assert property (Receive_FrameError_reg) $display("PASS: Receive_FrameError_reg");
	                       		else begin $error("Rx FrameError not set in reg"); ErrCntAssertions++; end
  Receive_Abort_reg_Assert  :  assert property (Receive_Abort_reg) $display("PASS: Receive_Abort_reg");
	                       		else begin $error("Rx Abort not set in reg"); ErrCntAssertions++; end
  Receive_Overflowed_reg_Assert  :  assert property (Receive_Overflowed_reg) $display("PASS: Receive_Overflowed_reg");
	                       		else begin $error("Rx Overflowed not set in reg"); ErrCntAssertions++; end


  Receive_ReadyValid_Assert  :  assert property (Receive_ReadyValid) /* $display("PASS: Receive_ReadyValid") ;*/
	                       		else begin $error("Rx ready not indicating ready data"); ErrCntAssertions++; end


  Receive_ReadAfterError_Assert  :  assert property (Receive_ReadAfterError)/* $display("PASS: Receive_ReadAfterError"); */
	                       		else begin $error("Rx Read after error error"); ErrCntAssertions++; end


  Receive_NonAligned_Assert    :  assert property (Receive_NonAligned) $display("PASS: Receive_NonAligned");
                                  else begin $error("Non aligen data not detected"); ErrCntAssertions++; end


  Receive_AbortDetect_Assert    :  assert property (Receive_AbortDetect) $display("PASS: Receive_AbortDetect");
                                  else begin $error("Abort sequence did not generate AbortDetect"); ErrCntAssertions++; end

  Receive_CRC_Assert    	    :  assert property (Receive_CRC) $display("PASS: Receive_CRC");
	                       		else begin $error("Rx CRC error"); ErrCntAssertions++; end

  Receive_Buffer_Assert    	    :  assert property (Receive_Buffer) $display("PASS: Receive_Buffer");
	                       		else begin $error("Rx buffer error"); ErrCntAssertions++; end


  Receive_FrameSize_Assert    	    :  assert property (Receive_FrameSize) $display("PASS: Receive_FrameSize");
	                       		else begin $error("Rx framesize error"); ErrCntAssertions++; end


  Rx_Overflow_Assert    	    :  assert property (Rx_Overflowed) $display("PASS: Rx_Overflowed");
                           		else begin $error("Rx overflow error"); ErrCntAssertions++; end

  Receive_FlagDetect_Assert     :  assert property (Receive_FlagDetect) $display("PASS: Receive_FlagDetect");
                                  else begin $error("Flag sequence did not generate FlagDetect"); ErrCntAssertions++; end


  Receive_RemoveZero_Assert    	:  assert property (Receive_RemoveZero) $display("PASS: Receive_RemoveZero");
                           		else begin $error("Extra zero was not removed zero?"); ErrCntAssertions++; end

  Rx_Endoffile_Assert    	    :  assert property (Rx_Endoffile) $display("PASS: Rx_EoF");
                           		else begin $error("Rx EoF error"); ErrCntAssertions++; end



   Transmit_aborted_Assert  :  assert property (Transmit_aborted) $display("PASS: Transmit_aborted");
	                       		else begin $error("Tx_AbortedTrans not set"); ErrCntAssertions++; end

   Transmit_overflow_Assert  :  assert property (Transmit_overflow) $display("PASS: Transmit_overflow");
	                       		else begin $error("Tx_Full not set"); ErrCntAssertions++; end


   Transmit_abort_gen_Assert  :  assert property (Transmit_abort_gen) $display("PASS: Transmit_abort_gen");
	                       		else begin $error("Abort pattern not generated"); ErrCntAssertions++; end


   Transmit_done_Assert  :  assert property (Transmit_done) $display("PASS: Transmit_done");
	                       		else begin $error("Tx_done not set"); ErrCntAssertions++; end


   Transmit_endframe_Assert  :  assert property (Transmit_endframe) $display("PASS: Transmit_endframe");
	                       		else begin $error("Tx end flag not generated"); ErrCntAssertions++; end

   Transmit_startframe_Assert  :  assert property (Transmit_startframe) $display("PASS: Transmit_startframe");
	                       		else begin $error("Tx Start flag not generated"); ErrCntAssertions++; end

/*
  property Transmit_AbortDetect;
    @(posedge Clk) Tx_AbortedTrans |-> ##1 Rx_abort;
  endproperty

  Transmit_AbortInsert_Assert  :  assert property (Transmit_AbortDetect) $display("PASS: Transmit_AbortDetect");
                                  else begin $error("Abort sequence did not generated after Tx_AbortedTrans"); ErrCntAssertions++; end
*/

endmodule