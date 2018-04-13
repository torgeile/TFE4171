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



  input logic Tx_AbortedTrans
  );


  initial begin
    ErrCntAssertions = 0;
  end

  sequence Rx_flag;
    !Rx ##1 Rx [*6] ##1 !Rx;
  endsequence

  // Check if flag sequence is detected
  property Receive_FlagDetect;
    @(posedge Clk) disable iff (!Rst) Rx_flag |-> ##2 Rx_FlagDetect;
  endproperty


  sequence Rx_abort;
    !Rx ##1 Rx [*7] ##1 !Rx;
  endsequence

  property Receive_AbortDetect;
    @(posedge Clk) disable iff (!Rst) Rx_abort |-> ##1 Rx_AbortDetect;
  endproperty

  sequence Rx_Zero;
    !Rx ##1 Rx [*5] ##1 !Rx;
  endsequence


  property Receive_RemoveZero;
   logic passed = 1'b0;
    @(posedge Clk) disable iff (!Rst) Rx_Zero |-> ##[5:13]Rx_NewByte  ##1 (Rx_Data==Zeroremove({$past(Rx,25),$past(Rx,24),$past(Rx,23),$past(Rx,22),$past(Rx,21),$past(Rx,20),$past(Rx,19),$past(Rx,18),$past(Rx,17),$past(Rx,16),$past(Rx,15),$past(Rx,14),$past(Rx,13),$past(Rx,12),$past(Rx,11)}));
  endproperty

  Receive_RemoveZero_Assert    	:  assert property (Receive_RemoveZero) $display("PASS: Receive_RemoveZero");
                           		else begin $error("Extra zero was not removed zero?"); ErrCntAssertions++; end


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
//$display("tempdata=%b %h", tempdata, tempdata);


   return (tempdata[15:8]);
  endfunction

  

  Receive_FlagDetect_Assert    :  assert property (Receive_FlagDetect) $display("PASS: Receive_FlagDetect");
                                  else begin $error("Flag sequence did not generate FlagDetect"); ErrCntAssertions++; end

  Receive_AbortDetect_Assert   :  assert property (Receive_AbortDetect) $display("PASS: Receive_AbortDetect");
                                  else begin $error("Abort sequence did not generate AbortDetect"); ErrCntAssertions++; end

/*
  property Transmit_AbortDetect;
    @(posedge Clk) Tx_AbortedTrans |-> ##1 Rx_abort;
  endproperty

  Transmit_AbortInsert_Assert  :  assert property (Transmit_AbortDetect) $display("PASS: Transmit_AbortDetect");
                                  else begin $error("Abort sequence did not generated after Tx_AbortedTrans"); ErrCntAssertions++; end
*/

endmodule



/*

  sequence Rx_Zero;
    !Rx ##1 Rx [*5] ##1 !Rx;
  endsequence


  property Receive_RemoveZero;
   logic passed = 1'b0;
   logic [7:0] Byte = '0;


//    @(posedge Clk) disable iff (!Rst) Rx_Zero |-> ##[13:21]Rx_NewByte  ##1 (1,passed=Zerocompare({$past(Rx,28),$past(Rx,27),$past(Rx,26),$past(Rx,25),$past(Rx,24),$past(Rx,23),$past(Rx,22),$past(Rx,21),$past(Rx,20),$past(Rx,19),$past(Rx,18),$past(Rx,17),$past(Rx,16),$past(Rx,15),$past(Rx,14),$past(Rx,13),$past(Rx,12),$past(Rx,11)} , {Rx_Data}))
//    @(posedge Clk) disable iff (!Rst) Rx_Zero |-> ##[5:13]Rx_NewByte  ##1 (1,passed=Zerocompare({$past(Rx,20),$past(Rx,19),$past(Rx,18),$past(Rx,17),$past(Rx,16),$past(Rx,15),$past(Rx,14),$past(Rx,13),$past(Rx,12),$past(Rx,11),$past(Rx,10),$past(Rx,9),$past(Rx,8),$past(Rx,7),$past(Rx,6),$past(Rx,5),$past(Rx,4),$past(Rx,3)} , {Rx_Data}))
//VIRKER!    @(posedge Clk) disable iff (!Rst) Rx_Zero |-> ##[5:13]Rx_NewByte ##1 (1,passed=Zerocompare({$past(Rx,28),$past(Rx,27),$past(Rx,26),$past(Rx,25),$past(Rx,24),$past(Rx,23),$past(Rx,22),$past(Rx,21),$past(Rx,20),$past(Rx,19),$past(Rx,18),$past(Rx,17),$past(Rx,16),$past(Rx,15),$past(Rx,14),$past(Rx,13),$past(Rx,12),$past(Rx,11)} , Rx_Data))
    @(posedge Clk) disable iff (!Rst) Rx_Zero |-> ##[5:13]Rx_NewByte  ##1 (1,passed=Zerocompare({$past(Rx,28),$past(Rx,27),$past(Rx,26),$past(Rx,25),$past(Rx,24),$past(Rx,23),$past(Rx,22),$past(Rx,21),$past(Rx,20),$past(Rx,19),$past(Rx,18),$past(Rx,17),$past(Rx,16),$past(Rx,15),$past(Rx,14),$past(Rx,13),$past(Rx,12),$past(Rx,11)} , Rx_Data))

     ##0(passed);
  endproperty

  Receive_RemoveZero_Assert    	:  assert property (Receive_RemoveZero) $display("PASS: Receive_RemoveZero");
                           		else begin $error("Extra zero was not removed zero?"); ErrCntAssertions++; end


function automatic logic Zerocompare(logic [17:0] InData, logic [7:0] OutData);
automatic   int oneCount = 0;
automatic   logic [15:0] tempdata;
automatic   logic  skipnext = 0;

$display("Time= %d", $time);
//$display("Rx_Data =%b", Rx_Data);

    for (int i = 16; i >= 0; i--) begin
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

$display("InData  =%b %h", InData, InData);
$display("tempdata=%b %h", tempdata, tempdata);
$display("OutData =%b %h", OutData, OutData);


   //retrun {tempdata[7:0],tempdata[13:8]};
   return (tempdata[15:8] == OutData);
  endfunction
*/