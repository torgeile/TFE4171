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

  input logic Tx_AbortedTrans
  );


  initial begin
    ErrCntAssertions = 0;
  end

  sequence Rx_flag;
    !Rx ##1 Rx [*6] ##1 !Rx;
  endsequence

  // 
  property Receive_FlagDetect;
    @(posedge Clk) disable iff (!Rst) Rx_flag |-> ##2 Rx_FlagDetect;
  endproperty


  sequence Rx_abort;
    !Rx ##1 Rx [*7] ##1 !Rx;
  endsequence

  //10
  property Receive_AbortDetect;
    @(posedge Clk) disable iff (!Rst) Rx_abort |-> ##1 Rx_AbortDetect;
  endproperty

  sequence Rx_Zero;
    !Rx ##1 Rx [*5] ##1 !Rx;
  endsequence

  // (6)B
  property Receive_RemoveZero;
    @(posedge Clk) disable iff (!Rst) Rx_Zero |-> first_match(##[9:19]Rx_NewByte)  ##1 (Rx_Data==Zeroremove({$past(Rx,25),$past(Rx,24),$past(Rx,23),$past(Rx,22),$past(Rx,21),$past(Rx,20),$past(Rx,19),$past(Rx,18),$past(Rx,17),$past(Rx,16),$past(Rx,15),$past(Rx,14),$past(Rx,13),$past(Rx,12),$past(Rx,11)}));
  endproperty



  // 13
  property Rx_Overflowed;
   @(posedge Clk) disable iff (!Rst) Rx_NewByte ##0 (##[7:9] Rx_NewByte) [*128] |-> ##1 Rx_Overflow;
  endproperty

  //12
  property Rx_Endoffile;
   @(posedge Clk) disable iff (!Rst) Rx_flag ##[18:19] Rx_NewByte ##0 Rx_ValidFrame [*1:(128*9)] ##1 !Rx_ValidFrame |-> ##1 Rx_EoF;
  endproperty




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
//$display("tempdata=%b %h", tempdata[15:8],tempdata[15:8]);
   return (tempdata[15:8]);
  endfunction

  Rx_Overflow_Assert    	    :  assert property (Rx_Overflowed) $display("PASS: Rx_Overflowed");
                           		else begin $error("Rx overflow error"); ErrCntAssertions++; end

  Receive_FlagDetect_Assert     :  assert property (Receive_FlagDetect) $display("PASS: Receive_FlagDetect");
                                  else begin $error("Flag sequence did not generate FlagDetect"); ErrCntAssertions++; end

  Receive_AbortDetect_Assert    :  assert property (Receive_AbortDetect) $display("PASS: Receive_AbortDetect");
                                  else begin $error("Abort sequence did not generate AbortDetect"); ErrCntAssertions++; end

  Receive_RemoveZero_Assert    	:  assert property (Receive_RemoveZero) $display("PASS: Receive_RemoveZero");
                           		else begin $error("Extra zero was not removed zero?"); ErrCntAssertions++; end
                           			
  Rx_Endoffile_Assert    	    :  assert property (Rx_Endoffile) $display("PASS: Rx_EoF");
                           		else begin $error("Rx EoF error"); ErrCntAssertions++; end



/*
  property Transmit_AbortDetect;
    @(posedge Clk) Tx_AbortedTrans |-> ##1 Rx_abort;
  endproperty

  Transmit_AbortInsert_Assert  :  assert property (Transmit_AbortDetect) $display("PASS: Transmit_AbortDetect");
                                  else begin $error("Abort sequence did not generated after Tx_AbortedTrans"); ErrCntAssertions++; end
*/

endmodule