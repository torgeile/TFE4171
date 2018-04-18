onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /test_hdlc/u_dut/Clk
add wave -noupdate /test_hdlc/u_dut/Rst
add wave -noupdate /test_hdlc/u_dut/Tx
add wave -noupdate /test_hdlc/u_dut/TxEN
add wave -noupdate /test_hdlc/u_dut/Tx_Enable
add wave -noupdate -divider TX_Buff
add wave -noupdate /test_hdlc/u_dut/Tx_WrBuff
add wave -noupdate /test_hdlc/u_dut/DataIn
add wave -noupdate /test_hdlc/u_dut/Tx_RdBuff
add wave -noupdate /test_hdlc/u_dut/Tx_Full
add wave -noupdate /test_hdlc/u_dut/Tx_AbortedTrans
add wave -noupdate /test_hdlc/u_dut/Tx_FrameSize
add wave -noupdate /test_hdlc/u_dut/Tx_Done
add wave -noupdate -divider TX_Channel
add wave -noupdate /test_hdlc/u_dut/Tx_NewByte
add wave -noupdate /test_hdlc/u_dut/Tx
add wave -noupdate /test_hdlc/u_dut/Tx_InitZero
add wave -noupdate /test_hdlc/u_dut/Tx_ValidFrame
add wave -noupdate -divider TX_FCS
add wave -noupdate /test_hdlc/u_dut/Tx_StartFCS
add wave -noupdate /test_hdlc/u_dut/Tx_WriteFCS
add wave -noupdate /test_hdlc/u_dut/Tx_FCSDone
add wave -noupdate -divider {New Divider}
add wave -noupdate /test_hdlc/u_dut/WriteEnable
add wave -noupdate /test_hdlc/u_dut/ReadEnable
add wave -noupdate /test_hdlc/u_dut/DataIn
add wave -noupdate /test_hdlc/u_dut/Address
add wave -noupdate /test_hdlc/u_dut/Tx_DataArray
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1144014 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 179
configure wave -valuecolwidth 57
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {1143700 ns} {1150068 ns}
