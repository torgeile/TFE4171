onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /test_hdlc/u_dut/Clk
add wave -noupdate /test_hdlc/u_dut/RxEN
add wave -noupdate /test_hdlc/u_dut/Rst
add wave -noupdate /test_hdlc/u_dut/Rx
add wave -noupdate -divider {New Divider}
add wave -noupdate /test_hdlc/u_dut/Rx_StartZeroDetect
add wave -noupdate /test_hdlc/u_dut/Rx_ValidFrame
add wave -noupdate /test_hdlc/u_dut/Rx_AbortDetect
add wave -noupdate /test_hdlc/u_dut/Rx_FlagDetect
add wave -noupdate /test_hdlc/u_dut/Rx_NewByte
add wave -noupdate /test_hdlc/u_dut/Rx_Data
add wave -noupdate -divider {RX FCS}
add wave -noupdate /test_hdlc/u_dut/Rx_StopFCS
add wave -noupdate /test_hdlc/u_dut/Rx_StartFCS
add wave -noupdate /test_hdlc/u_dut/RxD
add wave -noupdate /test_hdlc/u_dut/Rx_FCSerr
add wave -noupdate /test_hdlc/u_dut/Rx_FCSen
add wave -noupdate /test_hdlc/u_dut/u_RxFCS/FCS_reg
add wave -noupdate -divider {New Divider}
add wave -noupdate /test_hdlc/u_dut/Address
add wave -noupdate /test_hdlc/u_dut/DataIn
add wave -noupdate /test_hdlc/u_dut/DataOut
add wave -noupdate /test_hdlc/u_dut/WriteEnable
add wave -noupdate /test_hdlc/u_dut/ReadEnable
add wave -noupdate -divider {New Divider}
add wave -noupdate /test_hdlc/u_dut/Rx_Drop
add wave -noupdate /test_hdlc/u_dut/Rx_EoF
add wave -noupdate /test_hdlc/u_dut/Rx_RdBuff
add wave -noupdate /test_hdlc/u_dut/Rx_WrBuff
add wave -noupdate /test_hdlc/u_dut/Rx_Ready
add wave -noupdate /test_hdlc/u_dut/Rx_Overflow
add wave -noupdate /test_hdlc/u_dut/Rx_FrameSize
add wave -noupdate /test_hdlc/u_dut/Rx_DataBuffOut
add wave -noupdate -divider {New Divider}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {29007 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 191
configure wave -valuecolwidth 100
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
WaveRestoreZoom {27019 ns} {42437 ns}
