# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Any change in ROM instances path should be updated in following two files
# 1. hw/top_earlgrey/data/placement.xdc and
# 2. hw/top_earlgrey/util/vivado_hook_opt_design_post.tcl

send_msg "Designcheck 2-1" INFO "Checking if ROM memory is mapped to BRAM memory."

if {[catch [get_cells -hierarchical -filter { NAME =~  "*rom_rom*dout_o_reg_0" && PRIMITIVE_TYPE =~ BMEM.*.* }]]\
&& [catch [get_cells -hierarchical -filter { NAME =~  "*rom_rom*dout_o_reg_1" && PRIMITIVE_TYPE =~ BMEM.*.* }]] } {
  send_msg "Designcheck 2-2" INFO "BRAM implementation found for ROM memory."
} else {
  send_msg "Designcheck 2-3" INFO "BRAM implementation not found for ROM memory."
}
