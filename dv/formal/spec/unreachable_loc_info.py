# Copyright lowRISC contributors.
# Copyright 2024 University of Oxford, see also CREDITS.md.
# Licensed under the Apache License, Version 2.0 (see LICENSE for details).
# Original Author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0

with open("build/ibexspec.sv", "r") as f:
    c = f.read()

c = c.replace(
    "sail_reached_unreachable = 1;",
    "begin sail_reached_unreachable = 1; sail_reached_unreachable_loc = `__LINE__; end"
).replace(
    "sail_reached_unreachable = 0;",
    "begin sail_reached_unreachable = 0; sail_reached_unreachable_loc = -1; end"
).replace(
    "bit sail_reached_unreachable;",
    "bit sail_reached_unreachable;\n\tlogic [31:0] sail_reached_unreachable_loc;"
)

with open("build/ibexspec.sv", "w") as f:
    f.write(c)
