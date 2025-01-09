# Copyright lowRISC contributors.
# Copyright 2024 University of Oxford, see also CREDITS.md.
# Licensed under the Apache License, Version 2.0 (see LICENSE for details).
# Original Author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0

import sys
import re

names = sys.argv[1:]

with open("build/ibexspec.sv", "r") as f:
    c = f.read()

constants = {
    "cap_max_E_bits": "5'h18"
}

for func_name in names:
    m = re.search(r"^(\s*)function automatic .+ " + func_name + r"\(.*\);", c, re.MULTILINE)
    assert m is not None
    end = c.index("endfunction", m.start())
    assert end >= 0

    func = c[m.start():end + 11][1:]
    func = "\n".join(line[len(m[1]) - 1:] for line in func.split("\n"))

    for k in constants:
        func = re.sub(r"\b" + k + r"\b", constants[k], func)
    func = func.replace("sail_reached_unreachable = 1;", "").replace("sail_reached_unreachable_loc = `__LINE__;", "")
    
    print(func)
    print()
