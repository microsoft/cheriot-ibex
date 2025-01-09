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

for func_name in names:
    m = re.search(r"^(\s*)function automatic .+ " + func_name + r"\(.*\);", c, re.MULTILINE)
    assert m is not None
    end = c.index("endfunction", m.start())
    assert end >= 0

    c = c[0:m.start()] + c[end + 11:]

with open("build/ibexspec.sv", "w") as f:
    f.write(c)
