## Project

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

## Trademarks

This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft
trademarks or logos is subject to and must follow
[Microsoft's Trademark & Brand Guidelines](https://www.microsoft.com/en-us/legal/intellectualproperty/trademarks/usage/general).
Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship.
Any use of third-party trademarks or logos are subject to those third-party's policies.

## Introduction
cheriot-ibex is 32-bit RISC-V microcontroller which implements the CHERIoT ISA extension in addition to RV32IMCB. Same as the original ibex core, the design can be configured either with a 2-stage or a 3-stage pipeline. It has passed preliminary simulation, formal verification and FPGA validation, and is currently under further verification at Microsoft.

![image](https://github.com/microsoft/cheriot-ibex/assets/116126768/51b768f5-a528-4d93-bce4-392ac2fe1488)

## CHERIoT ISA support

cheriot-ibex supports all instructions listed in the [CHERIoT ISA specification](https://github.com/microsoft/cheriot-sail/tree/main/archdoc), including

- To query or test capabilities: cgetaddr, cgetbase, cgethigh, cgetlen, cgetperm, cgettag, cgettop, cgettype, ctestsubset, csetequalexact, csub, csethigh
- To modify or derive capabilities: auicgp, auipcc, candperm, ccleartag, cincaddr, cincaddrimm, cmove, cram, crrl, csetaddr, csetbounds, csetboundsexact, csetboundsimm, cseal, cunseal
- To load/store capabilities from memory: clc, csc
- To control the program flow: cjal, cjalr
- To access special capability registers (SCR): cspecialrw

Certain compressed instructions are also extended for capabilities, for example c.incaddr4cspn, c.incaddr16csp, c.jal, c.jalr. Also the RV64 c.ld and c.sd instructions are reused for c.clc and c.csc instructions

## Register file

cheriot-ibex contains a register file implementation (cheri_regfile.sv) which extends a configurable number of the general purpose registers into CherIoT capabilities.

## Load-store unit

cheriot-ibex extends its data bus to 33-bit, where the MSB 1-bit is used as a valid tag to differentiate between capabilities and normal integer data. The load-store unit is modified to support atomic capability load and store transactions according to the CherIoT ISA specification.

## Configuration and status registers

Per CherIoT specification, the following SCR's are implemented,
- MTCC (address 28), which replaces mtvec
- MTDC (address 29)
- MScratchC (address 30)
- MEPCC (address 31), which replaces mepc.

In addition, the following SCR's are added for debug support
- DEPCC (address 24)
- DScratchC0 (address 25)
- DScratchC1 (address 26)
- ZTOPC (address 27)

The PC capability register (PCC) is also implemented as part of the CSR module.

## CherIoT memory access rule checking

cheriot-ibex performs capability-based memory access rule checking including
- data load/store accesses
- capability load/store accesses
- Instruction fetch (PCC-based)
- jump target calculation (cjal and cjalr)

Exceptions are generated in the case of access rule violations.

## Temporal memory safety support

The cheriot-ibex CLC implementation provides an optional load-filter feature. When enabled (cheri_tsafe_en_i == 1), the CLC instruction checks a memory area which contains shadow bits for the heap memory data at 8-byte granularity. The tag bit of the loaded capability is cleared if the corresponding shadow bits == 1 (revoked). The shadow bits are accessed through a dedicated memory interface (tsmap_*).

## Integrated hardware accelerators 

When configured accordingly, cheriot-ibex contains 2 internal tightly-coupled hardware accelerators,
- The background revocation engine (TBRE). The TBRE engine is controlled by a memory-mapped registor interface. When activated, the engine scans a designated memory region and check all capabilities stored in the region against the revocation shadowbits area. If a match is found, the tag of the capability is cleared and stored back to the same memory location.
- The stack zerorization engine (STKZ). The STKZ engine is controlled by the special capability register ZTOPC. The STKZ is used to zeroize a (stack) memory region as specified by ZTOPC, in order to facilitate context switching.
  
Note that the main CPU pipeline, TBRE and STKZ all use the load-store unit to access the data memory space. The priorities in the case of contention are,
1. CPU pipeline (highest priority)
2. STKZ
3. TBRE (lowest priority)

## Backward compatibility

cheriot-ibex provides a backward-compatibility mode which is enabled by setting the input cheri_pmode_i = 0. In this mode, all CHERIoT features are disabled. The cheriot-ibex core is logically equivalent to the non-CHERIoT ibex core and runs unmodified RV32IMC binaries.

## Design configuration parameters

cheriot-ibex design added the following configuration parameters,

| Parameter | Description |
| ----------- | ----------- |
| CHERIoTEn  | Master enable of CHERIoT features. <br /> 0: disabes CHERIoT functionality <br /> 1: Enables CHERIoT functionality. |
| DataWidth  | Data bus width for load/store interface. <br /> Use 32 when CHERIoTEn = 0, 33 when CHERIoTEn = 1. |
| CheriPPLBC | Configures pipelined implementation of load-barrier CLC. <br />  0: non-pipelined implementation <br />  1: pipelined implementation (better performance but needs a separate memory read interface).|
| CheriSBND2 | Selects number of cycles taken by csetbounds* instructions. <br /> 0: csetbounds* takes 1 cycle. <br /> 1: csetbounds* takes 2 cycle (better fmax timing). |
| CheriTBRE | Configures the TBRE and STKZ. <br /> 0: Disables TBRE/STKZ. <br /> 1: Enables TBRE/STKZ.
| MemCapFmt | Selects the format used to store capabilities in memory. <br /> 0: use canonical memory capbility format. <br /> 1: use the alternative memory capability format (better memory access timing). |
|HeapBase|32-bit starting address of the system heap memory. <br /> only capabilities whose base pointing to an address in the heap space are subject to load-barrier checks during CLC.|
|TSMapSize|size of the shadow bits memory (in 32-bit words) used by the load-barrier operation. <br /> e.g., 1024 = 32k bits which covers 256kB heap memory. <br />This parameter is only used when CheriPPLSBC == 1.|
|TSMapBase|Starting address of the shadow bits memory <br /> This parameter is only used when CheriPPLSBC == 0.|
|TSMapTop|Ending address of the shadow bits memory <br /> This parameter is only used when CheriPPLSBC == 0.|


## Debug support

cheriot-ibex supports cheri-aware RISC-V debugging via JTAG interface. The debug module is published separately at (link). General-purpose capability registers and SCR's can both be accessed via the JTAG interface. SBA accesses are supported as well.

To debug capability-related software issues, cheriot-ibex also provides a debug feature which when enabled, escalates tag-clearing events defined in the CherIoT ISA spec (e.g, csetbounds length violations) into exceptions. Writing a 0x1 to the CDBGCTRL SCR (address 27) to enable this feature.

## Timing, area and power

A PPA study conducted at Microsoft shows that cheriot-ibex is similar to the original ibex design in terms of area and power, however with moderate increase in area. 

cheriot-ibex (configured as 3-stage pipeline) has been synthesized successfully using Synopsys DC-topo at 250MHz using TSMC 28nm (28LP) libraries (ss 1.03v) and 550MHz using TSMC 5nm (N5) libraries (ss 0.6v). Timing is mostly limited by TCM read access time (which approaches 1.6ns in the N5 case). 

The design area is ~60k gate equivalents. Both dynamic and leakage power are shown as similar to the original ibex design.


## Build the design for simulation and emulation
See [README-CHERI.md](https://github.com/microsoft/cheriot-ibex/blob/main/README-CHERI.md) for the list of RTL files need to compile/simulate/synthesize the cheriot_ibex design.

In addition, [cheriot-safe](https://github.com/microsoft/cheriot-safe) provides an open-source FPGA platform for emulation and prototyping. 

