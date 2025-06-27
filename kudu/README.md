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
cheriot-kudu is 32-bit RISC-V microcontroller currently under development at Microsoft. Feature highlights include
 - 5 stage pipeline
 - in-order, dual-issue 
 - RV32IMC 
 - CHERIoT extension (same as cheriot-ibex)
 - Backward compatibility mode (same as cheriot-ibex)

See the following block diagram for an overview of cheriot-kudu hardwared design.
<br><br>

![image](https://github.com/user-attachments/assets/d8337308-39fc-4907-abe5-26536c4ff03e)
<br>
## Build the design for simulation and emulation
- For VCS simulation, see the instructions in sim/ directory.

In addition, [cheriot-safe](https://github.com/microsoft/cheriot-safe) provides an open-source FPGA platform for emulation and prototyping, which is on the branch "kudu". 

