/-
Root of the formal development, in dependency order:
elementary layer (`Basic`, `Families`, `TheoremA`, `Ladder`,
`Elementary`) → finite
enumerations (`Enumerations`) → discrete-log bridges (`Bridges`) →
the R = 15 product-index bridge (`BridgeR15`) →
the reach ⟺ divisor-certificate bridge and composed corollary
(`DivisorBridge`) → Lemma S at R = 31 by certified dynamic
programming (`LemmaS31`) → Kneser's addition theorem (vendored,
`Kneser/`) and the unconditional support bound Theorem S
(`TheoremS`) → the kernel branch of the branch classification and
β-vacuity (`KernelBranch`) → the transfer of Theorem S to the
multiplicative divisor-class model, and Lemma S as its corollary at
every prime residual (`SupportBridge`). See lean/README.md.
-/
import ErdosStraus.Basic
import ErdosStraus.Families
import ErdosStraus.TheoremA
import ErdosStraus.Ladder
import ErdosStraus.Elementary
import ErdosStraus.Enumerations
import ErdosStraus.Bridges
import ErdosStraus.BridgeR15
import ErdosStraus.DivisorBridge
import ErdosStraus.LemmaS31
import ErdosStraus.TheoremS
import ErdosStraus.KernelBranch
import ErdosStraus.SupportBridge
