import TwoControl.RossSelinger.Basic
import DyadicCyclotomic.Basic
import TwoControl.RossSelinger.ZomegaRingTheory
import TwoControl.RossSelinger.ZomegaNormSolvability
import TwoControl.RossSelinger.GridLemma
import TwoControl.RossSelinger.Grid
import MatrixCompletion.Completion
import TwoControl.RossSelinger.DiophantineCore
import TwoControl.RossSelinger.Diophantine
import TwoControl.RossSelinger.Selinger75
import TwoControl.RossSelinger.MANormalForm
import TwoControl.RossSelinger.Algorithm
import TwoControl.RossSelinger.Correctness
import TwoControl.RossSelinger.Optimality

/-!
Entry point for the conditional Ross-Selinger compiler leg.

This leg is **independent of Lemma 12's universality proof**: Lemma 12 is now
proved through `Lemma12/Universal/BoykinDensity.lean` and does not import any
file under `RossSelinger/`.

The near-term targets here are:

* `Correctness.rossSelingerSearch_sound_if_returns` — soundness when the
  algorithm returns;
* `Optimality.rossSelingerOracle_optimal_if_returns` — `T`-count optimality
  of the factoring-oracle variant when it returns.

`Grid.boundedGridCandidatesAtLevel` is the current finite candidate-generation
kernel: it scans a concrete integer coordinate box at a fixed denominator
level and proves both emitted-candidate soundness and bounded completeness.
The remaining geometric work is to provide bounds large enough for full
fixed-level completeness.

`CircuitTranslation`, `DistanceBridge`, and the older `Oracle` compatibility
layer remain optional adapters and are intentionally not imported here.

Unconditional termination is *not* claimed.
-/
