## What changed

Proved `RingTheory.exists_inv_mem_jacobson_of_tensor_surjective` in
`Sheaf.RingTheory.JacobsonDenominatorFunctionField`, with its signature and existing
public imports unchanged. The proof realizes all three paragraphs of Stacks Tag 09N5:
normalization and conductor descent, localization at finitely many maximal ideals,
and induction on the finite family of DVR valuations. The Stacks proof was read at
https://stacks.math.columbia.edu/tag/09N5 because the local literature source is absent.

Private, completely proved helpers transport tensor surjectivity to overrings,
descend Jacobson membership along an integral injection, prove the single-DVR base
case by tensor induction, combine finitely many valuation inequalities, and recover
DVR maximal-ideal witnesses. The normalized multiplicative valuations avoid subring
identifications and additive-log coercions. The integer algebra structures on the
localizations are fixed explicitly so they agree with the tensor products over ℤ.
The parent node's proof and proof dependencies now describe this implementation.

Added proof imports: `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`,
`Mathlib.Algebra.Order.Archimedean.Basic`, `Mathlib.RingTheory.Ideal.GoingUp`,
`Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`, and
`Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset`.
No existing statement, definition, or public visibility changed.

## Proved and sorry left

Closed the one original hole:
`RingTheory.exists_inv_mem_jacobson_of_tensor_surjective`
(node `lem-sc-jacobson-denominator-function-field`).
There are no sorries left in the delivered module, and no holes were added or split off.
All six new private helpers are fully proved. This is a proof from the existing
normalization/conductor and localization interfaces, not a decomposition into new holes.

The proof still uses the existing, undelivered holed declarations
`semilocal_dim_one_conductor` (node `lem-sc-semilocal-dim-one-conductor`) and
`MaximalSpectrum.semilocal_dedekind_dvr_reduction`
(node `lem-sc-semilocal-dedekind-dvr-reduction`). Consequently the main theorem's
transitive axioms still include their `sorryAx`; this delivery does not claim final
axiom closure of the target. The valuation helpers themselves use only Mathlib.

## No longer needed

Removed the proof import `Sheaf.RingTheory.ExistsNegativeValuationOfTensorSurjective`.
Its node `lem-sc-dvr-tensor-surjective-negative-valuation` is no longer a dependency
of this proof: the single-DVR contradiction is proved directly for arbitrary ring
models by tensor induction. Its proof-only dependency module
`Sheaf.RingTheory.DVRValuationRingCharacterization` and node
`lem-sc-dvr-valuation-ring-characterization` are also unnecessary on this branch.
Whether another target still reaches these modules is for the maintainer's queue.

The arithmetic node `lem-sc-dvr-valuation-arithmetic` stays, through direct Mathlib
valuation laws. The Mathlib leaf `lem-sc-dvr-nonnegative-valuation-in-ring` stays,
through `IsDiscreteValuationRing.exists_lift_of_le_one`. The conductor, DVR reduction,
and integral lying-over nodes stay. No unit-level statement or route was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The old DVR base-case interface uses subrings of
one universe, whereas this item allows independent universes and arbitrary abstract
ring models. A direct tensor-induction proof is shorter than transporting all these
models to subrings, and eliminates that dependency without changing the statement.

Checked edge cases in the actual proof: an empty family returns a power of 1;
zero values in the Archimedean-power helper are handled separately; the valuation
induction chooses a positive common exponent; the final conductor exponent is a
positive finite product, including the empty product. Duplicate valuation rings and
arbitrary universes are allowed throughout. The sigma-indexed DVR family is finite
from the conductor theorem's finite maximal spectra. No arbitrary object is defined
by choosing data from an unproved existence statement.

LeanSearch was unavailable (HTTP 500); LeanFinder and Loogle returned no exact
common-denominator theorem. The library search found only the planned subring base
case. Every retained helper was compiled, and the final file compiles without warnings.

## Second reading by Q3

1. **Interface and accidental changes:** Compared the delivered module with the
   repository version. The public theorem signature and all existing declarations are
   byte-for-byte unchanged; only proof-only imports, private helpers, and the theorem
   proof differ. Verdict: pass.
2. **Proof validity:** Compiled the module with `lcompile.py`; it has no errors,
   warnings, `sorry`, axioms, unsafe declarations, or hollow definitions. A scratch
   `#print axioms` reports only the expected `sorryAx` from the two still-open imported
   declarations, together with `propext`, `Classical.choice`, and `Quot.sound`. Verdict:
   pass.
3. **Statements and split-offs:** No new public statements or split-off holes were
   added. The six private helpers are fully proved and have no DAG nodes required.
   The existing target statement remains unchanged and its edge cases (empty finite
   family, zero valuation, and repeated valuation rings) are handled. Verdict: pass.
4. **Pruning and route:** The removed negative-valuation proof import is unused by the
   direct tensor-induction base case; the retained imports and `proof_deps` match the
   Lean proof. The conductor and semilocal-to-DVR unit steps remain in the route.
   Verdict: pass.
5. **DAG agreement:** The node proof, dependencies, and origin describe the direct
   tensor-induction and finite valuation proof actually written, including the
   Mathlib valuation and lying-over facts. Verdict: pass.

Changed after this reading: no Lean declarations or statements; only this review
section was added to the report.
