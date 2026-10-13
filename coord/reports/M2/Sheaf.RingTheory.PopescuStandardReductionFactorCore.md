## What changed

Proved `Algebra.exists_standardSmooth_reduction_factorization_core` in
`Sheaf.RingTheory.PopescuStandardReductionFactorCore`, with its original signature,
universes and public imports unchanged. Added proof-only imports of
`Mathlib.Algebra.Category.Ring.FinitePresentation`,
`Mathlib.RingTheory.FiniteStability`,
`Sheaf.RingTheory.PopescuCorrectionReduction`, and
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth`.

Three proved private helpers implement stage factorization, coefficientwise lifting
of a presentation of any finitely presented reduced algebra, and finite-sum membership
in the image ideal of any ring homomorphism. The repair replaces the two rejected
private statements with genuine generalizations in the same module:

- `Algebra.exists_lifted_presentation` needs no ind-presentation, standard smoothness,
  or finite presentation of A over R. It accepts an arbitrary finitely presented
  A/IA-algebra C, a ring map to Λ/IΛ, and compatibility with φ on A. It returns an
  actual algebra equivalence of the reduced polynomial quotient with C, together
  with the lifted evaluation identities. The public proof now constructs the reduced
  factor separately and transports its smoothness along this equivalence.
- `Algebra.exists_sum_of_mem_ringHom_map` accepts any ring homomorphism f, with no
  algebra structure, and expresses membership in I.map f. The public proof specializes
  it to algebraMap R Λ. This is a mathematical generalization, not a renamed duplicate. The stage-factorization
helper adapts the already proved ring-colimit argument in
`Algebra.exists_smooth_factorization_of_ind_smooth` while retaining standard smoothness.
It replaces the source by an isomorphic finite polynomial quotient in the base
universe before applying ULift. This handles `w` larger than `max u v` without
changing the ind-presentation universe.

The rest constructs the explicit corrected polynomial quotient from Tag 07CK and
its maps. Its reduction is standard smooth by the already proved correction
isomorphism and polynomial standard smoothness. Updated the item's DAG proof,
proof dependencies and proof origin to describe this argument.

Source read: Stacks Project Tag 07CK (lemma-lift-once), online at
https://stacks.math.columbia.edu/tag/07CK, from the initial reduced factorization
through the reduction identity for A-prime. The local cited smoothing.tex file is
absent from this machine. Only the construction preceding the use of square-zero
nilpotence is used here. Existing Mathlib finite-presentation APIs implement the
00QO/07C3 and 00F4 steps.

## Proved and sorry left

Closed: `Algebra.exists_standardSmooth_reduction_factorization_core`
(node `new-lem-popescu-reduction-factor-core`). One original hole closed; zero
holes added, zero statements split off. No `sorry` remains in the delivered module.
All three private helpers are fully proved.

Repair compilation succeeded without warnings. The delivery tool's declaration-wise
axiom probe passed. The exact `tools/import_prune_check.py` gate cited in the return
also passed against the repository original (exit 0, no findings). The dry run
passed all worker checks; a fresh second reading remains for the next worker.

The arbitrary source universe, empty generator/relation/correction lists, zero rings,
`I = 0`, and `I = top` are permitted throughout; the construction uses quotient
surjectivity and finite support, with no nonzero-ring or nonempty-list assumption.
No definition is added and all quotient data is constructed explicitly.

## No longer needed

No import was removed from the original module; its four public imports still serve
its statement. The second reading removed three redundant proof-only imports:
`Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`,
`Mathlib.RingTheory.TensorProduct.Quotient`, and
`Mathlib.RingTheory.Extension.Presentation.Basic`. The remaining imports already
provide their required declarations and instances. The combined removal compiles
cleanly. A first-worker trial import of
`Mathlib.CategoryTheory.Filtered.Connected` was also removed.

The original node had empty `proof_deps`, so no old dependency node is omitted
from this list. No globally pruned module is claimed.

This proof needs no imports of `Sheaf.RingTheory.PopescuReductionPresentationCore`,
`Sheaf.RingTheory.PopescuReductionPresentationFromFactor`,
`Sheaf.RingTheory.PopescuReductionPresentation`, or
`Sheaf.RingTheory.PopescuStandardReductionFactor`. In particular it does not use
`new-lem-popescu-reduction-factor`,
`new-lem-popescu-reduction-presentation-from-factor`,
`lem-weil-pbc-popescu-reduction-presentation`, or
`lem-weil-pbc-popescu-standard-reduction-factor` as proof dependencies.
These modules are still used elsewhere; this delivery claims no globally pruned
module. No blueprint-unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan conflates a standard smooth factor over R/I with
the required finitely presented algebra over R. Finite-presentation colimit
factorization supplies the former; lifting a presentation and adding correction
variables supplies the latter. Both steps are now actual Lean proofs.

The existing `exists_popescu_reduction_factor` uses this very core theorem, so
importing its module here creates a cycle. The existing
`exists_popescu_reduction_presentation_of_factor` is already marked
STATEMENT-DISPUTED because it lacks finite presentation of A, and its module also
imports the core transitively. Neither is used. The repair's generic presentation helper only needs finite presentation of C over
A/IA, which is established in the public proof from the unchanged finite-presentation
hypothesis on A. No existing public statement or definition was changed, and no
forced adaptation is needed.

The maintainer's return identified two word-for-word duplicate private helper
statements. Both are now generalized mathematically as described above. Importing
`Sheaf.RingTheory.PopescuReductionPresentation` or
`Sheaf.RingTheory.PopescuStandardReductionFactor` is impossible: the prescribed
`tools/import_direction.py may` check reports an import cycle for each. Moreover,
the existing finite-sum helper is private and cannot be reused by import. No change
to those downstream modules is forced or included. The earlier second reading was
of the superseded helper statements; this repair awaits a fresh second reading.


## Second reading by M2

1. I compared the delivered module with the repository version. The public theorem signature and existing declaration interfaces are unchanged byte for byte; only proof imports, private helpers, and the theorem proof differ. The DAG statement remains unchanged.
2. I compiled the module with `lcompile.py` and compiled a probe containing `#print axioms` for the public theorem and all three private helpers. The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`. The compiler emitted no warnings.
3. The three helper statements are genuine reductions rather than restatements: the presentation helper is for arbitrary finitely presented reduced algebras, the finite sum helper is for arbitrary ring homomorphisms, and the factorization helper handles arbitrary source universes. I searched the library and Mathlib; no existing declaration duplicates these statements. Empty finite sets, zero rings, and the ideals `0` and `top` are covered by the constructions.
4. Reading top-down, the proof uses the finite-presentation colimit factorization, finite-presentation restriction of scalars, and the existing correction-reduction equivalence. The unit route through the reduced standard-smooth stage is preserved. The proof-only imports are minimal: removing any of the four added imports causes a required declaration or instance to become unavailable. No old proof dependency is removed from the node, and no downstream module is adapted.
5. The DAG proof steps, dependencies, source, and proof origin agree with the Lean proof: reduced factorization, coefficientwise lifting, finite-sum correction, and reduction smoothness occur in that order. The target statement is unchanged and no new node or split-off theorem is introduced.

I changed only this report section after the first reading. The delivered Lean module and its DAG proof metadata required no further repair.
