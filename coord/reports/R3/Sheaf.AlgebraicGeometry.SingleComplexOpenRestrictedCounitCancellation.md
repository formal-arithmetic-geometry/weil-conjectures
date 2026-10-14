## What changed

Replaced the proof of
`AlgebraicGeometry.singleComplexOpen_restricted_counit_cancellation` with the
existing node's cancellation argument. A proved private helper precomposes the
homotopy restriction equation with the inverse source comparison, postcomposes
with the inverse tensor comparison and the restricted homotopy counit, and uses
naturality of the target restriction comparison. The final normalization expands
the restricted coefficient, removes its mapped identity, and uses functoriality.
The public theorem's statement and visibility are unchanged. Scoped options
retain its original unused `F₀` and `a` let bindings without warnings and provide
an elaboration budget for comparing the pinned localization factors.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.singleComplexOpen_restricted_counit_cancellation`
(node `lem-pc-k3-open-restricted-counit-cancellation`).
Added no holes and split off no statements. The private categorical cancellation
helper is proved. No `sorry` remains in the delivered module.

The proof uses the existing
`AlgebraicGeometry.open_pinned_counit_homotopy_restriction`, as the DAG prescribes;
it makes no claim to remove holes reachable through existing imported modules.

## No longer needed

None. The proof uses the sole planned proof dependency
`lem-pc-open-pinned-counit-homotopy-restriction`, from
`Sheaf.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction`.
The three public imports provide declarations appearing in the unchanged
signature, including its pinned-adjunction let binding. No nodes or modules
from the original route are bypassed. The unit record
`sk-thm-picard-semicon` does not realize this node as its statement or a step.

## Where the brief, the DAG or earlier work was wrong

None. The existing proof plan suffices. LeanFinder returned generic commutative
square and natural-isomorphism lemmas; Loogle located `Iso.hom_inv_id_app`, and
Mathlib search located `mapDerivedCategoryFactorsh` in
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. Library search also
found the analogous inverse cancellation in
`SingleComplexOpenTermwiseCounitCompatibility`. The implementation follows the
item's own plan rather than importing that more specialized theorem.

## Second reading by R3

1. **Unchanged interface — pass.** Compared the sole delivered module with the
   repository using `diff`; independently compared the complete public theorem
   signature byte for byte. Its statement, visibility, docstring and imports are
   unchanged. The additions are a private proved helper, scoped elaboration/linter
   options, and the replacement proof. There are no definition changes, change
   records, forced adaptations or other delivered modules.
2. **Proof and axioms — pass.** The module compiles cleanly through `lcompile.py`
   (44.2 seconds). A scratch copy with `#print axioms` also compiles (47.4 seconds):
   `singleComplexOpen_restricted_counit_cancellation` uses only `propext`,
   `Classical.choice` and `Quot.sound`; `cancel_restricted_counit` uses only
   `Quot.sound`. No `sorry` or prohibited declaration occurs in this module, and
   no data construction was added. All lines meet the 100-column limit.
3. **Split statements — pass, none.** No new public statement or hole is split
   off. The private helper is a proved categorical equality: precompose the
   supplied equality with `a.inv`, postcompose with `t.inv` and `v`, cancel the
   inverse pairs, and substitute the supplied naturality square. It has no
   nonempty, nonzero or flatness premise, so zero complexes and empty opens
   introduce no exception.
4. **Route and pruning — pass.** Read the actual dependency theorem and the
   pinned comparisons. The argument specializes the existing homotopy restriction
   equation, uses restriction-factorization naturality, and normalizes mapped
   identities and composites. Checked Mathlib's `Iso.inv_comp_eq`,
   `Iso.comp_inv_eq` and inverse cancellation lemmas, and the analogous helper in
   `SingleComplexOpenTermwiseCounitCompatibility`; these provide the generic
   cancellation already performed here, rather than a shorter theorem for the
   pinned equation. Each of the three public imports supplies names explicitly
   used by the unchanged signature; the plain import supplies the proof's planned
   restriction theorem. Nothing in the old `proof_deps` is unused. The unit
   `sk-thm-picard-semicon` has empty `realized.statement` and step lists; no unit
   route is bypassed or changed.
5. **DAG agreement — pass.** The existing node
   `lem-pc-k3-open-restricted-counit-cancellation` already describes precisely
   these cancellations and naturality, and its sole proof dependency is exactly
   the theorem applied. Its source and `proof_origin` remain appropriate. No
   node edits or new nodes are needed.

Second reading changed only this report: no Lean repair was necessary. One
original named hole is closed, no holes are added, and no modules are pruned.
