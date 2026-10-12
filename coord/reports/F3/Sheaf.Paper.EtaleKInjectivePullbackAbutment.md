## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.etaleKInjective_pullback_abutment`
by a complete Lean proof from `AlgebraicGeometry.Etale.etaleKInjective_unit_leray`.
The latter is a new module `Sheaf.Paper.EtaleKInjectiveUnitLeray` stating only the
unit--Leray calculation on two K-injective complexes. It has no resolution
augmentations, no homotopy-over-augmentation hypothesis, and no cohomology degree.

The assigned module proves the remaining argument: form the unit--Leray natural
transformation, transport it along Q(ρ.map) by naturality, use exact inverse-image
factorization naturality, localize the specified homotopy hj, cancel Q(σ.map),
apply the homology functor, and cancel the canonical homology factorization
isomorphisms. All existing signatures and visibility are unchanged. No definitions
or other existing modules were adapted. The node's proof and proof dependencies
now describe these steps.

Deleted the previous attempt's sandbox-only bridge module and bridge node. They
restated the whole assigned theorem and do not belong in this delivery.

Both delivered modules compile without errors or linter warnings with lcompile.py.
The new node is a decomposition of the original node's unit--Leray calculation,
not an axiom-free proof of that calculation.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.etaleKInjective_pullback_abutment`
(node `lem-weil-pbc-kinjective-pullback-abutment`). No sorry remains in the assigned
module, and the proof combining the smaller lemma with resolution transport and
homology is complete.

Added one hole:
`AlgebraicGeometry.Etale.etaleKInjective_unit_leray`
(node `lem-weil-pbc-kinjective-unit-leray`), in
`lean/Sheaf/Paper/EtaleKInjectiveUnitLeray.lean`. Its body is exactly `:= by sorry`;
its docstring gives the source and the proof of the remaining calculation.

This is a decomposition: one hole closed and one strictly smaller hole added,
net zero holes. The assigned theorem still depends on sorry through that lemma.
No other holes were added. The previous sandbox's restatement hole was deleted,
not counted as a closed baseline hole.

## No longer needed

Removed these proof-only imports from the assigned module:

- `Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`.
- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.

Added only `import Sheaf.Paper.EtaleKInjectiveUnitLeray` for the new proof.
The two original public imports remain necessary for the original signature.
The new module's three public imports supply its statement's derived global
sections, derived adjunction, and K-injective comparison isomorphisms.

The proof no longer needs the nodes `lem-sp-kinjective-comparison-principle` or
`lem-weil-pbc-cohomology-pullback-derived-unit`. In particular, no bijective lifting
of morphisms is needed: hj already supplies the required comparison, and equality
under Q follows from Mathlib's `DerivedCategory.Q_map_eq_of_homotopy`.
No bounded-below comparison theorem is used. The node
`def-weil-pbc-cohomology-pullback` (whose recorded declaration is cohomologyMap)
is not a proof dependency of either delivered theorem.

The other removed imports expose definitions or generic tools still available
transitively through the necessary public imports; they are redundant direct
imports, not claims that those modules become globally unreachable. The
right-adjoint-preserves-K-injective node remains a dependency of the new core
calculation. No blueprint unit statement or realized step is bypassed:
`dag/units/sk-prop-h2.json` has empty realized lists, and this is a split below
that unit. Global reachability and pruning remain the maintainer's calculation.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox bridge was the original theorem under a new name, including
the same resolution choices, homotopy, w, degree, and conclusion. The rejection
as a restatement was correct. This delivery retains only the K-injective
unit--Leray calculation and proves the omitted augmentation/homotopy/homology
argument explicitly (roughly 65 lines of Lean).

The original DAG suggested using the bounded-below derived-unit theorem, but
ρ.complex and σ.complex are arbitrary K-injectives, not bounded-below choices.
The new lemma is unbounded and isolates the exact part not supplied by that
bounded-below theorem. No original statement was weakened or disputed.

Read the available local Stacks copies of derived.tex (lemma-K-injective and
lemma-adjoint-preserve-K-injectives) and cohomology.tex (lemma-functoriality,
equation-functorial-derived, and remark-explain-arrow). The cited formulas give
the adjoint-comparison and unit--Leray recipe; the unbounded computation uses
K-injectives and exact inverse image. The inherited source label
lemma-adjoint-preserves-K-injectives should be lemma-adjoint-preserve-K-injectives;
the new node uses the latter spelling.

## New nodes

`lem-weil-pbc-kinjective-unit-leray`, at
`dag/nodes/sec-curve-estimates/lem-weil-pbc-kinjective-unit-leray.json`, isolates
step 2 of the original plan on K-injectives, before resolution transport and
homology. It inherits the original chapter and unit. The statement was checked
on zero complexes/maps and on identity f: it reduces respectively to zero or
the ordinary derived comparison's naturality; it imposes no boundedness or
quasi-isomorphism on j. The K-injectivity assumptions are exactly those required
for the two rightDerivedFunctorObjQIso terms. Existence of w is a hypothesis;
no arbitrary witness is chosen and no definition contains sorry.

Searches: LeanFinder returned only ordinary injective-resolution comparisons;
Loogle found homologyFunctorFactors_hom_naturality, which is used in the
assigned proof; Mathlib/source grep found the generic derived unit and
composition APIs but no sectionwise unbounded étale calculation. LeanSearch was
attempted and returned Internal Server Error. Whole-DAG name/definition searches
and `tools/blueprint_refs.py search 'unit Leray'` found no matching blueprint
node (zero results). Existing derivedUnitLeray_id/comp concern coherence, not this
calculation; derivedUnit_classicalPullback_coherence and the existing global-germ
factorizations are bounded-below. No change record is needed: there is no
existing interface change or forced adaptation.

## Second reading by F3

1. **Interfaces and accidental changes.** I compared the assigned module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and proof-only imports differ. The added module contains one new theorem and no adaptations or definition changes. Verdict: pass.

2. **Proof and axioms.** I compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The assigned theorem has no `sorry`, and the only remaining `sorry` is the named split-off theorem `AlgebraicGeometry.Etale.etaleKInjective_unit_leray`, whose docstring and node record its source and proof. The proof uses only the derived-category transport, naturality, homotopy localization, and homology-factor cancellation shown in the source. Verdict: pass, with the split-off hole explicitly retained.

3. **Split-off statement.** I checked the new unit--Leray statement on zero complexes/maps and on identity inverse image: it reduces to the corresponding zero or ordinary derived comparison identities. It has no extra boundedness, augmentation, homotopy, or degree hypotheses, and its K-injective assumptions are exactly those required by the comparison isomorphisms. Searches recorded in the report found no existing declaration duplicating it. Verdict: true and strictly smaller than the assigned theorem.

4. **Pruning and route.** The proof follows the unit--Leray calculation, resolution transport, homotopy localization, and homology factorization route. It removes five proof-only imports and the corresponding obsolete proof dependencies; no removed declaration is used by the proof. The unit record has no realized statement or step to bypass. Verdict: pass.

5. **DAG agreement.** The assigned node proof and `proof_deps` match the Lean proof, and the new node has the required statement, source, proof, searches, Lean record, and chapter/unit metadata. Verdict: pass.

I changed only the assigned proof, its direct proof-only imports, the matching DAG proof metadata, and the strictly smaller split-off module/node. No statement, definition, or public import was changed.
