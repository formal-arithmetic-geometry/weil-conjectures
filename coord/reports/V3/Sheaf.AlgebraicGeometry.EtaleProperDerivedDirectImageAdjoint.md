## What changed

Proved `AlgebraicGeometry.Etale.isLeftAdjoint_proper_rightDerivedLowerStar` with its
original signature, universes and visibility. No existing definition or statement changes.
The proof uses the source library's finite-coefficient unbounded proper projection formula,
then coproduct preservation and the existing Grothendieck-derived Brown adjoint theorem.
It imposes no Noetherian, quasi-compactness, boundedness or global dimension hypothesis.

Three new modules contain complete proofs, rather than postponed obligations:

- `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`: constructs coproducts in a derived
  category with K-injective resolutions by representing objects by complexes and using
  termwise coproducts. It reuses the already-proved generic private chain-map/homotopy
  helpers in `DerivedModuleDirectSums` through `import all`.
- `Sheaf.CategoryTheory.CoproductsOfCopowers`: proves coproduct preservation from preservation
  of constant-family coproducts. Each family is a retract of the constant family on its sum;
  its comparison map is therefore an arrow retract of an invertible comparison.
- `Sheaf.CategoryTheory.ProjectionFormulaCoproducts`: applies an invertible bifunctor
  projection formula to sums of tensor units, obtains preservation of all copowers, then
  applies the retract theorem. Only source zero morphisms are required; functors need not
  preserve zero morphisms or be additive. Empty index sets are included.

Proof imports added: the two new modules used directly, the source triangulated
right-derived-functor API, and the source proper projection formula. The existing
BrownRightAdjoint proof import is retained.
The pre-existing public import is preserved. Second reading narrows two new-module
zero-morphism imports, removes a redundant new-module import, and makes the termwise
complex-limits import proof-only. It adds an exact DAG attachment for the existing
finite-coefficient proper projection-formula source theorem. The item node's proof, proof dependencies
and proof origin now describe this route. The unit `sk-prop-sf-cbc` has no realized statement
or proof-step nodes; no unit statement or step is bypassed or changed.

Validation: all four delivered Lean files compile cleanly via `lcompile.py --all`.
The original item compiles in approximately four seconds. An initial formulation as a
family of tensor-functor isomorphisms caused expensive kernel comparisons of concrete
functor structures. Passing the existing projection formula as a bifunctor isomorphism
avoids those comparisons; no definition change, time-limit increase or file-size workaround
was needed. Axiom probes show that all three new public theorems use only `propext`,
`Classical.choice`, and `Quot.sound`; the item additionally uses `sorryAx` through
existing imported obligations, as explained below.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.isLeftAdjoint_proper_rightDerivedLowerStar`
(`lem-etale-proper-derived-direct-image-adjoint`). No `sorry` remains in the item.

Added 0 holes. The new theorems are fully proved:
`CategoryTheory.derived_hasCoproducts`,
`CategoryTheory.preservesCoproducts_of_preservesCopowers`, and
`CategoryTheory.preservesCoproducts_of_projectionFormula`.
All private helpers in the delivery are proved. This is a proof from existing statements,
not a decomposition into new holed statements.

The item still depends on existing obligations outside this delivery, in particular
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`
in `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`, the finite-ring
specialization of `lem-kun-0f0g`. Thus closing this item does not assert that its entire
transitive axiom closure is already free of existing `sorry` proofs. Brown infrastructure
and sheaf/derived constructions are likewise reused as they stand. No imported obligation
was disguised as a new theorem with the same statement.

## No longer needed

Removed the original proof import
`Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`.
Also removed the original proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.

In the new modules, second reading also removed `Mathlib.CategoryTheory.Preadditive.Basic`
from `CoproductsOfCopowers` and `ProjectionFormulaCoproducts`, replacing it by the narrower
`Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`. Removed the redundant
`Mathlib.CategoryTheory.Limits.HasLimits` from `ProjectionFormulaCoproducts`. The retained
`Mathlib.Algebra.Homology.HomologicalComplexLimits` in `GrothendieckDerivedCoproducts` is
now a plain proof import.

The target no longer directly needs these original proof-plan nodes:

- `cor-weil-pbc-geometric-fiber-finite`;
- `thm-sc-finite-type-torsion-cd`;
- `lem-weil-pbc-cohomology-filtered-colimit`, module
  `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`;
- `lemma-weil-pbc-geometric-stalk-conservative`, source module
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`;
- `lem-exc-direct-image-coproducts`.

The affine-local finite-amplitude gluing route is unnecessary here. Some geometric tools
above remain needed by the existing projection-formula node or elsewhere in the targets'
closure; this report does not claim that they can all be deleted globally. The Brown node
is retained. No new proof imports are unused.

## Where the brief, the DAG or earlier work was wrong

The original plan is longer than necessary. The source library already states the
unbounded proper projection formula for finite coefficients and arbitrary schemes.
An elementary copower/retract argument converts it to exactly the coproduct preservation
needed by Brown. Original plan nodes without Lean attachments therefore do not obstruct
this delivery and were not duplicated.

The source's existing proper projection-formula hole is genuine work still to do.
This delivery uses that named statement as stage 3 requires; it does not claim to prove it.
The existing declaration docstring retains the original finite-amplitude proof in words;
a proof-body comment and the updated DAG identify the shorter implemented route.

## New nodes

`lem-grothendieck-derived-has-coproducts`:
`lean/Sheaf/CategoryTheory/GrothendieckDerivedCoproducts.lean`,
`CategoryTheory.derived_hasCoproducts`. Source: Stacks Tag 07D9, Lemma 19.13.4,
coproduct clauses (1)-(2). The proof only needs the explicit K-injective resolution and
underlying coproduct hypotheses, so it is stated at that generality. The K-injective
localization Hom bijection is the existing Mathlib-matched node
`lem-weil-pbc-kinjective-hom-derived`. No arbitrary data is chosen from a holed existence
statement: representatives and resolutions use the existing APIs, and the colimit object
is the actual termwise coproduct with a proved universal property.

`lem-coproducts-of-copowers`:
`lean/Sheaf/CategoryTheory/CoproductsOfCopowers.lean`,
`CategoryTheory.preservesCoproducts_of_preservesCopowers`. Source: the elementary arrow-retract
construction written by V3 and formalized using Mathlib coproduct comparisons and stability
of isomorphisms under retracts. Tested also conceptually for empty families and for functors
that do not preserve zero; neither case requires a missing hypothesis.

`lem-projection-formula-preserves-coproducts`:
`lean/Sheaf/CategoryTheory/ProjectionFormulaCoproducts.lean`,
`CategoryTheory.preservesCoproducts_of_projectionFormula`. Source: the categorical
projection-formula argument written by V3, followed by the preceding retract theorem.
The stated isomorphism is natural in both variables and matches the project's actual
projection formula without expensive concrete functor comparisons.

The three proved nodes have completed LeanFinder, Loogle and grep searches; LeanSearch returned
Internal Server Error and is recorded as unavailable. Blueprint searches for copowers,
derived coproducts/direct sums and projection formula found no duplicate of these abstract
statements. Geometric projection-formula nodes are reused, not restated. Those three new
nodes are already proved, have no remaining task, and are reached from the updated item.
No change record or forced adaptation is needed, because existing interfaces are unchanged.


`lem-etale-proper-projection-formula-finite` (added by the second reader): an exact
attachment to the existing source theorem
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite` in
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`. It records the finite-ring
specialization of Stacks Tag 0F0G used by the Lean proof. The general torsion-ring node
`lem-kun-0f0g` has no Lean attachment and is not itself the declaration used; the item now
names this exact finite case instead. The new record has `lean.existing: true`, because
it reuses an existing source declaration and adds no Lean statement or hole. The source
statement is still open, as already recorded under `## Proved and sorry left`.

## Second reading by V3

1. **Existing interfaces: pass.** Diffed every delivered module against the repository.
   The sole existing theorem's signature, universes, visibility and docstring are byte
   for byte unchanged; its body replaces the original `sorry`. The other three modules
   are new. No definitions, target statements or modules held by other groups changed.
2. **Proof and axioms: pass.** Compiled all four files with `lcompile.py --all`, cleanly,
   including after the import repairs. Searched the delivered Lean for `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern` and kernel-check bypasses: none occurs.
   A fresh scratch axiom probe shows only `propext`, `Classical.choice`, `Quot.sound` for
   the three new public theorems. The item additionally shows `sorryAx` from the existing
   imported obligations already listed above. The colimit is the actual termwise
   coproduct; the proof chooses representatives and resolutions through existing APIs,
   and introduces no data definition from an arbitrary unproved existence theorem.
3. **New statements: pass.** No new split-off `sorry` statement exists. Read the three
   categorical proofs and their DAG statements in full. Tested the empty family,
   singleton family, zero object/ring, arbitrary indexing universes, and absence of
   zero-preservation for the functor. Retraction identities use functoriality only.
   K-injective Hom computation supplies exactly existence and equality modulo homotopy.
   Independent LeanFinder, Loogle and grep searches used different queries (localization
   of complexes, pointed-category constant diagrams, tensor projection isomorphisms).
   Hits provide supporting APIs and specialized module/sheaf cases, not an exact theorem.
   Checked Stacks [07D9](https://stacks.math.columbia.edu/tag/07D9) and
   [0F0G](https://stacks.math.columbia.edu/tag/0F0G) directly against the claimed sources.
4. **Route and pruning: pass after import repairs.** The proof uses the available proper
   projection formula, copower retract reduction, and the existing Brown theorem. The
   unit `sk-prop-sf-cbc` has empty `steps` and empty `realized` entries; no prescribed
   realized unit step is bypassed. Compared the old `proof_deps` against the new proof:
   every discarded node is listed in `## No longer needed`, and Brown is retained.
   Changed proof-only `HomologicalComplexLimits` from public to plain import. Replaced
   `Preadditive.Basic` in both elementary categorical modules by the narrower public
   `Limits.Shapes.ZeroMorphisms`, which supplies their signature's zero-morphism class.
   Removed redundant public `Limits.HasLimits` from `ProjectionFormulaCoproducts`.
5. **DAG agreement: pass after repair.** The original item's Lean interface record is
   unchanged. Verified the three proved new nodes' signatures against Lean and checked
   that `proof_deps` is the union of step uses. Repaired the proper-projection dependency:
   `lem-kun-0f0g` states a general torsion-ring theorem without a Lean declaration;
   the actual proof invokes its finite-coefficient source specialization. Added
   `lem-etale-proper-projection-formula-finite` with an exact existing-source attachment,
   source proof and searches, then pointed the item's proof step and `proof_deps` to it.
   This adds a DAG record of an existing open theorem, not a new proof hole or a
   restatement of the adjoint theorem. The unchanged original docstring describes the
   longer former proof plan; the body comment and node describe the implemented route.

Second reading changed only imports in the new modules and the exact source-theorem DAG
attachment described above. No proof body or existing signature needed repair. Closed
one original hole, added zero holes; the three new categorical theorems remain proved.
