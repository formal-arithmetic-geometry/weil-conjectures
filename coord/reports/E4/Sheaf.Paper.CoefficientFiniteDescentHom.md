## What changed

Completed the Lean proof of `AlgebraicGeometry.ProEtale.coefficient_finite_descent_hom`
without changing its statement or any existing definition. The first two clauses use
adjunction bijectivity. A proved generic adjunction-naturality helper gives both
transition identities. The existing coefficient-complex colimit theorem gives the
colimit clause and additive functors preserve the common zero terms.

For finite representatives, apply the source library's now-proved
`constructibleCocone_homSurj` to C and D[r], then explicitly compare its full-subcategory
maps and shift isomorphisms with the specified coefficient maps. This existing proof
uses coefficient presentations and Ext continuity, retaining the blueprint unit route.
For eventual equality, pass to a common finite compositum and use faithfulness of
extension to the algebraic closure. A generic shifted-Hom composition lemma is proved
in this module. The canonical tensor-comparison associativity equation is obtained directly from
the second clause of the existing proved `condensedCoefficientCoherence` theorem.
The standing scheme supplies its Noetherian hypothesis. The unused speculative
associativity module and node from the interrupted attempt are omitted.

Updated the main node's proof and proof dependencies to the declarations actually used. All existing public signatures and definitions
remain identical. The proof-scope command additions are recorded in
`coord/changes/coefficient-finite-descent-hom-proof-scope.md`; no consumer adaptation is needed.

Validation: remote single-file compilation passed with no diagnostics. The resumed
required dry run on 2026-10-19 compiled the item and passed preflight (commit
`fc8281dec4`, review class CODEX). The delivery tool performs the same checks again
when pushing.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.coefficient_finite_descent_hom`
(node `det-lem-coefficient-finite-descent-hom`). There are zero holes in the item module,
zero new holes, and no split-offs: one original hole closed, net one hole removed.
The proof uses existing named library dependencies; this count does not assert that
their transitive axiom closures are already free of `sorry`.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.Paper.FiniteSubextensionsDirected`
- `Mathlib.CategoryTheory.Localization.Adjunction`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Sheaf.CategoryTheory.DirectedRingSheafModuleColimit`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.SheafTensor`
- `Sheaf.Paper.CompletedCondensedCoefficients`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.Paper.ConstructibleExtContinuity`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`

The following old direct proof dependencies are subsumed by the existing canonical
adjunction/finite-model/complex-colimit APIs and are no longer direct proof inputs:

- `def-sfb-derived-extend-comp-iso`
- `def-sfb-derived-extend-subfield`
- `def-sfb-derived-extend-to-qlbar`
- `def-sfb-modobj-relative-tensor`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `lem-sfb-adjunction-localization`
- `lem-sfb-bounded-representative`
- `lem-sfb-directed-ring-sheaf-module-colimit`
- `lem-sfb-qlbar-flat`
- `lem-sfb-subfield-flat`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-independent-sheaf-tensor-colimits`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `sk-def-sfb-bounded-constructible`
- `sk-def-sfb-change-of-scalars`
- `sk-def-sfb-dc-setting`
- `sk-def-sfb-derived-categories`
- `sk-def-sfb-sheaf-tensor`
- `sk-lem-constructible-ext-continuity`
- `sk-prop-sfb-qlbar-colimit-x`

The finite-field filteredness API remains available through the retained imports,
so `Sheaf.Paper.FiniteSubextensionsDirected` needs no separate direct import.
These are direct-edge and import removals, not claims that their modules leave the
targets' transitive import closure: the reused proofs still need the coefficient
colimit and Ext-continuity route. The existing proved coefficient-coherence API supplies the needed normalization. Obsolete top-level
`tool_uses` approvals for all six former direct tool dependencies were removed.
No complete module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The retained report described a decomposition that the retained Lean no longer uses.
The current library proves `condensedCoefficientCoherence`, including exactly the
algebraic-closure associativity equation needed here; the final proof uses that API.
An unused speculative associativity module and its unsubmitted node were removed
from this delivery. No library module is withdrawn and no node in the repository is
deleted. The proof-scope change record is the only change record in this delivery. The source library also provides complete finite-model Hom-surjectivity and
derived coefficient faithfulness proofs, so reproducing their theory is unnecessary.
No statement is disputed and no target, definition or existing public signature is
changed. No consumer adaptations are required; the proof-scope command additions are recorded in
`coord/changes/coefficient-finite-descent-hom-proof-scope.md`.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
