## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.towerAdjunctionRealization` in
`Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization`, preserving its full statement,
including its universes and the specified unit/counit and coefficient identity formulas.
`termwiseAdjunction` is unchanged.

The proof uses the existing strict-tower exactness, constant-ring composition and
K-injective-resolution APIs. Naturality comes from the already proved arbitrary-ring
`Scheme.proEtaleConstantInverseImageMap_naturality`. The identity coefficient calculation
is proved by sheafification uniqueness followed by the conjugation unit identity.
The derived-functor and adjunction clauses use the actual existing constructions.

Private, completely proved component/assembly helpers reproduce the existing explicit
diagram-module equivalence with a small index and a site in the larger universe. Its
coefficient ring is an explicit sheaf, not a witness selected from an existence theorem.
The assembled equivalence is composed with the actual AsSmall module-site equivalence.
A free-diagram separating-family argument proves Grothendieck abelianness directly.
The DAG proof now records this argument and the dependencies it actually uses.

Validation: complete module compiled remotely without warnings in 22.6 seconds before
removing the unused public DiagramSiteRealization import. The final pruned module compiled remotely without warnings in 34.2 seconds;
the import-pruning checker also passed. A textual check confirms that existing
signatures and docstrings are verbatim; there are no new public declarations.
All private definitions have actual data and complete proofs. The index includes level
zero (representing positive level one); empty opens and the zero ring are admitted by
the same exactness and universal-property proofs. There are no boundedness or finite-ring
assumptions.

The removed public proof-only import is documented in
`coord/changes/W3-strict-tower-realization-imports.md`. No target definition changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.StrictTower.towerAdjunctionRealization`
(node `lem-cbc-tower-adjunction-realization`).

Proved 1 of 1 original sorries; added 0; split off 0; remaining 0 in the delivered module.
This is a proof from existing declarations, not a decomposition. Transitive dependencies
can still contain existing holes; their proof obligations are not claimed closed here.

## No longer needed

Removed imports:

- `public import Sheaf.CategoryTheory.DiagramSiteRealization`
- `import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `import Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `import Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`
- `import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro`
- `import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`
- `import Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `import Mathlib.Algebra.Homology.DerivedCategory.KInjective`

The following planned proof dependencies are not used directly by this proof:

- `lem-pur-proetale-constant-coefficient-comparison`
- `lem-weil-pbc-ringed-topoi-module-adjunction`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-diagram-site-realization`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-weil-pbc-kinjective-hom-derived`
- `def-pc-essentially-constant-ind-diagram`
- `def-pc-essentially-constant-pro-diagram`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-proetale-ringed-open-comparison`
- `lem-pur-site-restriction-module-adjunction-exact`

The strict-tower definitions already provide module exactness, K-injective resolutions,
constant-ring composition and normalized derived/open adjunctions. Thus their general
construction theorems need no separate reapplication. The full diagram-site realization
is replaced by the explicit vertical topology and a privately proved equivalence with the
required universes; its set-sheaf and evaluation clauses are unnecessary here. The direct
K-injective derivability API eliminates the essential-constancy/fraction-diagram detour.

This list describes dependencies pruned from this proof, not modules proved unreachable
from the entire project. In particular, definitions may still use some of them transitively.
All upstream source declarations remain intact. Obsolete tool_uses entries corresponding
to these unused dependencies are removed, preserving the remaining approval order.

## Where the brief, the DAG or earlier work was wrong

The general `exists_diagramSite_realization` API ties the universe of the index to the
universe of the site. It cannot directly instantiate its index with the actual small
`ℕᵒᵖ` used in the target statement at site universe `u+1`. The already generalized
`verticalDiagramSiteTopology` and its sheaf criterion support the necessary universes;
the private component/assembly construction supplies the missing equivalence without
changing an existing interface. The arbitrary-ring identity formula is genuinely the
specified `leftAdjointIdIso`, verified by the adjunction calculation.

The old eight-step plan redoes substantial theory already proved in the imported tower
operations. The shorter proof reuses those exact declarations. The unit's route is
preserved: all constant coefficient, tower, diagram-site, K-injective and normalized open
and derived clauses remain in the theorem, with their original types.

`lem-weil-pbc-profinite-coefficient-inverse-image` is used only through its proved
arbitrary-CommRingCat naturality helper, not its profinite-limit assertion.
`lem-weil-pbc-diagram-site-topology` supplies the generalized vertical topology criterion;
the module-equivalence node supplies the explicit component/assembly argument reproduced
with independent index universe. These are generic tools, with the same tower realization
step retained; no change to a unit statement or route is proposed.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
