## What changed

Proved `AlgebraicGeometry.ProEtale.sp_coefficient_towers_abelian` in
`Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`. All helper declarations are private
and proved. The existing public statements, coefficient constructions, abelian axioms
and abelian instance are retained.

Constructed the explicit sectionwise normalized equivalence between the recorded
varying-coefficient module presheaves and `StrictRingSystem`. Applied the existing
`systemLevelLeftExtensionTheory` for Grothendieck abelianness, evaluation coproducts,
and normalized scalar/tensor models. Constructed ordinary reduction by adjunction
and derived reduction by fully faithful precomposition with derived localization.
Proved identity and composition using one source-level K-flat resolution and the
existing normalized comparison formulas. Private normalization lemmas and local
irreducibility settings prevent repeated expansion of the explicit equivalence.
Additivity follows from preservation of binary products and zero morphisms.
Preservation and record assembly are proved with an abstract equivalence before
applying them to the concrete tower equivalence.
Updated the node's proof, proof dependencies and proof origin to match this route.

Validation: the complete module compiled through `lcompile.py` with the normal
options and the original generated structure API (59.2 seconds). The source contains
no `sorry`, and all five preceding public declarations remain verbatim.

The conservative command-level preflight requested a scope record. Added
`coord/changes/J1-coefficient-towers-abelian-proof-environment.md`, documenting
the local attributes, private helper scopes, and all 85 unchanged downstream consumers.
No consumer adaptation or public definition repair is included.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.sp_coefficient_towers_abelian`
(node `det-sp-coefficient-towers-abelian`). No holes added; no split-off statements;
no `sorry` remains in the delivered module. The previously proved
`sp_coefficient_towers_abelian_axioms` is retained and is not counted as a newly closed
hole. Existing imported theorems, including `systemLevelLeftExtensionTheory`, retain
their own proof obligations; this delivery does not claim to close those.

## No longer needed

The direct argument no longer needs the diagram-site realization theorem, the
ringed-site Grothendieck theorem, or the module-sheaf colimits-forgetful theorem:
the normalized equivalence is constructed directly and the existing system-level
theory supplies Grothendieck abelianness and evaluation coproducts. It also no longer
needs ringed-topos K-flat pullback, the resolving-class left-derived existence theorem,
or change-of-rings preservation of K-flatness. Reduction descends using localization
full faithfulness, and coherence uses only one source-level resolution and the
stipulated scalar comparison formulas. The separate exact-functor-derived theorem
is replaced by Mathlib's exact-functor localization API. The node's direct dependencies
are updated accordingly.

Removed the following private proof imports (public imports are preserved):

- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Sites.Limits`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`

Retained the vertical-topology and independent-coefficient K-flat resolution imports;
added the independent-coefficient tensor/flatness comparison and Mathlib's
colimits-from-coproducts-and-coequalizers construction.

Removed obsolete top-level `tool_uses` approvals:
`lem-weil-pbc-diagram-site-realization`,
`lem-pur-ringed-site-grothendieck-abelian`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-ringed-topos-kflat-pullback`,
`lem-pur-left-derived-from-kflat-class`, and
`lem-pur-kflat-change-of-rings`.

No modules are withdrawn. Some of these results remain dependencies of the existing
system-level theory or other library modules; this is direct-route pruning, not a
claim that those modules have left the targets' transitive closure.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The earlier plan asked for simultaneous K-flat
resolutions of all tower levels, which is unnecessary for this statement: the
comparison is already natural on every complex, and a single source-level resolution
suffices to establish each coherence equality. Equal indices, level zero (the first
positive coefficient level), and composed transitions are covered by the explicit
identity and composition proofs; no surjectivity, boundedness, or flatness hypothesis
on towers is added.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
