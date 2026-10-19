## Worker report

The module `lean/Sheaf/Paper/SitePointReconstructionSets.lean` states the set-valued
site-point reconstruction theorem from Stacks 00YA(2), 00YB, and 00YC.  It defines
`CategoryTheory.sitePointFunctor`, the pointed-object category
`CategoryTheory.sitePointNeighbourhood`, the section diagram
`CategoryTheory.sitePointSectionDiagram`, and the Yoneda/sheafification map
`CategoryTheory.sitePointSectionHom`.  These are actual constructions; the only
postponed proof is the theorem `CategoryTheory.site_point_reconstruction_sets`.

The theorem renders each clause of the node as follows.

* The small site is `C : Type u` with `[Category.{v} C]`, its covering structure is
  `J : Precoverage C` with `hJ : J.IsSiteForCoverings`, and finite limits are
  `[HasFiniteLimits C]`.  The sheafification instance is explicit as
  `[HasWeakSheafify J.toGrothendieck (Type v)]`, and the geometric morphism is
  `p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v))`.
* `u(U)=p⁻¹(h_U^#)` is `sitePointFunctor J p`; the first conjunct is
  `PreservesFiniteLimits (sitePointFunctor J p)`.
* For every index type `I : Type (max u v)`, object family `Ui`, arrows `f`, and
  covering `Presieve.ofArrows Ui f ∈ J U`, the next conjunct says every
  `x : u(U)` is `u(f i) y` for some `i` and `y : u(Ui i)`.  This includes an empty
  cover (then the conclusion forces the covered value to be empty), as required by
  the source.
* `sitePointNeighbourhood J p` is the Mathlib category of elements of `u`; the
  third conjunct is `IsCofiltered` (the carrier is a Type in the chosen small
  universe, so this is the small cofiltered category of the statement).
* For each set sheaf `F`, and each available Type colimit instance, the theorem
  supplies a cocone `c` over `sitePointSectionDiagram J p F`, an isomorphism
  `e : c.pt ≅ p.inverse.obj F`, and bijectivity of the canonical map
  `colimit.desc ... c ≫ e.hom`.  Its generator equation is
  `e.hom (c.ι.app (op ⟨U,a⟩) s) = p.inverse.map (sitePointSectionHom J F s) a`.
  By `yonedaEquiv`, a section `s : F(U)` is exactly a map `t : h_U^# ⟶ F`, so
  this is precisely the node's displayed `(U,a,t) ↦ p⁻¹(t)(a)` formula.
* The final conjunct gives naturality in `F`: for every sheaf map `α : F ⟶ G`,
  `sitePointSectionHom J G ((Sheaf.homEquiv α).app (op U) s)` equals
  `sitePointSectionHom J F s ≫ α`.  Thus the displayed bijection is natural in
  the sheaf variable.

Dependency declarations used are: `CategoryTheory.Precoverage.IsSiteForCoverings`
from `Sheaf.CategoryTheory.SiteCoveringAxioms`; the size convention
`def-weil-size-convention` is metatheoretic and has no Lean declaration;
`CategoryTheory.GeometricMorphism` from `Sheaf.CategoryTheory.Sites.GeometricMorphism`;
`CategoryTheory.presheafToSheaf`, `CategoryTheory.sheafificationAdjunction`, and
`CategoryTheory.yonedaEquiv` from Mathlib; `CategoryTheory.Limits.colimit` and
`CategoryTheory.Limits.IsFiltered`/`IsCofiltered` from Mathlib; the recorded
`CategoryTheory.sheafification_sections_local` (module
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`); and the
recorded Mathlib `CategoryTheory.yonedaEquiv`.  The latter two are proof-plan
imports conceptually; the statement itself uses only the Mathlib and site
constructions listed above.

Edge cases checked: the empty covering is included by the `∀ I` binder; the
terminal and empty site objects are not excluded by the finite-limit assumptions;
`I` is in `Type (max u v)` so the index is in the site size bound; a one-object
site and identity covering reduce to the identity pointed-object case; and the
formula is stated for every set sheaf, including the initial and terminal sheaves.
No extra base, coefficient, characteristic, or universe equality hypothesis was
introduced.

Existing-declaration searches were made before writing the module:

* `msearch.py ... leanfinder "The inverse image of a geometric morphism from sets to sheaves is a continuous left exact functor and recovers the point"` returned only intrinsic Mathlib `Point`/sheaf-adjunction results, with no reconstruction theorem.
* `msearch.py ... loogle "Point, presheafToSheafCompSheafFiber"` returned the intrinsic
  `CategoryTheory.GrothendieckTopology.Point` fibre declarations, which start with a
  given site point and do not state this abstract geometric-morphism theorem.
* `msearch.py ... grep "ofGeometric|point.site.topos|presheafToSheaf"` over Mathlib
  found only `Sites/Point` and skyscraper declarations; `rg` over the project found
  no declaration of this reconstruction statement.
* A repository/DAG search for `lem-trf-site-point-reconstruction-sets`, `N_u`, and
  the 00YA canonical comparison found no existing Lean declaration.  The recorded
  Mathlib `yonedaEquiv` is the exact Yoneda component used by `sitePointSectionHom`.

There is no `STATEMENT-DISPUTED` flag and no node fault.

## Second reading by N0

I reread the returned node, its Stacks source places, the complete module, and every
recorded statement dependency.  The finite-limit conjunct, cover-by-cover joint
surjectivity, pointed-object category, cofilteredness, cocone colimit map, generator
formula, and sheaf naturality each have a direct Lean counterpart listed above.  The
empty-cover and identity cases remain included.  I corrected the returned delivery's
missing module and lean record and left all non-`lean` node fields unchanged.  No
mismatch remains.

## Maintainer review fix (2026-10-18)

The fourth conjunct previously assumed `∀ [HasColimit (sitePointSectionDiagram J p F)]`.
The node asserts the colimit exists and the canonical map is a bijection, with no such
hypothesis. In `Type v` that instance is automatic only when the site's objects lie in
`Type u` with `u ≤ v`. For the étale-type sites this is used on (objects in a larger
universe than the morphisms and sheaves), the instance amounts to `Small.{v}` of the
quotient, which is part of what the theorem proves. Without the instance the clause said
nothing. The clause now reads
`∃ (c : Cocone _) (e : c.pt ≅ p.inverse.obj F), Nonempty (IsColimit c) ∧ (generator formula)`.
So the colimit exists in `Type v`, and the canonical map `e.hom`, with
`(U,a,s) ↦ p⁻¹(s̃)(a)`, is a bijection (an isomorphism of types). No other clause changed.
The record now lists the helper declarations `sitePointFunctor`, `sitePointNeighbourhood`,
`sitePointSectionDiagram` and `sitePointSectionHom` in `lean.declarations`.
