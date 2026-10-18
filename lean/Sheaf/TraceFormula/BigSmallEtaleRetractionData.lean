module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.Sites.GeometricMorphism

@[expose] public section

/-!
# Canonical big-to-small étale retraction data

Source: Stacks Project, Sites, Tags 00XR, 00XT, 00XU and Etale Cohomology Tag 0DDI
(blueprint: def-trf-big-small-etale-retraction-data).  The direct-image fields are
natural isomorphisms of functors, so the datum records the canonical restriction
maps rather than merely asserting equality of values for some arbitrary morphism.
-/


open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Data for the exact retraction from sheaves on the big étale site of a scheme `T`
to sheaves on its small étale site, induced by the inclusion
`Scheme.Etale.forget T : T.Etale ⥤ Over T`.

* `topos` is the geometric morphism `π_T : Sh(B_T) → Sh(T_Et)` of sheaves of sets, and
  `topos_direct` identifies its direct image with restriction along the inclusion,
  `(π_{T,*} G)(U/T) = G(U/T)`, naturally in `G`, `U` and the restriction maps.
* `morphism` is `π_T` on abelian sheaves, with `direct_restrict` the same identification
  of its direct image with restriction along the inclusion.
* The abelian direct image preserves finite limits and finite colimits (it is exact), and
  the abelian unit `F → π_{T,*} π_T^{-1} F` is an isomorphism for every small abelian
  sheaf `F`.

Since both direct images are pinned to restriction along the inclusion, the inverse images
are the canonical left adjoints (unique up to unique isomorphism), so these are the data
of the canonical `π_T`, not of an arbitrary geometric morphism.
Source: Stacks, Sites, Tags 00XR, 00XT, 00XU; Etale Cohomology, Tag 0DDI
(blueprint: def-trf-big-small-etale-retraction-data). -/
structure BigSmallEtaleRetractionData (T : Scheme.{u}) where
  topos :
    GeometricMorphism
      (Sheaf (Scheme.etaleTopology.over T) (Type (u + 1)))
      (Sheaf T.smallEtaleTopology (Type (u + 1)))
  topos_direct :
    topos.direct ⋙ sheafToPresheaf T.smallEtaleTopology (Type (u + 1)) ≅
      sheafToPresheaf (Scheme.etaleTopology.over T) (Type (u + 1)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (Scheme.Etale.forget T).op
  morphism :
    GeometricMorphism
      (Sheaf (Scheme.etaleTopology.over T) AddCommGrpCat.{u + 1})
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
  direct_restrict :
    morphism.direct ⋙ sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      sheafToPresheaf (Scheme.etaleTopology.over T) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ _).obj (Scheme.Etale.forget T).op
  direct_preserves_finite_limits : PreservesFiniteLimits morphism.direct
  direct_preserves_finite_colimits : PreservesFiniteColimits morphism.direct
  unit_is_iso : ∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
    IsIso (morphism.adj.unit.app F)

end AlgebraicGeometry
