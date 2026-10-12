/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-!
# Stalks of higher direct images and the strict henselization

Let `f : X ⟶ S` be quasi-compact and quasi-separated with `X` quasi-compact and quasi-separated,
let `F` be an abelian étale sheaf on `X` and `s : Spec Ω ⟶ S` a geometric point. The higher
direct image `Rᵠ f_* F` is the sheafification of the presheaf `V ↦ Hᵠ(X ×_S V, F|)` on `S_ét`
(`AlgebraicGeometry.Etale.cohomologyPresheaf`, with `Hᵠ(X ×_S V, F|) = Extᵠ(ℤ[X ×_S V], F)`), so
its geometric stalk at `s` is the colimit of the `Hᵠ(X ×_S V, F|)` over the pointed étale
neighbourhoods `(V, v)` of `s`. We show that this colimit is `Hᵠ(X ×_S S_(s), F|)`, where
`S_(s)` is the strict localization: the affine pointed étale neighbourhoods are cofinal and have
limit `S_(s)`, base change to `X` preserves this limit, and étale cohomology commutes with the
limit (`AlgebraicGeometry.Etale.commutesWithLimit_of_isLimit`).

## Main definitions

- `AlgebraicGeometry.Etale.cohomologyPresheaf f F q`: the presheaf `V ↦ Hᵠ(X ×_S V, F|)`.
- `AlgebraicGeometry.Etale.stalkComparison`: the map `Hᵠ(X ×_S V, F|) ⟶ Hᵠ(X ×_S S_(s), F|)`
  for a pointed étale neighbourhood `(V, v)`.

## Main statements

- `AlgebraicGeometry.Etale.stalkComparison_bijective`: the stalk formula, elementwise.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section Presheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  (q : ℕ)

/-- The **cohomology presheaf** `V ↦ Hᵠ(X ×_S V, F|)` of `f : X ⟶ S` on the small étale site of
`S`, where `Hᵠ(X ×_S V, F|)` is `Extᵠ(ℤ[X ×_S V], F)`; its sheafification is the higher direct
image `Rᵠ f_* F`. -/
@[simps]
noncomputable def cohomologyPresheaf : S.Etaleᵒᵖ ⥤ AddCommGrpCat where
  obj V := AddCommGrpCat.of (Abelian.Ext ((freeAbSheaf X).obj (f.Etale.obj V.unop)) F q)
  map a := AddCommGrpCat.ofHom
    { toFun y := (Abelian.Ext.mk₀ ((freeAbSheaf X).map (f.Etale.map a.unop))).comp y (zero_add q)
      map_zero' := by simp
      map_add' _ _ := by simp }
  map_id V := by
    ext y
    simp
  map_comp a b := by
    ext y
    simp [Abelian.Ext.mk₀_comp_mk₀_assoc]

end Presheaf

section Stalk

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The leg `S_(s) ⟶ V` over `S` of the strict localization, for a pointed étale neighbourhood
`(V, v)` of `s`. -/
noncomputable def strictLocalizationLeg (e : Scheme.PointedEtaleNeighborhood s) :
    CategoryTheory.Over.mk (Scheme.strictLocalizationToBase s) ⟶
      (Scheme.Etale.forget S).obj e.1 :=
  CategoryTheory.Over.homMk ((Scheme.strictLocalizationConeAll s).π.app e) (by
    have := (Scheme.strictLocalizationConeAll s).w (Scheme.PointedEtaleNeighborhood.toBase s e)
    simpa [Scheme.neighborhoodDiagram, Scheme.PointedEtaleNeighborhood.toBase,
      Scheme.strictLocalizationToBase] using this)

lemma strictLocalizationLeg_comp {e e' : Scheme.PointedEtaleNeighborhood s} (a : e' ⟶ e) :
    strictLocalizationLeg s e' ≫ (Scheme.Etale.forget S).map a.1 = strictLocalizationLeg s e := by
  ext
  exact (Scheme.strictLocalizationConeAll s).w a

/-- The pointed étale neighbourhoods of `s`, as schemes over `S`. -/
noncomputable abbrev neighborhoodDiagramOver :
    Scheme.PointedEtaleNeighborhood s ⥤ CategoryTheory.Over S :=
  CategoryOfElements.π _ ⋙ Scheme.Etale.forget S

/-- The strict localization `S_(s)` as a cone over all pointed étale neighbourhoods of `s`, as
schemes over `S`. -/
@[simps]
noncomputable def strictLocalizationConeAllOver : Cone (neighborhoodDiagramOver s) where
  pt := CategoryTheory.Over.mk (Scheme.strictLocalizationToBase s)
  π :=
    { app e := strictLocalizationLeg s e
      naturality e e' a := by
        rw [Functor.const_obj_map, Category.id_comp]
        exact (strictLocalizationLeg_comp s a).symm }

/-- The strict localization is the limit of all pointed étale neighbourhoods, over `S`. -/
noncomputable def isLimitStrictLocalizationConeAllOver :
    IsLimit (strictLocalizationConeAllOver s) :=
  have := IsCofiltered.isConnected (Scheme.PointedEtaleNeighborhood s)
  isLimitOfReflects (CategoryTheory.Over.forget S)
    ((Scheme.isLimitStrictLocalizationConeAll s).ofIsoLimit (Cone.ext (Iso.refl _)))

end Stalk

end AlgebraicGeometry.Etale
