/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.AlgebraicGeometry.FiniteCoverKillsConstantCohomology
import WeilConjectures.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Killing one finite-pushforward component by a finite-cover unit

## References

* Stacks Project, Tags 09ZE and 09ZD.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private lemma cohomology_map_injective_of_isIso
    {S : Scheme.{u}} {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) [IsIso a] (q : ℕ) : Function.Injective (Sheaf.H.map a q) := by
  intro x y h
  have h' := congrArg (Sheaf.H.map (inv a) q) h
  simpa only [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply] using h'

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- A class with coefficients in a finite pushforward of a finite constant module dies
under the pushforward of the unit of a finite surjective cover of the source.

(Stacks, Tag 09ZE, Tag 0959, Tag 09ZD) -/
theorem exists_finite_cover_pushforward_unit_closed_cohomology_eq_zero
    {X Y Z : Scheme.{u}} [IsAffine X] (f : Y ⟶ X) [IsFinite f]
    [LocallyOfFinitePresentation f] (i : Z ⟶ X) [IsClosedImmersion i]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℕ) (hq : 0 < q)
    (x : Sheaf.H (((i)^*[AddCommGrpCat.{u + 1}]).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) q) :
    ∃ (Y' : Scheme.{u}) (π : Y' ⟶ Y),
      IsFinite π ∧ Surjective π ∧ LocallyOfFinitePresentation π ∧
        Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
            ((lowerStar (ModuleCat.{u + 1} Λ) f).map
              ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app
                ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))))
          q x = 0 := by
  classical
  let UY := sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let UX := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let E := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let G := UY.obj E
  let iY := pullback.fst f i
  let fZ := pullback.snd f i
  let sq := IsPullback.of_hasPullback f i
  let β := (baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app G
  let GZ := ((iY)^*[AddCommGrpCat.{u + 1}]).obj G
  let ξ := Sheaf.H.map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} fZ).counit.app GZ) q
      (cohomologyMap fZ _ q (Sheaf.H.map β q x))
  let MAb := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfSize.{u + 1, u + 1} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} Λ
  have : Y.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification Y.smallEtaleTopology U
  let e : GZ ≅ (constantSheaf (pullback f i).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj MAb :=
    ((iY)^*[AddCommGrpCat.{u + 1}]).mapIso
      ((constantCommuteCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app M) ≪≫
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} iY).app MAb
  have : IsAffine Y := isAffine_of_isAffineHom f
  obtain ⟨Y', π, hπ, hsurj, hπfp, hkill⟩ :=
    exists_isFinite_surjective_constant_cohomology_eq_zero iY MAb q hq
      (Sheaf.H.map e.hom q ξ)
  let : IsFinite π := hπ
  let : Surjective π := hsurj
  let πZ := pullback.snd π iY
  let iY' := pullback.fst π iY
  let fZ' := πZ ≫ fZ
  let sqπ := IsPullback.of_hasPullback π iY
  let sq' := sqπ.paste_vert sq
  have hk : cohomologyMap πZ GZ q ξ = 0 := by
    have h₁ : cohomologyMap πZ _ q (Sheaf.H.map e.hom q ξ) = 0 := by
      apply cohomology_map_injective_of_isIso
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} πZ).hom.app MAb) q
      simpa only [map_zero] using hkill
    have h₂ := cohomologyMap_map πZ q e.hom ξ
    rw [h₁] at h₂
    apply cohomology_map_injective_of_isIso
      (((πZ)^*[AddCommGrpCat.{u + 1}]).map e.hom) q
    simpa only [map_zero] using h₂.symm
  let η := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} π).unit.app G
  let t := (lowerStar AddCommGrpCat.{u + 1} f).map η
  let c := (lowerStarComp AddCommGrpCat.{u + 1} π f).hom.app
    (((π)^*[AddCommGrpCat.{u + 1}]).obj G)
  have ht : Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map (t ≫ c)) q x = 0 := by
    let G' := ((π)^*[AddCommGrpCat.{u + 1}]).obj G
    let β' := (baseChangeMap AddCommGrpCat.{u + 1} sq'.toCommSq).app G'
    have : IsIso β' := by
      have := isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq'
      infer_instance
    apply cohomology_map_injective_of_isIso β' q
    apply (bijective_edgeMap_of_isFinite fZ'
      (((iY')^*[AddCommGrpCat.{u + 1}]).obj G') q).1
    have hcompat := DFunLike.congr_fun
      (cohomology_baseChange_unit_edge_compatibility f π i iY fZ iY' fZ'
        πZ sq sq' sqπ.toCommSq rfl G q) x
    change Sheaf.H.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} fZ').counit.app
        (((iY')^*[AddCommGrpCat.{u + 1}]).obj G')) q
      (cohomologyMap fZ' _ q
        (Sheaf.H.map β' q
          (Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map (t ≫ c)) q x))) =
      Sheaf.H.map ((squareUpperStarIso AddCommGrpCat.{u + 1} sqπ.toCommSq).hom.app G) q
        (cohomologyMap πZ GZ q ξ) at hcompat
    simpa only [map_zero, hk] using hcompat
  have ht₀ : Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map t) q x = 0 := by
    apply cohomology_map_injective_of_isIso (((i)^*[AddCommGrpCat.{u + 1}]).map c) q
    rw [map_zero]
    convert ht using 1
    simp only [Functor.map_comp, Sheaf.H.map_comp_apply]
    rfl
  refine ⟨Y', π, hπ, hsurj, hπfp, ?_⟩
  let ηM := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app E
  let a := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} π).homEquiv
    G ((sheafCompose Y'.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (((π)^*[ModuleCat.{u + 1} Λ]).obj E))).symm (UY.map ηM)
  have ha : η ≫ (lowerStar AddCommGrpCat.{u + 1} π).map a = UY.map ηM := by
    exact ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} π).homEquiv _ _)
      |>.apply_symm_apply _
  have hm : UX.map ((lowerStar (ModuleCat.{u + 1} Λ) f).map ηM) =
      t ≫ (lowerStar AddCommGrpCat.{u + 1} f).map
        ((lowerStar AddCommGrpCat.{u + 1} π).map a) := by
    change (lowerStar AddCommGrpCat.{u + 1} f).map (UY.map ηM) = _
    rw [← ha, Functor.map_comp]
  change Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map
    (UX.map ((lowerStar (ModuleCat.{u + 1} Λ) f).map ηM))) q x = 0
  have hfinal := congrArg
    (Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map
      ((lowerStar AddCommGrpCat.{u + 1} f).map
        ((lowerStar AddCommGrpCat.{u + 1} π).map a))) q) ht₀
  rw [hm, Functor.map_comp, Sheaf.H.map_comp_apply]
  convert hfinal using 1; simp only [map_zero]

end AlgebraicGeometry.Etale
