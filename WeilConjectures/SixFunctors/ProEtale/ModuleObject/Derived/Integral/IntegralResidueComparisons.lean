/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueProjectionNormalization
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable

/-! # Perfect integral residue coefficient comparisons

## References

- Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.5.9(3).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueComparisons
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Perfect residue change admits coherent pull comparisons whose direct-image mates
are invertible on the unbounded ambient derived categories. -/
theorem integralResidue_comparisons
    (hPerfect : ∀ T : Scheme.{u},
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))))
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ c : IntegralResiduePullComparisons.{u} ℓ E,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso (c.push f) := by
  obtain ⟨c, hc⟩ := integralResidue_projection_normalization ℓ E hTensor
  refine ⟨c, ?_⟩
  intro X Y f
  obtain ⟨m, hm⟩ := hc f
  let := m
  have component (K : residueExchangeDerived (integralCoeff ℓ E) X) :
      IsIso ((c.push f).app K) := by
    obtain ⟨s, e, h⟩ := hm K
    let t := (c.restrictPushIso f).app ((residueExchangeReduction ℓ E X).obj K) ≪≫
      (residueExchangeLowerStar (integralCoeff ℓ E) f).mapIso e
    obtain ⟨b⟩ := DerivedCategory.nonempty_braidedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y))
    let := b
    have hp :=
      Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable
        (residueExchangeAdjunction (integralCoeff ℓ E) f)
        (Functor.OplaxMonoidal.δNatTrans
          (residueExchangeUpperStar (integralCoeff ℓ E) f))
        (fun _ _ ↦ rfl) K (hPerfect Y)
    let R : residueExchangeDerived
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y ⥤
        residueExchangeDerived (integralCoeff ℓ E) Y :=
      (Mod.comap (C := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory
    have : IsIso (R.map ((c.push f).app K) ≫ t.hom) := by
      change R.map ((c.push f).app K) ≫ _ ≫ _ = _ at h
      simp only [t, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
      rw [h]
      infer_instance
    have : IsIso (R.map ((c.push f).app K)) :=
      IsIso.of_isIso_comp_right _ t.hom
    rw [DerivedCategory.isIso_iff]
    intro n
    let G : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y) ⥤
        Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) Y) :=
      Mod.comap (C := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) Y)
    have : IsIso (G.map ((DerivedCategory.homologyFunctor _ n).map
        ((c.push f).app K))) :=
      (NatIso.isIso_map_iff (G.mapDerivedCategoryHomologyFunctorIso n)
        ((c.push f).app K)).2 (by
          change IsIso ((DerivedCategory.homologyFunctor _ n).map
            (R.map ((c.push f).app K)))
          infer_instance)
    have : IsIso ((Mod.forget (condensedRingObj (integralCoeff ℓ E) Y)).map
        (G.map ((DerivedCategory.homologyFunctor _ n).map ((c.push f).app K)))) :=
      inferInstance
    change IsIso ((Mod.forget (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y)).map
        ((DerivedCategory.homologyFunctor _ n).map ((c.push f).app K))) at this
    exact isIso_of_reflects_iso _
      (Mod.forget (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y))
  exact NatIso.isIso_of_isIso_app (c.push f)

end AlgebraicGeometry.ProEtale.CondensedRing
