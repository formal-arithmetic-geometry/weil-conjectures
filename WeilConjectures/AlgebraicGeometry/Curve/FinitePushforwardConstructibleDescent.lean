/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveSubQuotient
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Finite.Stalk

/-!
# Constructibility descends from finite direct image on curves

Source: Stacks Project, Etale Cohomology, Tags 03QP (1), 095G and 09BH (2),
combined in the converse of Tag 095R in.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A torsion quotient of a constructible torsion middle term is constructible.
Source: Stacks Project, Proposition 09BH (2). -/
theorem CurveCoefficientPair.constructible_of_short_exact
    {k : Type u} [Field k] [IsAlgClosed k] (P : CurveCoefficientPair k)
    (Fmid K : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hK : P.C.IsTorsionAbelianSheaf K)
    (hmidT : P.C.IsTorsionAbelianSheaf Fmid)
    (hmid : (fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
      ({ C := P.C, toSpec := P.toSpec, isCurve := P.isCurve, F := Fmid,
         isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp hmidT) } : CurveCoefficientPair k))
    (alpha : K ⟶ Fmid) (beta : Fmid ⟶ P.F) (w : alpha ≫ beta = 0)
    (hshort : (ShortComplex.mk alpha beta w).ShortExact) :
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)) := by
  let Q : CurveCoefficientPair k :=
    { C := P.C, toSpec := P.toSpec, isCurve := P.isCurve, F := Fmid,
      isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp hmidT) }
  exact (CurveCoefficientPair.constructible_sub_quotient Q K P.F hK 
    ((Scheme.isTorsionAbelianSheaf_characterizations
      P.F).1.mpr P.isTorsion)
    alpha beta w hshort hmid).2

-- Keep the inherited compatibility binder; the counit construction does not need it.
set_option linter.unusedVariables false in
/-- The finite direct image supplies a torsion constructible middle term and a short exact
sequence ending in the original sheaf. Source: Stacks Project, Tags 03QP (1), 095G and 03PU. -/
theorem CurveCoefficientPair.finite_pushforward_data
    {k : Type u} [Field k] [IsAlgClosed k] (P : CurveCoefficientPair k)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsCurve g]
    (f : P.C ⟶ Y) [IsFinite f] (hf : f ≫ g = P.toSpec)
    (hT : Y.IsTorsionAbelianSheaf (Etale.lowerStar AddCommGrpCat.{u + 1} f |>.obj P.F))
    (hC : (fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
      ({ C := Y, toSpec := g, isCurve := inferInstance,
         F := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F, isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp hT) }
        : CurveCoefficientPair k)) :
    ∃ (Fmid K : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hmidT : P.C.IsTorsionAbelianSheaf Fmid)
      (_hK : P.C.IsTorsionAbelianSheaf K)
      (_hmid : (fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
        ({ C := P.C, toSpec := P.toSpec, isCurve := P.isCurve, F := Fmid,
           isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp hmidT) } : CurveCoefficientPair k))
      (alpha : K ⟶ Fmid) (beta : Fmid ⟶ P.F) (w : alpha ≫ beta = 0),
      (ShortComplex.mk alpha beta w).ShortExact := by
  classical
  let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
  let Fmid := (Etale.upperStar AddCommGrpCat.{u + 1} f).obj G
  let beta : Fmid ⟶ P.F :=
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app P.F
  have hmidT : P.C.IsTorsionAbelianSheaf Fmid :=
    (Scheme.isTorsionAbelianSheaf_characterizations Fmid).1.mpr
      (Etale.isTorsion_upperStar f
        ((Scheme.isTorsionAbelianSheaf_characterizations G).1.mp hT))
  have hmid : (fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
      ({ C := P.C, toSpec := P.toSpec, isCurve := P.isCurve, F := Fmid,
         isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp hmidT) } : CurveCoefficientPair k) :=
    Scheme.isConstructibleEtaleSheafOfSets_upperStar f G hC
  have hstalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ P.C) :
      Epi ((Scheme.pointSmallEtale s).sheafFiber.map beta) := by
    let D := fun t : Scheme.Hom.GeometricFiber f (s ≫ f) ↦
      (Scheme.pointSmallEtale t.1).sheafFiber.obj P.F
    have hrestrict : Epi (Etale.stalkRestrict AddCommGrpCat.{u + 1} f
        (s ≫ f) ⟨s, rfl⟩ P.F) := by
      have he : (Etale.stalkIsoPi AddCommGrpCat.{u + 1} f (s ≫ f) P.F).hom ≫
          CategoryTheory.Limits.Pi.π D ⟨s, rfl⟩ = _ :=
        CategoryTheory.Limits.Pi.lift_comp_π _ _
      rw [← he]
      infer_instance
    exact epi_of_epi_fac
      (Etale.stalkRestrict_eq_counit AddCommGrpCat.{u + 1} f s P.F).symm
  have : Epi beta := by
    let hpoints := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale P.C
    apply (hpoints.jointlyReflectEpimorphisms AddCommGrpCat.{u + 1}).epi_iff beta |>.mpr
    rintro ⟨-, ⟨x⟩⟩
    let e := (Scheme.pointSmallEtale (P.C.algClosurePoint x)).uliftSheafFiberIso.{u + 1}
      AddCommGrpCat.{u + 1}
    have := hstalk _ (P.C.algClosurePoint x)
    let Φ := Scheme.pointSmallEtale (P.C.algClosurePoint x)
    change Epi ((Φ.ulift.{u + 1}).sheafFiber.map beta)
    rw [← epi_comp_iff_of_isIso _ (e.hom.app P.F), e.hom.naturality]
    infer_instance
  let K := CategoryTheory.Limits.kernel beta
  have hK : P.C.IsTorsionAbelianSheaf K := by
    apply (Scheme.isTorsionAbelianSheaf_characterizations K).2.mpr
    intro Ω _ _ s
    let L := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
    have ht := (Scheme.isTorsionAbelianSheaf_characterizations Fmid).2.mp hmidT Ω s
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_shrink.{u, u, u + 1, u + 1} _
    have : CategoryTheory.Limits.PreservesFiniteLimits L := inferInstance
    have hm : Mono (L.map (CategoryTheory.Limits.kernel.ι beta)) := inferInstance
    intro x
    obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
      (ht ((L.map (CategoryTheory.Limits.kernel.ι beta)).hom x))
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective (L.map (CategoryTheory.Limits.kernel.ι beta))).mp hm
    simpa only [map_nsmul, map_zero] using hx
  exact ⟨Fmid, K, hmidT, hK, hmid, CategoryTheory.Limits.kernel.ι beta, beta,
    CategoryTheory.Limits.kernel.condition beta,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel beta) inferInstance inferInstance⟩

/-- Constructibility descends from a finite direct image of a torsion sheaf on a curve.
Source: a composition of Stacks Project, Tags 03QP (1), 095G and 09BH (2),
forming the converse of Tag 095R. -/
theorem CurveCoefficientPair.isConstructible_of_finite_pushforward
    {k : Type u} [Field k] [IsAlgClosed k] (P : CurveCoefficientPair k)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsCurve g]
    (f : P.C ⟶ Y) [IsFinite f] (hf : f ≫ g = P.toSpec)
    (hT : Y.IsTorsionAbelianSheaf (Etale.lowerStar AddCommGrpCat.{u + 1} f |>.obj P.F)) :
    ((fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
      ({ C := Y
         toSpec := g
         isCurve := inferInstance
         F := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
         isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp hT) } : CurveCoefficientPair k)) →
      (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)) := by
  intro hC
  obtain ⟨Fmid, K, hmidT, hK, hmid, alpha, beta, hw, hshort⟩ :=
    CurveCoefficientPair.finite_pushforward_data P g f hf hT hC
  exact CurveCoefficientPair.constructible_of_short_exact P Fmid K hK hmidT hmid
    alpha beta hw hshort

end AlgebraicGeometry
