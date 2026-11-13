/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Derived Nakayama from the first reduction

The canonical reduction functor at index n is reduction modulo pi^(n+1).
The four conjuncts express vanishing, closure under cones, closure under all integer
shifts, and detection of isomorphisms by the first reduction.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The sectionwise uniformizer formula determines its module endomorphism uniquely. -/
private theorem uniformizer_end_unique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (d d' : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) a).down s =
        Padic.coefficientExtensionUniformizer l E * a.down s)
    (hd' : ∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d'.asHom.hom.hom.app S) a).down s =
        Padic.coefficientExtensionUniformizer l E * a.down s) : d = d' := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  apply End.ext
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext
  ext a
  apply ULift.ext
  apply ContinuousMap.ext
  intro s
  exact (hd S a s).trans (hd' S a s).symm

/-- Derived complete complexes vanish if their first reduction vanishes, are closed under
cones and shifts, and have isomorphisms detected by their first reduction. There is no
boundedness assumption, no restriction on `X`, and no invertibility hypothesis on `l` on `X`. -/
theorem derived_nakayama_first_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K →
      IsZero ((AdicCompletion.derivedReduction l E X 0).obj K) →
        (∀ n : ℕ, IsZero ((AdicCompletion.derivedReduction l E X n).obj K)) ∧ IsZero K) ∧
    (∀ T : Triangle (DerivedCategory (AdicCompletion.Modules l E X)),
      T ∈ distTriang (DerivedCategory (AdicCompletion.Modules l E X)) →
      IsDerivedComplete l E X T.obj₁ → IsDerivedComplete l E X T.obj₂ →
        IsDerivedComplete l E X T.obj₃) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K → ∀ r : ℤ, IsDerivedComplete l E X (K⟦r⟧)) ∧
    (∀ (K L : DerivedCategory (AdicCompletion.Modules l E X)) (f : K ⟶ L),
      IsDerivedComplete l E X K → IsDerivedComplete l E X L →
      IsIso ((AdicCompletion.derivedReduction l E X 0).map f) → IsIso f) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  obtain ⟨data, hdata, a, F, c, κ, sF, hF, ha, hc, hψ, hcomplete, hshift, htriangle⟩ :=
    CompletionTriangle.completion_triangle_comparison l E X
  have cones : ∀ T : Triangle (DerivedCategory (AdicCompletion.Modules l E X)),
      T ∈ distTriang (DerivedCategory (AdicCompletion.Modules l E X)) →
      IsDerivedComplete l E X T.obj₁ → IsDerivedComplete l E X T.obj₂ →
      IsDerivedComplete l E X T.obj₃ := by
    intro T hT h₁ h₂
    obtain ⟨hFT, γ, hγ₁, hγ₂, hγ₃⟩ := htriangle T hT
    apply (hcomplete _).2
    rw [← hγ₃]
    apply isIso₃_of_isIso₁₂ γ hT hFT
    · rw [hγ₁]
      exact (hcomplete _).1 h₁
    · rw [hγ₂]
      exact (hcomplete _).1 h₂
  have shifts : ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K → ∀ r : ℤ,
      IsDerivedComplete l E X (K⟦r⟧) := by
    intro K hK r
    have : IsIso (c.app K) := (hcomplete _).1 hK
    apply (hcomplete _).2
    have : IsIso (c.app (K⟦r⟧) ≫
        (Functor.commShiftIso (self := sF) F r).hom.app K) := by
      rw [hshift]
      infer_instance
    exact IsIso.of_isIso_comp_right (c.app (K⟦r⟧))
      ((Functor.commShiftIso (self := sF) F r).hom.app K)
  obtain ⟨d, hd, D, hobj, χ, t, j, sD, sR, κR, Φ,
    hχ, hmap, ht, hj, hcompat, hqi, hexact, hrest⟩ :=
    PrincipalReduction.principal_reduction_cone_calculus l E X
  obtain ⟨d', hd', r, hr, i, q, hi, hq, hres⟩ :=
    DerivedNakayama.derived_nakayama_resolution l E
  have hdd : d' = d := uniformizer_end_unique l E d' d hd' hd
  subst d'
  have levelIso (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ) :
      Nonempty (AdicCompletion.integralLevel l E X K n ≅
        (DerivedNakayama.reductionFunctor l E X (n + 1)).obj K) := by
    let M := DerivedCategory.Q.objPreimage K
    let e : DerivedCategory.Q.obj M ≅ K := DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨ec⟩ := (hres X (n + 1) (by omega)).2.1
    refine ⟨((PrincipalReduction.reductionFunctor l E X n).mapIso e).symm ≪≫
      ((κR n).app M).symm ≪≫ ?_ ≪≫
      (DerivedNakayama.reductionFunctor l E X (n + 1)).mapIso e⟩
    exact eqToIso (congrArg DerivedCategory.Q.obj (hobj n M)) ≪≫ (ec.app M).symm
  have vanishing (K : DerivedCategory (AdicCompletion.Modules l E X))
      (hK : IsDerivedComplete l E X K)
      (h₀ : IsZero (AdicCompletion.integralLevel l E X K 0)) : IsZero K := by
    have hlevels : ∀ n : ℕ,
        IsZero ((DerivedNakayama.reductionFunctor l E X (n + 1)).obj K) := by
      intro n
      induction n with
      | zero =>
        obtain ⟨e⟩ := levelIso K 0
        exact e.isZero_iff.1 h₀
      | succ n hn =>
        obtain ⟨δ, hδ⟩ := (hres X (n + 1) (by omega)).2.2 1 (by omega) (by omega) K
        exact Triangle.isZero₂_of_isZero₁₃ _ hδ
          ((levelIso K 0).some.isZero_iff.1 h₀) hn
    have hB (n : ℕ) : IsZero (AdicCompletion.integralLevel l E X K n) :=
      (levelIso K n).some.isZero_iff.2 (hlevels n)
    let J := Discrete.functor (AdicCompletion.integralLevel l E X K)
    have hJ : IsZero J := (Functor.isZero_iff J).2 (fun n ↦ hB n.as)
    let cone : Cone J := Cone.mk 0 0
    let : HasLimit J := ⟨⟨cone, IsLimit.ofIsZero cone hJ (isZero_zero _)⟩⟩
    have hprod : IsZero (∏ᶜ (AdicCompletion.integralLevel l E X K)) :=
      (limit.isLimit J).isZero_pt hJ
    obtain ⟨P, hP, ⟨e⟩, hPi⟩ := hK
    obtain ⟨p, δ, htri, hunit⟩ :=
      AdicCompletion.roos_isDerivedLimit l E X K P hP e
    have hz : IsZero (DerivedCategory.Q.obj (AdicCompletion.roos l E X P)) :=
      Triangle.isZero₁_of_isZero₂₃ _ htri hprod hprod
    have : IsIso (AdicCompletion.completionMap l E X K P e) := by
      dsimp only [AdicCompletion.completionMap]
      infer_instance
    exact hz.of_iso (asIso (AdicCompletion.completionMap l E X K P e))
  refine ⟨?_, cones, shifts, ?_⟩
  · intro K hK h₀
    have hz := vanishing K hK ((AdicCompletion.restrict l E X 0).map_isZero h₀)
    refine ⟨?_, hz⟩
    intro n
    have : (AdicCompletion.derivedReduction l E X n).IsLeftAdjoint :=
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E X n)).isLeftAdjoint
    exact (AdicCompletion.derivedReduction l E X n).map_isZero hz
  · intro K L f hK hL hf
    obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle f
    let T := Triangle.mk f g h
    have hC : IsDerivedComplete l E X C := cones T hT hK hL
    let R := PrincipalReduction.reductionFunctor l E X 0
    let : R.CommShift ℤ := sR 0
    have : R.IsTriangulated := (hexact 0).2
    have : IsIso (R.map f) := by
      change IsIso ((AdicCompletion.restrict l E X 0).map
        ((AdicCompletion.derivedReduction l E X 0).map f))
      infer_instance
    have hC₀ : IsZero (R.obj C) :=
      Triangle.isZero₃_of_isIso₁ _ (R.map_distinguished T hT)
        (show IsIso (R.map f) from inferInstance)
    exact (T.isZero₃_iff_isIso₁ hT).1 (vanishing C hC hC₀)

end AlgebraicGeometry.ProEtale
