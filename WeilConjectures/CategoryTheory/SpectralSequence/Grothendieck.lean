/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# The Grothendieck spectral sequence

Let `A ⥤ B ⥤ C` be left exact additive functors such that `F` sends injective objects of `A` to
`G`-acyclic objects of `B`. Then for every `X : A` there is a first quadrant cohomological
spectral sequence with `E₂`-page `R^p G (R^q F X)` abutting to `R^{p + q} (F ⋙ G) X`.

Convergence is expressed through `CategoryTheory.SpectralSequence.AbutsTo` of
`WeilConjectures/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`; the blueprint's
`sk-def-groth-ss` describes both the acyclicity hypothesis on the pair `(F, G)` and the image
filtration attached to a first quadrant double complex, and the second half of that subsection
is what `SpectralSequence.Abutment` records.

## Main definitions

- `CategoryTheory.Functor.IsAcyclicComposablePair`: a composable pair with acyclicity.

## Main statements

- `CategoryTheory.Functor.exists_grothendieckSpectralSequence`: the Grothendieck spectral
  sequence of a composable pair with acyclicity.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C]

/-- The pair of additive functors `A ⥤ B ⥤ C` is a *composable pair with acyclicity* if `F` sends
every injective object `I` of `A` to a `G`-acyclic object of `B`, that is, one at which all the
higher right derived functors `R^q G` for `q > 0` vanish. This is what makes an injective
resolution of `X : A` compute `R^n (F ⋙ G) X` after applying `F`, and hence what makes the
Grothendieck spectral sequence of `Functor.exists_grothendieckSpectralSequence` exist.

(blueprint: `sk-def-groth-ss`) -/
def Functor.IsAcyclicComposablePair (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] : Prop :=
  ∀ (I : A) [Injective I] (q : ℕ), 0 < q → IsZero ((G.rightDerived q).obj (F.obj I))

namespace Functor

variable (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The bounded below cochain complex `F(I)`, where `I` is the chosen injective resolution of
`X : A`. Its image in the derived category `D⁺(B)` is `RF(X)`. -/
noncomputable def rightDerivedPlusComplex (X : A) : CochainComplex.Plus B :=
  ⟨(F.mapHomologicalComplex _).obj (injectiveResolution X).cochainComplex, 0, inferInstance⟩

variable [HasDerivedCategory B] [HasDerivedCategory C]

/-- The spectral object in `C` whose spectral sequence is the Grothendieck spectral sequence of
`X : A`: to `a ≤ b` in `EInt` and `n : ℤ` it attaches `H^n(RG(τ_{≥ a} τ_{< b} RF(X)))`, where `τ`
denotes the truncations for the canonical t-structure on `D⁺(B)`. -/
noncomputable def grothendieckSpectralObject (X : A) : Abelian.SpectralObject C EInt :=
  ((DerivedCategory.Plus.TStructure.t.spectralObject
    (DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X))).mapTriangulatedFunctor
      G.rightDerivedFunctorPlus).mapHomologicalFunctor (DerivedCategory.Plus.homologyFunctor C 0)

instance (X : A) : DerivedCategory.Plus.TStructure.t.IsGE
    (DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X)) 0 := by
  refine (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).1 ?_
  have : (F.rightDerivedPlusComplex X).obj.IsStrictlyGE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex _).obj
      (injectiveResolution X).cochainComplex) 0)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((DerivedCategory.quotientCompQhIso B).app (F.rightDerivedPlusComplex X).obj).symm 0

instance (X : A) : (F.grothendieckSpectralObject G X).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    have := DerivedCategory.Plus.TStructure.t.isZero_eTruncLT_obj_obj
      (DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X)) 0 j hj
    change IsZero (((DerivedCategory.Plus.homologyFunctor C 0).shift n).obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
        ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj
          (DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X))))))
    exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ this))
  isZero₂ i j hij n hi := by
    have := DerivedCategory.Plus.TStructure.t.isGE_eTruncGE_obj_obj (n + 1) i (by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i => simp at hi ⊢; lia
      | top => simp) ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj
        (DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X)))
    exact G.isZero_homology_rightDerivedFunctorPlus_obj_of_isGE
      ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
        ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj
          (DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X)))) (n + 1) n (by lia)

/-- The Grothendieck spectral sequence of `X : A`, the first quadrant `E₂` spectral sequence of
the spectral object `Functor.grothendieckSpectralObject`. -/
noncomputable def grothendieckSpectralSequence (X : A) : E₂CohomologicalSpectralSequenceNat C :=
  (F.grothendieckSpectralObject G X).E₂SpectralSequenceNat

/-- The `E₂`-page of the Grothendieck spectral sequence is `E₂^{p,q} = R^p G (R^q F X)`. -/
theorem nonempty_grothendieckSpectralSequence_page_two_iso (X : A) (p q : ℕ) :
    Nonempty (((F.grothendieckSpectralSequence G X).page 2).X (p, q) ≅
      (G.rightDerived p).obj ((F.rightDerived q).obj X)) := by
  let K := DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X)
  let H₀ := DerivedCategory.Plus.homologyFunctor C 0
  let M := (DerivedCategory.Plus.homologyFunctor B q).obj K
  obtain ⟨e₁⟩ := DerivedCategory.Plus.nonempty_eTruncGE_eTruncLT_iso_singleFunctor K q
  let e₂ : M ≅ (F.rightDerived q).obj X :=
    DerivedCategory.Plus.homologyFunctorObjQIso _ q ≪≫
      ((injectiveResolution X).isoRightDerivedObjCochainComplex F q).symm
  obtain ⟨e₃⟩ := G.nonempty_homology_rightDerivedFunctorPlus_obj_singleFunctor_iso M p
  let e₄ := ((DerivedCategory.Plus.singleFunctors B).shiftIso (-(q : ℤ)) q 0 (by simp)).app M
  let e₅ := (G.rightDerivedFunctorPlus.commShiftIso (-(q : ℤ))).app
    ((DerivedCategory.Plus.singleFunctor B 0).obj M)
  let e₆ := (H₀.shiftIso (-(q : ℤ)) ((p + q : ℕ) : ℤ) p (by push_cast; ring)).app
    (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M))
  exact ⟨(F.grothendieckSpectralObject G X).E₂SpectralSequenceNatPageTwoXIso p q ≪≫
    (H₀.shift ((p + q : ℕ) : ℤ)).mapIso (G.rightDerivedFunctorPlus.mapIso (e₁ ≪≫ e₄.symm) ≪≫ e₅) ≪≫
    e₆ ≪≫ e₃ ≪≫ (G.rightDerived p).mapIso e₂⟩

/-- The Grothendieck spectral sequence of a composable pair with acyclicity abuts to
`R^n (F ⋙ G) X`. -/
theorem grothendieckSpectralSequence_abutsTo [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) :
    (F.grothendieckSpectralSequence G X).AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X) := by
  refine (F.grothendieckSpectralObject G X).abutsTo_E₂SpectralSequenceNat.of_nonempty_iso
    (fun n ↦ ?_)
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let K := DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X)
  have hK : (t.eTruncGE.obj ⊥).obj ((t.eTruncLT.obj ⊤).obj K) = K := by
    rw [t.eTruncGE_obj_bot, t.eTruncLT_obj_top]
    rfl
  have hL (k : ℤ) : G.rightAcyclic ((F.rightDerivedPlusComplex X).obj.X k) :=
    fun q ↦ hFG _ (q + 1) (by lia)
  obtain ⟨e⟩ := G.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso _ hL n
  exact ⟨(DerivedCategory.Plus.homologyFunctor C n).mapIso
    (G.rightDerivedFunctorPlus.mapIso (eqToIso hK)) ≪≫ e ≪≫
      ((injectiveResolution X).isoRightDerivedObjCochainComplex (F ⋙ G) n).symm⟩

end Functor

/-- **The Grothendieck spectral sequence.** If `F : A ⥤ B` and `G : B ⥤ C` are left exact
additive functors forming a composable pair with acyclicity

```
    A ───── F ─────▶ B ───── G ─────▶ C
     ╲                                ▲
      ╲───────────── F ⋙ G ──────────╱
```

then for every `X : A` there is a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ R^p G (R^q F X)` abutting to `R^{p + q} (F ⋙ G) X`.

For `A` the abelian sheaves on a site `X`, `F = f_*` and `G = h_*` along morphisms of sites
`X ⥤ Y ⥤ Z`, the acyclicity hypothesis holds because `f_*` is right adjoint to the exact functor
`f^{-1}` and hence preserves injectives, and the statement specializes to
`R^p h_* R^q f_* F ⟹ R^{p + q} (h ∘ f)_* F`. Taking `Z` to be the punctual site, so that
`h_* = Γ(Y, -)`, it specializes further to the Leray spectral sequence
`H^p(Y, R^q f_* F) ⟹ H^{p + q}(X, F)`.

(blueprint: `sk-thm-groth-ss`) -/
theorem Functor.exists_grothendieckSpectralSequence (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ p q : ℕ,
        Nonempty ((E.page 2).X (p, q) ≅ (G.rightDerived p).obj ((F.rightDerived q).obj X))) ∧
      E.AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X) := by
  let := HasDerivedCategory.standard B
  let := HasDerivedCategory.standard C
  exact ⟨F.grothendieckSpectralSequence G X,
    F.nonempty_grothendieckSpectralSequence_page_two_iso G X,
    F.grothendieckSpectralSequence_abutsTo G hFG X⟩

end CategoryTheory
