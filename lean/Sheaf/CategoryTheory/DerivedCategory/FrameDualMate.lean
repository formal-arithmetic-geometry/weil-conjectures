/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! # Precomposition as the dual mate of a finite-frame pairing

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
  sk-p-trace/sk-p-trace.proof.md, final two sentences
  (blueprint: lem-trf-frame-dual-mate).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

/-- The coefficient ring in degree zero, with the canonical signed tensor-unit structure.
Source: blueprint `sk-p-trace/sk-p-trace.proof.md`, finite-frame duality convention
(blueprint: lem-trf-frame-dual-mate). -/
noncomputable abbrev frameUnit (A : Type u) [CommRing A] :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  HomologicalComplex.tensorUnit (ModuleCat A) (.up ℤ)

/-- The chain map induced by precomposition on the recorded total Hom complexes.

Source: blueprint `sk-p-trace.proof.md`, final two sentences
(blueprint: lem-trf-frame-dual-mate).  Its components are the actual cochain
composition `(Cochain.ofHom f).comp φ (zero_add j)`, as in
`CochainComplex.moduleHomPrecomp`.
-/
noncomputable def frameDualMap {A : Type u} [CommRing A]
    {P R : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ R) :
    CochainComplex.moduleHomComplex R (frameUnit A) ⟶
      CochainComplex.moduleHomComplex P (frameUnit A) :=
  CochainComplex.moduleHomPrecomp (frameUnit A) f

/-- Precomposition is the right dual mate for finite-frame pairings.

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
`sk-p-trace/sk-p-trace.proof.md`, final two sentences
(blueprint: lem-trf-frame-dual-mate).

Proof: the component hypotheses fix evaluation to φ ⊗ x ↦ φ(x), zero off
sum degree zero, and coevaluation at 1 to the finite dual-frame sum, with each
functional embedded in dual degree -i. Precomposition is a chain map by the signed
total-Hom differential and `Cochain.ofHom` composition. Evaluation on homogeneous pure
tensors gives the mate equation, and that equation determines every functional degree by degree,
so the map is unique.  Expanding the finite dual frames gives the coevaluation
identity.  The two triangle identities for each chosen evaluation and
coevaluation are used to identify the displayed maps as right-dual pairings.
-/
theorem frame_dual_mate
    {A : Type u} [CommRing A]
    (P R : CochainComplex (ModuleCat.{u} A) ℤ)
    (hPbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    (hRbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (R.X i))
    (hPfinite : ∀ i : ℤ, Module.Finite A (P.X i))
    (hRfinite : ∀ i : ℤ, Module.Finite A (R.X i))
    (hPprojective : ∀ i : ℤ, Module.Projective A (P.X i))
    (hRprojective : ∀ i : ℤ, Module.Projective A (R.X i))
    (nP : ℤ → ℕ)
    (eP : ∀ i : ℤ, Fin (nP i) → P.X i)
    (εP : ∀ i : ℤ, Fin (nP i) → (P.X i →ₗ[A] A))
    (frameP : ∀ (i : ℤ) (x : P.X i), x = ∑ a, (εP i a x) • eP i a)
    (hPempty : ∀ i : ℤ, IsZero (P.X i) → nP i = 0)
    (nR : ℤ → ℕ)
    (eR : ∀ i : ℤ, Fin (nR i) → R.X i)
    (εR : ∀ i : ℤ, Fin (nR i) → (R.X i →ₗ[A] A))
    (frameR : ∀ (i : ℤ) (x : R.X i), x = ∑ a, (εR i a x) • eR i a)
    (hRempty : ∀ i : ℤ, IsZero (R.X i) → nR i = 0)
    (evP : CochainComplex.moduleHomComplex P (frameUnit A) ⊗ P ⟶ frameUnit A)
    (coevP : frameUnit A ⟶ P ⊗ CochainComplex.moduleHomComplex P (frameUnit A))
    (evR : CochainComplex.moduleHomComplex R (frameUnit A) ⊗ R ⟶ frameUnit A)
    (coevR : frameUnit A ⟶ R ⊗ CochainComplex.moduleHomComplex R (frameUnit A))
    (hEvP : ∀ (i : ℤ)
        (φ : (CochainComplex.moduleHomComplex P (frameUnit A)).X (-i)) (x : P.X i),
      (evP.f 0).hom
          ((HomologicalComplex.ιTensorObj (CochainComplex.moduleHomComplex P (frameUnit A))
            P (-i) i 0 (neg_add_cancel i)).hom (φ ⊗ₜ[A] x)) =
        (φ.v i 0 (add_neg_cancel i)).hom x)
    (hEvPzero : ∀ n : ℤ, n ≠ 0 → evP.f n = 0)
    (hCoevP : ∀ (a b : ℤ),
      (∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) →
      (coevP.f 0).hom
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv.hom 1) =
        ∑ i ∈ Finset.Icc a b, ∑ r : Fin (nP i),
          (HomologicalComplex.ιTensorObj P (CochainComplex.moduleHomComplex P (frameUnit A))
            i (-i) 0 (add_neg_cancel i)).hom
              (eP i r ⊗ₜ[A] CochainComplex.HomComplex.Cochain.single
                (ModuleCat.ofHom (εP i r) ≫
                  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv) (-i)))
    (hEvR : ∀ (i : ℤ)
        (φ : (CochainComplex.moduleHomComplex R (frameUnit A)).X (-i)) (x : R.X i),
      (evR.f 0).hom
          ((HomologicalComplex.ιTensorObj (CochainComplex.moduleHomComplex R (frameUnit A))
            R (-i) i 0 (neg_add_cancel i)).hom (φ ⊗ₜ[A] x)) =
        (φ.v i 0 (add_neg_cancel i)).hom x)
    (hEvRzero : ∀ n : ℤ, n ≠ 0 → evR.f n = 0)
    (hCoevR : ∀ (a b : ℤ),
      (∀ i : ℤ, i < a ∨ b < i → IsZero (R.X i)) →
      (coevR.f 0).hom
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv.hom 1) =
        ∑ i ∈ Finset.Icc a b, ∑ r : Fin (nR i),
          (HomologicalComplex.ιTensorObj R (CochainComplex.moduleHomComplex R (frameUnit A))
            i (-i) 0 (add_neg_cancel i)).hom
              (eR i r ⊗ₜ[A] CochainComplex.HomComplex.Cochain.single
                (ModuleCat.ofHom (εR i r) ≫
                  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv) (-i)))
    (hTriP₁ :
      (CochainComplex.moduleHomComplex P (frameUnit A)) ◁ coevP ≫
          (α_ _ _ _).inv ≫ evP ▷ (CochainComplex.moduleHomComplex P (frameUnit A)) =
        (ρ_ _).hom ≫ (λ_ _).inv)
    (hTriP₂ :
      coevP ▷ P ≫ (α_ _ _ _).hom ≫ P ◁ evP =
        (λ_ _).hom ≫ (ρ_ _).inv)
    (hTriR₁ :
      (CochainComplex.moduleHomComplex R (frameUnit A)) ◁ coevR ≫
          (α_ _ _ _).inv ≫ evR ▷ (CochainComplex.moduleHomComplex R (frameUnit A)) =
        (ρ_ _).hom ≫ (λ_ _).inv)
    (hTriR₂ :
      coevR ▷ R ≫ (α_ _ _ _).hom ≫ R ◁ evR =
        (λ_ _).hom ≫ (ρ_ _).inv)
    (f : P ⟶ R) :
    HomologicalComplex.tensorHom (frameDualMap f) (𝟙 P) ≫ evP =
        HomologicalComplex.tensorHom
          (𝟙 (CochainComplex.moduleHomComplex R (frameUnit A))) f ≫ evR ∧
      coevP ≫ HomologicalComplex.tensorHom f
          (𝟙 (CochainComplex.moduleHomComplex P (frameUnit A))) =
        coevR ≫ HomologicalComplex.tensorHom (𝟙 R) (frameDualMap f) ∧
      (∀ v : CochainComplex.moduleHomComplex R (frameUnit A) ⟶
          CochainComplex.moduleHomComplex P (frameUnit A),
        HomologicalComplex.tensorHom v (𝟙 P) ≫ evP =
            HomologicalComplex.tensorHom
              (𝟙 (CochainComplex.moduleHomComplex R (frameUnit A))) f ≫ evR →
          v = frameDualMap f)
:= by
  sorry

end CategoryTheory
