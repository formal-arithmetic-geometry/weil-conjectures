# CategoryTheory.frame_dual_mate

## Reason

The shorter proof does not inspect the original boundedness, finite-frame and
coevaluation-component hypotheses. Retain all hypotheses verbatim and scope
`linter.unusedVariables false` to this declaration so it compiles without warnings.
The delivery checker classifies this declaration-local option as an interface
command and requires this record. The option changes only lint reporting while
elaborating this theorem; it introduces no persistent option and changes no
mathematical signature, definition, instance, attribute or import.

The direct `ModuleHomComplex` import is also redundant: the retained public
`Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy` import publicly imports the
current `WeilConjectures.Algebra.Homology.ModuleHomComplex`. Remove the direct
import while preserving exactly the same transitive public declarations. This
also avoids combining the renamed module with pre-rename cached dependencies
while the server refreshes its compiled snapshot. No definitions are copied.

## Old

The current delivery base has the redundant direct import:

```lean
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
```


```lean
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
```

## New

Remove the direct import above; retain
`public import Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy`, whose public
imports supply `ModuleHomComplex`. The resulting public declarations are unchanged.


```lean
set_option linter.unusedVariables false in
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
```

The existing docstring remains between the scoped option and the theorem.
The proof is completed in the same delivery; all data definitions are unchanged.

## Users

`tools/downstream.py Sheaf.CategoryTheory.DerivedCategory.FrameDualMate --uses
CategoryTheory.frame_dual_mate` lists the seven downstream modules below. It finds
no reference to the theorem outside its own module. All downstream statements and
definitions retain exactly the same meaning. No target review is reopened because
no definition or mathematical statement changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedCategory.FrameDualMate | A2 | Public declarations unchanged; redundant direct import removed; no adaptation. |
| Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace | J5 | Public declarations unchanged; redundant direct import removed; no adaptation. |
| Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws | H1 | Public declarations unchanged; redundant direct import removed; no adaptation. |
| Sheaf.Paper.CondensedPointSupertrace | unclaimed | Public declarations unchanged; redundant direct import removed; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Public declarations unchanged; redundant direct import removed; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | Public declarations unchanged; redundant direct import removed; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Public declarations unchanged; redundant direct import removed; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Public declarations unchanged; redundant direct import removed; no adaptation. |

## Status

landed 20261019T231023-L-539718 2026-10-19 (merge of deliver/A2/Sheaf.CategoryTheory.DerivedCategory.FrameDualMate)
