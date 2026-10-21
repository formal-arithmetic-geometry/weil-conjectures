/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Naturality and rationalization of a completed tensor comparison

Source: Weil conjectures blueprint, main-20261015, `def-wf-tensor-product`, second
sentence (tensor Frobenius); the abstract reflector and rationalization argument
(blueprint: lem-sf-completed-tensor-rational-naturality).

## Main definitions and statements

- `restriction`: the restriction P of H.
- `tensor`: the completed bifunctor B.
- `comparison`: the given component d = c ; L(tau).
- `naturality_and_rationalization`: naturality and the unique localized isomorphism.

The full subcategory is Mathlib's `ObjectProperty.FullSubcategory`. The raw localization
uses the project's scalar-first tensor convention: `f/p^n` is `p⁻ⁿ ⊗ f`.
The object and fraction formulas for the supplied localized functors use heterogeneous
equality only to accommodate their specified, rather than definitional, object maps.
-/

@[expose] public section

universe r u v

open TensorProduct

namespace CategoryTheory.CompletedTensorComparison

variable {D : Type u} [Category.{v} D] (C : ObjectProperty D)
  (L : D ⥤ C.FullSubcategory) (H : D ≌ D)
  (hH : ∀ M : C.FullSubcategory, C (H.functor.obj M.obj))
  (T : D × D ⥤ D)

/-- The restriction P of H to the full subcategory.
Source: blueprint `def-wf-tensor-product`, tensor Frobenius
(blueprint: lem-sf-completed-tensor-rational-naturality). -/
def restriction : C.FullSubcategory ⥤ C.FullSubcategory :=
  C.lift (C.ι ⋙ H.functor) hH

/-- The completed bifunctor B(M,N) = L(T(M,N)).
Source: blueprint `def-wf-tensor-product`, tensor Frobenius
(blueprint: lem-sf-completed-tensor-rational-naturality). -/
def tensor : C.FullSubcategory × C.FullSubcategory ⥤ C.FullSubcategory :=
  (C.ι.prod C.ι) ⋙ T ⋙ L

/-- The specified component d = c ; L(tau), regarded in the full subcategory.
Source: blueprint `def-wf-tensor-product`, tensor Frobenius
(blueprint: lem-sf-completed-tensor-rational-naturality). -/
def comparison
    (c : ∀ X : D, H.functor.obj (C.ι.obj (L.obj X)) ≅ C.ι.obj (L.obj (H.functor.obj X)))
    (τ : T ⋙ H.functor ≅ (H.functor.prod H.functor) ⋙ T)
    (M N : C.FullSubcategory) :
    (restriction C H hH).obj ((tensor C L T).obj (M, N)) ≅
      (tensor C L T).obj ((restriction C H hH).obj M, (restriction C H hH).obj N) :=
  ObjectProperty.isoMk C
    (c (T.obj (M.obj, N.obj)) ≪≫ C.ι.mapIso (L.mapIso (τ.app (M.obj, N.obj))))

/-- Unit normalization forces naturality and a unique rational tensor comparison.
Source: blueprint `def-wf-tensor-product`, second sentence (tensor Frobenius)
(blueprint: lem-sf-completed-tensor-rational-naturality).

Proof: (1) rewrite H(eta_X) as eta_(HX) ; c_X.inv. The reflector Hom bijection
then cancels H(eta_X) against any target in C; no global epimorphism is asserted.
(2) Precompose the two candidate naturality composites for c with H(eta_X).
Naturality of eta and the unit equations make them equal, so (1) cancels.
(3) Apply (2) to T(f,g), then functoriality of L and naturality of tau. This gives
simultaneous naturality of d = c ; L(tau).
(4) Use `IsLocalizedModule.isBaseChange` (lem-weil-pbc-localization-module-tensor)
and `LocalizedModule.Away` (def-weil-pbc-module-localization-away) on each Hom
module: every arrow is f/p^n, with equality tested after multiplication by some
power of p. Scalar-localization composition adds denominators.
(5) Define every component to be Q(d). For arbitrary fractions f/p^r and g/p^s,
the prescribed functor formulas reduce naturality to (3), divided by p^(r+s).
This proves an equality in localized Hom modules without cancelling p integrally.
(6) Functoriality of Q gives both inverse identities with Q(d.inv); naturality of
the inverse follows by composing the forward naturality equation with inverses.
Every localized object is an integral object, so the component formula also gives
uniqueness. No step requires torsion-free Hom modules. -/
theorem naturality_and_rationalization
    (A : Type r) [CommRing A] [Preadditive D] [Linear A D] (p : A)
    [L.Additive] [L.Linear A] [H.functor.Additive] [H.functor.Linear A]
    [(restriction C H hH).IsEquivalence]
    (η : 𝟭 D ⟶ L ⋙ C.ι)
    (hη : ∀ (X : D) (Y : C.FullSubcategory),
      Function.Bijective (fun f : C.ι.obj (L.obj X) ⟶ Y.obj ↦ η.app X ≫ f))
    (c : ∀ X : D, H.functor.obj (C.ι.obj (L.obj X)) ≅ C.ι.obj (L.obj (H.functor.obj X)))
    (hc : ∀ X : D, H.functor.map (η.app X) ≫ (c X).hom = η.app (H.functor.obj X))
    (hT : ∀ M M' N N' : D,
      ∃ t : (M ⟶ M') →ₗ[A] (N ⟶ N') →ₗ[A] (T.obj (M, N) ⟶ T.obj (M', N')),
        ∀ (f : M ⟶ M') (g : N ⟶ N'), t f g = T.map (Prod.mkHom f g))
    (τ : T ⋙ H.functor ≅ (H.functor.prod H.functor) ⋙ T)
    (Pbar : ScalarLocalization A C.FullSubcategory p ⥤
      ScalarLocalization A C.FullSubcategory p)
    (Bbar : ScalarLocalization A C.FullSubcategory p ×
      ScalarLocalization A C.FullSubcategory p ⥤ ScalarLocalization A C.FullSubcategory p)
    (hPobj : ∀ M : C.FullSubcategory,
      Pbar.obj ⟨M⟩ = ⟨(restriction C H hH).obj M⟩)
    (hBobj : ∀ M N : C.FullSubcategory,
      Bbar.obj (⟨M⟩, ⟨N⟩) = ⟨(tensor C L T).obj (M, N)⟩)
    (hPmap : ∀ (M M' : C.FullSubcategory) (f : M ⟶ M') (n : ℕ),
      HEq (Pbar.map ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) ⊗ₜ[A] f :
        ScalarLocalization.mk (R := A) (p := p) M ⟶ ScalarLocalization.mk M'))
        ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) ⊗ₜ[A]
          (restriction C H hH).map f))
    (hBmap : ∀ (M M' N N' : C.FullSubcategory) (f : M ⟶ M') (g : N ⟶ N') (n m : ℕ),
      HEq (Bbar.map (Prod.mkHom
        ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) ⊗ₜ[A] f :
          ScalarLocalization.mk (R := A) (p := p) M ⟶ ScalarLocalization.mk M')
        ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ m) ⊗ₜ[A] g :
          ScalarLocalization.mk (R := A) (p := p) N ⟶ ScalarLocalization.mk N')))
        ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ (n + m)) ⊗ₜ[A]
          (tensor C L T).map (Prod.mkHom f g))) :
    (∀ (X X' : D) (f : X ⟶ X'),
      H.functor.map (C.ι.map (L.map f)) ≫ (c X').hom =
        (c X).hom ≫ C.ι.map (L.map (H.functor.map f))) ∧
    (∀ (M M' N N' : C.FullSubcategory) (f : M ⟶ M') (g : N ⟶ N'),
      (restriction C H hH).map ((tensor C L T).map (Prod.mkHom f g)) ≫
          (comparison C L H hH T c τ M' N').hom =
        (comparison C L H hH T c τ M N).hom ≫
          (tensor C L T).map (Prod.mkHom
            ((restriction C H hH).map f) ((restriction C H hH).map g))) ∧
    ∃! μ : Bbar ⋙ Pbar ≅ (Pbar.prod Pbar) ⋙ Bbar,
      ∀ M N : C.FullSubcategory,
        HEq (μ.hom.app (⟨M⟩, ⟨N⟩))
          ((ScalarLocalization.localization A C.FullSubcategory p).map
            (comparison C L H hH T c τ M N).hom) ∧
        HEq (μ.inv.app (⟨M⟩, ⟨N⟩))
          ((ScalarLocalization.localization A C.FullSubcategory p).map
            (comparison C L H hH T c τ M N).inv) := by
  sorry

end CategoryTheory.CompletedTensorComparison
