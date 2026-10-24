/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Rigid.TraceZigzag
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleSymmetric
public import WeilConjectures.TraceFormula.SupportedClass

/-!

# Point normalization of the trace class

Over the base point `s = Spec k`, the trace class of the diagonal correspondence of an
endomorphism `v` of a dualizable object integrates to the categorical trace of `v` (blueprint
`prop-trf-pairing-point-normalization`, `sk-p-pairing`).

## Strategy

By the description of the trace class as an exceptional adjoint along the fixed locus
(`Correspondence.traceClass_eq_homEquiv`) and of the supported class of the diagonal
correspondence (`supportedClass_ofEnd`), the integral `∫_s Tr(v)` is
`P ∘ (v ⊗ D_s K) ∘ σ` (`Correspondence.integral_traceClass_ofEnd_eq`) for a morphism
`σ : ℚ̄_ℓ ⟶ K ⊗ D_s K` built from the class of the identity and a pairing
`P : K ⊗ D_s K ⟶ ℚ̄_ℓ` built from the evaluation. The pair `(σ, P)` satisfies the zigzag identity
of a duality, and the trace through such a pair is the categorical trace
(`MonoidalCategory.trace_eq_of_zigzag`), the Koszul braiding being symmetric
(`boundedConstructibleBraiding_hom_braiding_hom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Verdier

/-- Abstract form of the reduction of the integral of the trace class of a diagonal
correspondence: the exceptional adjoint along `d` of `b ≫ G (A ≫ B) ≫ dI ≫ e`, read through
`ψ : R ≅ 𝟭`, with `G B ≫ dI = dI ≫ (v ▷ D)`. -/
lemma integral_traceClass_aux {Cs CP : Type*} [Category Cs] [MonoidalCategory Cs] [Category CP]
    {G : CP ⥤ Cs} {Lf R : Cs ⥤ Cs} (adj : Lf ⊣ R) (ψ : R ≅ 𝟭 Cs) {U T E : CP} {U' : Cs}
    {K D ω ω' : Cs} (ε : 𝟙_ Cs ⟶ U') (b : Lf.obj U' ⟶ G.obj T) (sc A : T ⟶ E) (B : E ⟶ E)
    (hsc : sc = A ≫ B) (dI : G.obj E ⟶ K ⊗ D) (v : K ⟶ K)
    (hB : G.map B ≫ dI = dI ≫ v ▷ D) (e : K ⊗ D ⟶ ω) (d₁ : R.obj ω ⟶ ω') (d₂ : ω' ⟶ 𝟙_ Cs) :
    (ε ≫ adj.homEquiv _ _ (b ≫ G.map sc ≫ dI ≫ e) ≫ d₁) ≫ d₂ =
      (ε ≫ adj.unit.app U' ≫ R.map (b ≫ G.map A ≫ dI) ≫ ψ.hom.app _) ≫ v ▷ D ≫
        (e ≫ ψ.inv.app ω ≫ d₁ ≫ d₂) := by
  subst hsc
  rw [Adjunction.homEquiv_unit, G.map_comp]
  simp only [Category.assoc, reassoc_of% hB]
  rw [show b ≫ G.map A ≫ dI ≫ v ▷ D ≫ e = (b ≫ G.map A ≫ dI) ≫ (v ▷ D ≫ e) by
    simp only [Category.assoc], R.map_comp, ← NatIso.naturality_2 ψ (v ▷ D ≫ e)]
  simp only [Functor.id_map, Category.assoc]

/-- Abstract form of the naturality of the identification `LΔ^* (K ⊠ N) ≅ K ⊗ N` in `K`. -/
lemma diagIso_naturality_aux {Cs CP : Type*} [Category Cs] [MonoidalCategory Cs] [Category CP]
    [MonoidalCategory CP] (G : CP ⥤ Cs) [G.Monoidal] {A A' Y : CP} {K K' N : Cs} (a : A ⟶ A')
    (k : K ⟶ K') (e₁ : G.obj A ⟶ K) (e₁' : G.obj A' ⟶ K') (e₂ : G.obj Y ⟶ N)
    (he : G.map a ≫ e₁' = e₁ ≫ k) :
    G.map (a ▷ Y) ≫ Functor.OplaxMonoidal.δ G A' Y ≫ (e₁' ⊗ₘ e₂) =
      (Functor.OplaxMonoidal.δ G A Y ≫ (e₁ ⊗ₘ e₂)) ≫ k ▷ N := by
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, Category.assoc, ← tensorHom_id,
    ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, he, Category.id_comp,
    Category.comp_id]

end CategoryTheory.Verdier

namespace CategoryTheory.Verdier

/-- A naturality square for a composite of three morphisms. -/
lemma comp_comp_naturality {𝒞 : Type*} [Category 𝒞] {A A' B B' C C' D D' : 𝒞} {x : A ⟶ A'}
    {y : B ⟶ B'} {z : C ⟶ C'} {w : D ⟶ D'} {c : A ⟶ B} {c' : A' ⟶ B'} {e : B ⟶ C}
    {e' : B' ⟶ C'} {s : C ⟶ D} {s' : C' ⟶ D'} (h₁ : x ≫ c' = c ≫ y) (h₂ : y ≫ e' = e ≫ z)
    (h₃ : z ≫ s' = s ≫ w) :
    x ≫ c' ≫ e' ≫ s' = (c ≫ e ≫ s) ≫ w := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

end CategoryTheory.Verdier

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Naturality

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

lemma upperStar_map_comp_eqToHom_of_eq {f g : X ⟶ X} (h : f = g)
    {L L' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L') :
    (boundedConstructibleUpperStar _ ℓ f).map b ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (boundedConstructibleUpperStar _ ℓ g).map b := by
  subst h
  simp

variable (ℓ) in
/-- The identification `LΔ^* (K ⊠ N) ≅ K ⊗ N` is natural in `K`. -/
lemma diagUpperStarExternalProductIso_hom_naturality {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (v : K ⟶ K') (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).map v ▷
          (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj N) ≫
        (diagUpperStarExternalProductIso ℓ K' N).hom =
      (diagUpperStarExternalProductIso ℓ K N).hom ≫ v ▷ N := by
  have h₁ := (boundedConstructibleUpperStarComp _ ℓ (diag X) prod.fst).inv.naturality v
  have h₂ := upperStar_map_comp_eqToHom_of_eq (ℓ := ℓ)
    (show diag X ≫ prod.fst = 𝟙 X by simp) v
  have h₃ := (boundedConstructibleUpperStarId _ ℓ X).hom.naturality v
  have h₄ := Verdier.comp_comp_naturality h₁ h₂ h₃
  have h₅ := Verdier.diagIso_naturality_aux (boundedConstructibleUpperStar _ ℓ (diag X))
    (Y := (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj N) _ v _ _
    ((boundedConstructibleUpperStarComp _ ℓ (diag X) prod.snd).inv.app N ≫
      eqToHom (by rw [diag, prod.lift_snd]) ≫ (boundedConstructibleUpperStarId _ ℓ X).hom.app N)
    h₄
  simp only [diagUpperStarExternalProductIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Functor.Monoidal.μIso_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom]
  convert h₅ using 4
  all_goals rfl

set_option maxHeartbeats 20000 in
example : (monoidalCategory_boundedConstructible (Profinite.padicAlgClRingObj ℓ) X).toMonoidalCategoryStruct =
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).instMonoidalCategoryStructFullSubcategory := rfl

end Naturality

end AlgebraicGeometry.ProEtale.CondensedRing
