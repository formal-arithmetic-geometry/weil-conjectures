/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.TraceFormula.ProperCompatibilityExchange

/-!

# Exchange of the evaluation kernels along a proper map

For a proper morphism `f : X ⟶ Y`, `q = f × f` and `K' = Rf_* K`, the kernel pushforward
`ρ_f : Rq_* (K ⊠ D_X K) ⟶ K' ⊠ D_Y K'` exchanges the evaluation kernels:
`e_{K'} ∘ ρ_f = RΔ_{Y*} τ_f ∘ Rq_* e_K` (blueprint `lem-trf-trace-map-exchange`, (1)). The proof
passes to the `LΔ_Y^* ⊣ RΔ_{Y*}` and `Lf^* ⊣ Rf_*` adjoints, where it is the coherence of the
composition isomorphisms of the derived pullbacks with each other and with the tensor
comparisons.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- The adjoint for a composite adjunction through the conjugate composition isomorphism: for
`Lpq ≅ Lq ⋙ Lp` and its conjugate `Rp ⋙ Rq ≅ Rpq`, `(φ♯)♯ ≫ (Rp ⋙ Rq ≅ Rpq) = (c ≫ φ)♯`. -/
lemma Adjunction.homEquiv_homEquiv_comp_hom_app {CA CB CC : Type*} [Category CA] [Category CB]
    [Category CC] {Lp : CB ⥤ CA} {Rp : CA ⥤ CB} {Lq : CC ⥤ CB} {Rq : CB ⥤ CC} {Lpq : CC ⥤ CA}
    {Rpq : CA ⥤ CC} (ap : Lp ⊣ Rp) (aq : Lq ⊣ Rq) (apq : Lpq ⊣ Rpq) (cU : Lpq ≅ Lq ⋙ Lp)
    (cR : Rp ⋙ Rq ≅ Rpq) (hcR : cR.inv = conjugateEquiv apq (aq.comp ap) cU.inv) {oC : CC}
    {oA : CA} (φ : Lp.obj (Lq.obj oC) ⟶ oA) :
    aq.homEquiv _ _ (ap.homEquiv _ _ φ) ≫ cR.hom.app oA =
      apq.homEquiv _ _ (cU.hom.app oC ≫ φ) := by
  have h := Adjunction.unit_map_comp_unit_map ap aq apq cU cR hcR (𝟙 _) φ (cU.hom.app oC ≫ φ)
    (by simp)
  rw [← cancel_mono (cR.inv.app oA)]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  simpa [Adjunction.homEquiv_unit] using h

/-- Monoidal bookkeeping: `δ ≫ ((a ≫ c₁) ⊗ (b ≫ c₂')) = δ ≫ (c₁ ⊗ c₂) ≫ (M ◁ χ)` for `a = 𝟙` and
`b ≫ c₂' = c₂ ≫ χ`. -/
lemma comp_tensorHom_eq_of_eq {C : Type*} [Category C] [MonoidalCategory C] {T P Q Q' M N N' : C}
    (δ : T ⟶ P ⊗ Q) (a : P ⟶ P) (ha : a = 𝟙 P) (c₁ : P ⟶ M) (b : Q ⟶ Q') (c₂' : Q' ⟶ N')
    (c₂ : Q ⟶ N) (χ : N ⟶ N') (h : b ≫ c₂' = c₂ ≫ χ) :
    δ ≫ ((a ≫ c₁) ⊗ₘ (b ≫ c₂')) = δ ≫ (c₁ ⊗ₘ c₂) ≫ (M ◁ χ) := by
  subst ha
  rw [MonoidalCategory.tensorHom_comp_whiskerLeft, h, Category.id_comp]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Coherence

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {W X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- Associativity of the composition isomorphisms, with the inner one inverted. -/
lemma boundedConstructibleUpperStarComp_hom_app_map_inv_app (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) (A : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ a b).hom.app
        ((boundedConstructibleUpperStar Λ ℓ c).obj A) ≫
      (boundedConstructibleUpperStar Λ ℓ a).map
        ((boundedConstructibleUpperStarComp Λ ℓ b c).inv.app A) =
    (boundedConstructibleUpperStarComp Λ ℓ (a ≫ b) c).inv.app A ≫
      eqToHom (by rw [Category.assoc]) ≫
      (boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).hom.app A := by
  rw [← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ (a ≫ b) c).hom.app A),
    reassoc_of% (boundedConstructibleUpperStarComp_assoc_app Λ ℓ a b c A)]
  simp [← Functor.map_comp]

/-- Associativity of the composition isomorphisms, with the outer one inverted. -/
lemma boundedConstructibleUpperStar_map_hom_app_comp_inv_app (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) (A : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStar Λ ℓ a).map
        ((boundedConstructibleUpperStarComp Λ ℓ b c).hom.app A) ≫
      (boundedConstructibleUpperStarComp Λ ℓ a b).inv.app
        ((boundedConstructibleUpperStar Λ ℓ c).obj A) =
    (boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).inv.app A ≫
      eqToHom (by rw [Category.assoc]) ≫
      (boundedConstructibleUpperStarComp Λ ℓ (a ≫ b) c).hom.app A := by
  have h := boundedConstructibleUpperStarComp_assoc_app Λ ℓ a b c A
  rw [← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).hom.app A),
    ← cancel_epi (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj A)
      (Category.assoc a b c)))]
  rw [← reassoc_of% h]
  simp

/-- Associativity of the composition isomorphisms, both inverted. -/
lemma boundedConstructibleUpperStarComp_inv_app_comp_inv_app' (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) (A : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ a b).inv.app
        ((boundedConstructibleUpperStar Λ ℓ c).obj A) ≫
      (boundedConstructibleUpperStarComp Λ ℓ (a ≫ b) c).inv.app A =
    (boundedConstructibleUpperStar Λ ℓ a).map
        ((boundedConstructibleUpperStarComp Λ ℓ b c).inv.app A) ≫
      (boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).inv.app A ≫
      eqToHom (by rw [Category.assoc]) := by
  have h := boundedConstructibleUpperStarComp_assoc_app Λ ℓ a b c A
  rw [← cancel_epi ((boundedConstructibleUpperStar Λ ℓ a).map
      ((boundedConstructibleUpperStarComp Λ ℓ b c).hom.app A)),
    ← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).hom.app A),
    ← cancel_epi (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj A)
      (Category.assoc a b c)))]
  rw [← reassoc_of% h]
  simp [← Functor.map_comp_assoc]

lemma boundedConstructibleUpperStarComp_hom_app_map_eqToHom_inv_app {r r' : X ⟶ Z} (h : r = r')
    (a : W ⟶ X) (A : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ a r).hom.app A ≫
      (boundedConstructibleUpperStar Λ ℓ a).map
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj A) h)) ≫
      (boundedConstructibleUpperStarComp Λ ℓ a r').inv.app A =
    eqToHom (by rw [h]) := by
  subst h
  simp

lemma eqToHom_comp_boundedConstructibleUpperStarComp_inv_app {u u' : W ⟶ X} (h : u = u')
    (v : X ⟶ Z) (A : Dᵇc(Z.left)⟦Λ⟧) :
    eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ v).obj A)) h) ≫
      (boundedConstructibleUpperStarComp Λ ℓ u' v).inv.app A =
    (boundedConstructibleUpperStarComp Λ ℓ u v).inv.app A ≫ eqToHom (by rw [h]) := by
  subst h
  simp

lemma boundedConstructibleUpperStarComp_hom_app_eqToHom_id {r : X ⟶ X} (h : r = 𝟙 X)
    (f : X ⟶ Y) (A : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ r f).hom.app A ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ f).obj A)) h) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app
        ((boundedConstructibleUpperStar Λ ℓ f).obj A) =
    eqToHom (by rw [h, Category.id_comp]; rfl) := by
  subst h
  simpa using boundedConstructibleUpperStarComp_id_left_app Λ ℓ f A

lemma boundedConstructibleUpperStarComp_inv_app_eqToHom_id {r : Y ⟶ Y} (h : r = 𝟙 Y)
    (f : X ⟶ Y) (A : Dᵇc(Y.left)⟦Λ⟧)
    (h' : (boundedConstructibleUpperStar Λ ℓ (f ≫ r)).obj A =
      (boundedConstructibleUpperStar Λ ℓ f).obj A) :
    (boundedConstructibleUpperStarComp Λ ℓ f r).inv.app A ≫ eqToHom h' =
      (boundedConstructibleUpperStar Λ ℓ f).map
        (eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h) ≫
          (boundedConstructibleUpperStarId Λ ℓ Y).hom.app A) := by
  subst h
  rw [← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ f (𝟙 Y)).hom.app A)]
  simpa using (boundedConstructibleUpperStarComp_id_right_app Λ ℓ f A).symm

/-- The two identifications `Lf^* LΔ_Y^* Lp^* A ≅ Lf^* A` in the square `ΔX ≫ q = f ≫ ΔY` with
`q ≫ p = p' ≫ f`, `ΔY ≫ p = 𝟙` and `ΔX ≫ p' = 𝟙` agree. -/
lemma boundedConstructibleUpperStarComp_square_coherence (f : X ⟶ Y) (ΔX : X ⟶ W)
    (ΔY : Y ⟶ Z) (q : W ⟶ Z) (p : Z ⟶ Y) (p' : W ⟶ X) (h₁ : f ≫ ΔY = ΔX ≫ q)
    (h₂ : q ≫ p = p' ≫ f) (h₃ : ΔY ≫ p = 𝟙 Y) (h₄ : ΔX ≫ p' = 𝟙 X) (A : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ f ΔY).inv.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj A) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ p).obj A)) h₁) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX q).hom.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj A) ≫
      (boundedConstructibleUpperStar Λ ℓ ΔX).map
        ((boundedConstructibleUpperStarComp Λ ℓ q p).inv.app A ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₂) ≫
          (boundedConstructibleUpperStarComp Λ ℓ p' f).hom.app A) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX p').inv.app
        ((boundedConstructibleUpperStar Λ ℓ f).obj A) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ f).obj A)) h₄) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app
        ((boundedConstructibleUpperStar Λ ℓ f).obj A) =
    (boundedConstructibleUpperStar Λ ℓ f).map
      ((boundedConstructibleUpperStarComp Λ ℓ ΔY p).inv.app A ≫
        eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₃) ≫
        (boundedConstructibleUpperStarId Λ ℓ Y).hom.app A) := by
  have e₁ := boundedConstructibleUpperStarComp_hom_app_map_inv_app Λ ℓ ΔX q p A
  have e₂ := boundedConstructibleUpperStar_map_hom_app_comp_inv_app Λ ℓ ΔX p' f A
  have e₃ := boundedConstructibleUpperStarComp_hom_app_map_eqToHom_inv_app Λ ℓ h₂ ΔX A
  have e₄ := boundedConstructibleUpperStarComp_hom_app_eqToHom_id Λ ℓ h₄ f A
  have e₅ := eqToHom_comp_boundedConstructibleUpperStarComp_inv_app Λ ℓ h₁ p A
  have e₆ := boundedConstructibleUpperStarComp_inv_app_comp_inv_app' Λ ℓ f ΔY p A
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂, reassoc_of% e₃, e₄, reassoc_of% e₅,
    reassoc_of% e₆]
  simp only [eqToHom_trans]
  rw [boundedConstructibleUpperStarComp_inv_app_eqToHom_id Λ ℓ h₃ f A]
  simp only [Functor.map_comp]

lemma boundedConstructibleUpperStar_map_eqToHom_id {r : X ⟶ X} (h : r = 𝟙 X)
    {M K : Dᵇc(X.left)⟦Λ⟧} (φ : M ⟶ K) :
    (boundedConstructibleUpperStar Λ ℓ r).map φ ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj K) h) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app K =
    eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj M) h) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app M ≫ φ := by
  subst h
  simp

/-- `boundedConstructibleUpperStarComp_square_coherence` followed by a map `φ : Lf^* A ⟶ K`. -/
lemma boundedConstructibleUpperStarComp_square_coherence_comp (f : X ⟶ Y) (ΔX : X ⟶ W)
    (ΔY : Y ⟶ Z) (q : W ⟶ Z) (p : Z ⟶ Y) (p' : W ⟶ X) (h₁ : f ≫ ΔY = ΔX ≫ q)
    (h₂ : q ≫ p = p' ≫ f) (h₃ : ΔY ≫ p = 𝟙 Y) (h₄ : ΔX ≫ p' = 𝟙 X) {A : Dᵇc(Y.left)⟦Λ⟧}
    {K : Dᵇc(X.left)⟦Λ⟧} (φ : (boundedConstructibleUpperStar Λ ℓ f).obj A ⟶ K) :
    (boundedConstructibleUpperStarComp Λ ℓ f ΔY).inv.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj A) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ p).obj A)) h₁) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX q).hom.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj A) ≫
      (boundedConstructibleUpperStar Λ ℓ ΔX).map
        ((boundedConstructibleUpperStarComp Λ ℓ q p).inv.app A ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₂) ≫
          (boundedConstructibleUpperStarComp Λ ℓ p' f).hom.app A ≫
          (boundedConstructibleUpperStar Λ ℓ p').map φ) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX p').inv.app K ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj K) h₄) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app K =
    (boundedConstructibleUpperStar Λ ℓ f).map
      ((boundedConstructibleUpperStarComp Λ ℓ ΔY p).inv.app A ≫
        eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₃) ≫
        (boundedConstructibleUpperStarId Λ ℓ Y).hom.app A) ≫ φ := by
  have n₁ := (boundedConstructibleUpperStarComp Λ ℓ ΔX p').inv.naturality φ
  have n₂ := boundedConstructibleUpperStar_map_eqToHom_id Λ ℓ h₄ φ
  have c := boundedConstructibleUpperStarComp_square_coherence Λ ℓ f ΔX ΔY q p p' h₁ h₂ h₃ h₄ A
  simp only [Functor.comp_map] at n₁
  simp only [Functor.map_comp, Category.assoc] at c ⊢
  rw [reassoc_of% n₁, n₂, reassoc_of% c]

variable [IsEllAdicFinitenessCoefficient ℓ Λ]

/-- The monoidality of the composition isomorphisms, inverted. -/
lemma boundedConstructibleUpperStarComp_inv_app_tensor_δ (f : X ⟶ Y) (g : Y ⟶ Z)
    (K M : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ f g).inv.app (K ⊗ M) ≫
        δ (boundedConstructibleUpperStar Λ ℓ (f ≫ g)) K M =
      (boundedConstructibleUpperStar Λ ℓ f).map (δ (boundedConstructibleUpperStar Λ ℓ g) K M) ≫
        δ (boundedConstructibleUpperStar Λ ℓ f) _ _ ≫
        ((boundedConstructibleUpperStarComp Λ ℓ f g).inv.app K ⊗ₘ
          (boundedConstructibleUpperStarComp Λ ℓ f g).inv.app M) := by
  have h := boundedConstructibleUpperStarComp_hom_app_tensor_δ Λ ℓ f g K M
  rw [← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ f g).hom.app (K ⊗ M)),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% h, MonoidalCategory.tensorHom_comp_tensorHom]
  simp

lemma eqToHom_comp_δ_boundedConstructibleUpperStar {r r' : X ⟶ Y} (h : r = r')
    (K M : Dᵇc(Y.left)⟦Λ⟧) :
    eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj (K ⊗ M)) h) ≫
        δ (boundedConstructibleUpperStar Λ ℓ r') K M =
      δ (boundedConstructibleUpperStar Λ ℓ r) K M ≫
        (eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj K) h) ⊗ₘ
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj M) h)) := by
  subst h
  simp

set_option maxHeartbeats 2000000 in
-- the tensor comparisons of composite pullbacks are unfolded
/-- The tensor form of `boundedConstructibleUpperStarComp_square_coherence_comp`: the two
identifications `Lf^* LΔ_Y^* (Lp₁^* A ⊗ Lp₂^* B) ⟶ K ⊗ N` in the square `ΔX ≫ q = f ≫ ΔY` with
`q ≫ pᵢ = p'ᵢ ≫ f`, `ΔY ≫ pᵢ = 𝟙` and `ΔX ≫ p'ᵢ = 𝟙`, through `φ : Lf^* A ⟶ K` and
`ψ : Lf^* B ⟶ N`, agree. -/
lemma boundedConstructibleUpperStarComp_square_coherence_tensor (f : X ⟶ Y) (ΔX : X ⟶ W)
    (ΔY : Y ⟶ Z) (q : W ⟶ Z) (p₁ p₂ : Z ⟶ Y) (p₁' p₂' : W ⟶ X) (h₁ : f ≫ ΔY = ΔX ≫ q)
    (h₂ : q ≫ p₁ = p₁' ≫ f) (h₂' : q ≫ p₂ = p₂' ≫ f) (h₃ : ΔY ≫ p₁ = 𝟙 Y)
    (h₃' : ΔY ≫ p₂ = 𝟙 Y) (h₄ : ΔX ≫ p₁' = 𝟙 X) (h₄' : ΔX ≫ p₂' = 𝟙 X)
    {A B : Dᵇc(Y.left)⟦Λ⟧} {K N : Dᵇc(X.left)⟦Λ⟧}
    (φ : (boundedConstructibleUpperStar Λ ℓ f).obj A ⟶ K)
    (ψ : (boundedConstructibleUpperStar Λ ℓ f).obj B ⟶ N) :
    (boundedConstructibleUpperStarComp Λ ℓ f ΔY).inv.app
        ((boundedConstructibleUpperStar Λ ℓ p₁).obj A ⊗
          (boundedConstructibleUpperStar Λ ℓ p₂).obj B) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ p₁).obj A ⊗
          (boundedConstructibleUpperStar Λ ℓ p₂).obj B)) h₁) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX q).hom.app
        ((boundedConstructibleUpperStar Λ ℓ p₁).obj A ⊗
          (boundedConstructibleUpperStar Λ ℓ p₂).obj B) ≫
      (boundedConstructibleUpperStar Λ ℓ ΔX).map
        (δ (boundedConstructibleUpperStar Λ ℓ q) _ _) ≫
      (boundedConstructibleUpperStar Λ ℓ ΔX).map
        (((boundedConstructibleUpperStarComp Λ ℓ q p₁).inv.app A ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₂) ≫
          (boundedConstructibleUpperStarComp Λ ℓ p₁' f).hom.app A ≫
          (boundedConstructibleUpperStar Λ ℓ p₁').map φ) ⊗ₘ
        ((boundedConstructibleUpperStarComp Λ ℓ q p₂).inv.app B ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj B) h₂') ≫
          (boundedConstructibleUpperStarComp Λ ℓ p₂' f).hom.app B ≫
          (boundedConstructibleUpperStar Λ ℓ p₂').map ψ)) ≫
      δ (boundedConstructibleUpperStar Λ ℓ ΔX) _ _ ≫
      (((boundedConstructibleUpperStarComp Λ ℓ ΔX p₁').inv.app K ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj K) h₄) ≫
          (boundedConstructibleUpperStarId Λ ℓ X).hom.app K) ⊗ₘ
        ((boundedConstructibleUpperStarComp Λ ℓ ΔX p₂').inv.app N ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj N) h₄') ≫
          (boundedConstructibleUpperStarId Λ ℓ X).hom.app N)) =
    (boundedConstructibleUpperStar Λ ℓ f).map
        (δ (boundedConstructibleUpperStar Λ ℓ ΔY) _ _) ≫
      (boundedConstructibleUpperStar Λ ℓ f).map
        (((boundedConstructibleUpperStarComp Λ ℓ ΔY p₁).inv.app A ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₃) ≫
          (boundedConstructibleUpperStarId Λ ℓ Y).hom.app A) ⊗ₘ
        ((boundedConstructibleUpperStarComp Λ ℓ ΔY p₂).inv.app B ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj B) h₃') ≫
          (boundedConstructibleUpperStarId Λ ℓ Y).hom.app B)) ≫
      δ (boundedConstructibleUpperStar Λ ℓ f) _ _ ≫ (φ ⊗ₘ ψ) := by
  rw [← reassoc_of% (δ_natural (boundedConstructibleUpperStar Λ ℓ ΔX) _ _)]
  rw [← reassoc_of% (δ_natural (boundedConstructibleUpperStar Λ ℓ f) _ _)]
  rw [← reassoc_of% (boundedConstructibleUpperStarComp_hom_app_tensor_δ Λ ℓ ΔX q _ _)]
  rw [reassoc_of% (eqToHom_comp_δ_boundedConstructibleUpperStar Λ ℓ h₁
    ((boundedConstructibleUpperStar Λ ℓ p₁).obj A) ((boundedConstructibleUpperStar Λ ℓ p₂).obj B))]
  rw [    reassoc_of% (boundedConstructibleUpperStarComp_inv_app_tensor_δ Λ ℓ f ΔY
    ((boundedConstructibleUpperStar Λ ℓ p₁).obj A) ((boundedConstructibleUpperStar Λ ℓ p₂).obj B))]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [boundedConstructibleUpperStarComp_square_coherence_comp Λ ℓ f ΔX ΔY q p₁ p₁' h₁ h₂ h₃ h₄,
    boundedConstructibleUpperStarComp_square_coherence_comp Λ ℓ f ΔX ΔY q p₂ p₂' h₁ h₂' h₃' h₄']
end Coherence

section Evaluation

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {A B X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The adjoint for `Lp^* ⊣ Rp_*` followed by the cast along `p = p'`. -/
lemma homEquiv_comp_eqToHom_of_eq {p p' : A ⟶ B} (h : p = p')
    {M : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {N : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : (boundedConstructibleUpperStar _ ℓ p).obj M ⟶ N) :
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p).homEquiv _ _ φ ≫
        eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerStar _ ℓ r).obj N) h) =
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p').homEquiv _ _
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj M) h.symm) ≫ φ) := by
  subst h
  simp

/-- The adjoint for `L(f ≫ g)^* ⊣ R(f ≫ g)_*` through the composition isomorphisms. -/
lemma homEquiv_comp_lowerStarComp_hom_app {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (a : X ⟶ Y) (b : Y ⟶ Z)
    {M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : (boundedConstructibleUpperStar _ ℓ a).obj ((boundedConstructibleUpperStar _ ℓ b).obj M) ⟶
      N) :
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ b).homEquiv _ _
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ a).homEquiv _ _ φ) ≫
      (boundedConstructibleLowerStarComp _ ℓ a b).hom.app N =
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (a ≫ b)).homEquiv _ _
      ((boundedConstructibleUpperStarComp _ ℓ a b).hom.app M ≫ φ) :=
  Adjunction.homEquiv_homEquiv_comp_hom_app _ _ _ _ _ rfl φ

/-- The adjoint for `L(f ≫ g)^* ⊣ R(f ≫ g)_*` followed by the inverse composition isomorphism. -/
lemma homEquiv_comp_lowerStarComp_inv_app {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (a : X ⟶ Y) (b : Y ⟶ Z)
    {M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : (boundedConstructibleUpperStar _ ℓ (a ≫ b)).obj M ⟶ N) :
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (a ≫ b)).homEquiv _ _ φ ≫
      (boundedConstructibleLowerStarComp _ ℓ a b).inv.app N =
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ b).homEquiv _ _
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ a).homEquiv _ _
        ((boundedConstructibleUpperStarComp _ ℓ a b).inv.app M ≫ φ)) := by
  rw [← cancel_mono ((boundedConstructibleLowerStarComp _ ℓ a b).hom.app N), Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, homEquiv_comp_lowerStarComp_hom_app,
    Iso.hom_inv_id_app_assoc]

set_option maxHeartbeats 2000000 in
-- TEMP
/-- The identification `LΔ^* (K ⊠ N) ≅ K ⊗ N` is natural in `N`. -/
lemma diagUpperStarExternalProductIso_hom_naturality_right
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {N N' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (χ : N ⟶ N') :
    (boundedConstructibleUpperStar _ ℓ (diag X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj M ◁
          (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map χ) ≫
      (diagUpperStarExternalProductIso ℓ M N').hom =
    (diagUpperStarExternalProductIso ℓ M N).hom ≫ (M ◁ χ) := by
  have h₂ : diag X ≫ (prod.snd : X ⨯ X ⟶ X) = 𝟙 X := by simp [diag]
  have n₁ := (boundedConstructibleUpperStarComp _ ℓ (diag X) (prod.snd : X ⨯ X ⟶ X)).inv.naturality χ
  have n₂ := boundedConstructibleUpperStar_map_eqToHom_id _ ℓ h₂ χ
  simp only [Functor.comp_map] at n₁
  unfold externalProduct at *
  simp only [diagUpperStarExternalProductIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.app_inv, Iso.app_hom, eqToIso.hom, Category.assoc, Functor.Monoidal.μIso_inv]
  have d := δ_natural (boundedConstructibleUpperStar _ ℓ (diag X))
    (𝟙 ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj M))
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map χ)
  rw [← MonoidalCategory.id_tensorHom, ← reassoc_of% d, MonoidalCategory.tensorHom_comp_tensorHom]
  have h : (boundedConstructibleUpperStar _ ℓ (diag X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map χ) ≫
      (boundedConstructibleUpperStarComp _ ℓ (diag X) (prod.snd : X ⨯ X ⟶ X)).inv.app N' ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar _ ℓ u).obj N') h₂) ≫
      (boundedConstructibleUpperStarId _ ℓ X).hom.app N' =
    ((boundedConstructibleUpperStarComp _ ℓ (diag X) (prod.snd : X ⨯ X ⟶ X)).inv.app N ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar _ ℓ u).obj N) h₂) ≫
      (boundedConstructibleUpperStarId _ ℓ X).hom.app N) ≫ χ := by
    simp only [Category.assoc]
    rw [reassoc_of% n₁, n₂]
  exact comp_tensorHom_eq_of_eq _ _ (CategoryTheory.Functor.map_id _ _) _ _ _ _ _ h

end Evaluation

end AlgebraicGeometry.ProEtale.CondensedRing
