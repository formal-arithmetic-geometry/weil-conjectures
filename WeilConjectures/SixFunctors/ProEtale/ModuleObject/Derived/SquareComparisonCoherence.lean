/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

/-!
# Coherence of the pullback comparisons of derived pullbacks

For a commutative square `g' ≫ p = p' ≫ g` of schemes, the pullback comparison
`θ_sq : Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*` (`ProEtale.CondensedRing.pullbackSquareComparison`) of the
derived pullbacks of module objects satisfies the following coherences:

- `ProEtale.CondensedRing.pullbackSquareComparison_flip`: the comparison of the transposed square
  is the inverse comparison;
- `ProEtale.CondensedRing.pullbackSquareComparison_cube`: for a commutative cube, the two
  composites of the comparisons of the faces agree;
- `ProEtale.CondensedRing.pullbackSquareComparison_tensor`: the comparison is monoidal, i.e.
  compatible with the tensor comparisons of the derived pullbacks.

The proofs are diagram chases for abstract families of functors with composition isomorphisms
satisfying the associativity law, where the computations are cheap, specialized to the derived
pullbacks of module objects.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

/-- The composition isomorphism `c a h` composed with `(U a).map` of an `eqToHom` in the second
argument, for an abstract family of functors `U` with composition isomorphisms `c`. -/
private lemma comp_hom_app_map_eqToHom_aux {𝒞 : Type*} [Category 𝒞] {D : 𝒞 → Type*}
    [∀ S, Category (D S)] (U : ∀ {S T : 𝒞}, (S ⟶ T) → D T ⥤ D S)
    (c : ∀ {R S T : 𝒞} (a : R ⟶ S) (b : S ⟶ T), U (a ≫ b) ≅ U b ⋙ U a)
    {R S T : 𝒞} (a : R ⟶ S) {h h' : S ⟶ T} (e : h = h') (K : D T) :
    (c a h).hom.app K ≫ (U a).map (eqToHom (congrArg (fun r ↦ (U r).obj K) e)) =
      eqToHom (congrArg (fun r ↦ (U (a ≫ r)).obj K) e) ≫ (c a h').hom.app K := by
  subst e
  simp

/-- The composition isomorphism `c h b` composed with an `eqToHom` in the first argument, for an
abstract family of functors `U` with composition isomorphisms `c`. -/
private lemma comp_hom_app_eqToHom_aux {𝒞 : Type*} [Category 𝒞] {D : 𝒞 → Type*}
    [∀ S, Category (D S)] (U : ∀ {S T : 𝒞}, (S ⟶ T) → D T ⥤ D S)
    (c : ∀ {R S T : 𝒞} (a : R ⟶ S) (b : S ⟶ T), U (a ≫ b) ≅ U b ⋙ U a)
    {R S T : 𝒞} {h h' : R ⟶ S} (e : h = h') (b : S ⟶ T) (K : D T) :
    (c h b).hom.app K ≫ eqToHom (congrArg (fun r ↦ (U r).obj ((U b).obj K)) e) =
      eqToHom (congrArg (fun r ↦ (U (r ≫ b)).obj K) e) ≫ (c h' b).hom.app K := by
  subst e
  simp

/-- `(U a).map θ_sq` in terms of the triple composition isomorphisms, for abstract pullback
comparisons `θ`. -/
private lemma map_square_aux {𝒞 : Type*} [Category 𝒞] {D : 𝒞 → Type*}
    [∀ S, Category (D S)] (U : ∀ {S T : 𝒞}, (S ⟶ T) → D T ⥤ D S)
    (c : ∀ {R S T : 𝒞} (a : R ⟶ S) (b : S ⟶ T), U (a ≫ b) ≅ U b ⋙ U a)
    (θ : ∀ {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X},
      CommSq g' p' p g → (U g ⋙ U p' ≅ U p ⋙ U g'))
    (hθ : ∀ {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
      (sq : CommSq g' p' p g) (K : D Y), (θ sq).hom.app K =
        (c p' g).inv.app K ≫ eqToHom (congrArg (fun r ↦ (U r).obj K) sq.w.symm) ≫
          (c g' p).hom.app K)
    {W X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) (a : W ⟶ X') (K : D Y) :
    (c a (p' ≫ g)).hom.app K ≫ (U a).map ((c p' g).hom.app K) ≫ (U a).map ((θ sq).hom.app K) =
      eqToHom (congrArg (fun r ↦ (U (a ≫ r)).obj K) sq.w.symm) ≫
        (c a (g' ≫ p)).hom.app K ≫ (U a).map ((c g' p).hom.app K) := by
  rw [hθ, ← (U a).map_comp, Iso.hom_inv_id_app_assoc, (U a).map_comp,
    reassoc_of% (comp_hom_app_map_eqToHom_aux U c a sq.w.symm K)]

/-- `θ_sq` at `(U b).obj K` in terms of the triple composition isomorphisms, for abstract
pullback comparisons `θ`. -/
private lemma square_app_obj_aux {𝒞 : Type*} [Category 𝒞] {D : 𝒞 → Type*}
    [∀ S, Category (D S)] (U : ∀ {S T : 𝒞}, (S ⟶ T) → D T ⥤ D S)
    (c : ∀ {R S T : 𝒞} (a : R ⟶ S) (b : S ⟶ T), U (a ≫ b) ≅ U b ⋙ U a)
    (A : ∀ {R S T V : 𝒞} (a : R ⟶ S) (b : S ⟶ T) (d : T ⟶ V) (K : D V),
      (c (a ≫ b) d).hom.app K ≫ (c a b).hom.app ((U d).obj K) =
        eqToHom (congrArg (fun r ↦ (U r).obj K) (Category.assoc a b d)) ≫
          (c a (b ≫ d)).hom.app K ≫ (U a).map ((c b d).hom.app K))
    (θ : ∀ {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X},
      CommSq g' p' p g → (U g ⋙ U p' ≅ U p ⋙ U g'))
    (hθ : ∀ {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
      (sq : CommSq g' p' p g) (K : D Y), (θ sq).hom.app K =
        (c p' g).inv.app K ≫ eqToHom (congrArg (fun r ↦ (U r).obj K) sq.w.symm) ≫
          (c g' p).hom.app K)
    {X Y X' Y' V : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) (b : Y ⟶ V) (K : D V) :
    (c p' (g ≫ b)).hom.app K ≫ (U p').map ((c g b).hom.app K) ≫
        (θ sq).hom.app ((U b).obj K) =
      eqToHom (congrArg (fun r ↦ (U r).obj K)
          (by rw [← Category.assoc, ← sq.w, Category.assoc] : p' ≫ g ≫ b = g' ≫ p ≫ b)) ≫
        (c g' (p ≫ b)).hom.app K ≫ (U g').map ((c p b).hom.app K) := by
  have A₁ := (eqToHom_comp_iff _ _ _).1 (A p' g b K).symm
  have A₂ := A g' p b K
  rw [reassoc_of% A₁, hθ, Iso.hom_inv_id_app_assoc,
    reassoc_of% (comp_hom_app_eqToHom_aux U c sq.w.symm b K), A₂]
  simp

/-- The pullback comparison of the transposed square is the inverse, for abstract pullback
comparisons `θ`. -/
private lemma flip_aux {𝒞 : Type*} [Category 𝒞] {D : 𝒞 → Type*}
    [∀ S, Category (D S)] (U : ∀ {S T : 𝒞}, (S ⟶ T) → D T ⥤ D S)
    (c : ∀ {R S T : 𝒞} (a : R ⟶ S) (b : S ⟶ T), U (a ≫ b) ≅ U b ⋙ U a)
    (θ : ∀ {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X},
      CommSq g' p' p g → (U g ⋙ U p' ≅ U p ⋙ U g'))
    (hθ : ∀ {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
      (sq : CommSq g' p' p g) (K : D Y), (θ sq).hom.app K =
        (c p' g).inv.app K ≫ (eqToHom (congrArg (fun r ↦ U r) sq.w.symm)).app K ≫
          (c g' p).hom.app K)
    {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) (K : D Y) :
    (θ sq.flip).hom.app K = (θ sq).inv.app K := by
  simp only [eqToHom_app] at hθ
  rw [← cancel_epi ((θ sq).hom.app K), Iso.hom_inv_id_app, hθ, hθ]
  simp

/-- The cube coherence of abstract pullback comparisons `θ`. -/
private lemma cube_aux {𝒞 : Type*} [Category 𝒞] {D : 𝒞 → Type*}
    [∀ S, Category (D S)] (U : ∀ {S T : 𝒞}, (S ⟶ T) → D T ⥤ D S)
    (c : ∀ {R S T : 𝒞} (a : R ⟶ S) (b : S ⟶ T), U (a ≫ b) ≅ U b ⋙ U a)
    (A : ∀ {R S T V : 𝒞} (a : R ⟶ S) (b : S ⟶ T) (d : T ⟶ V) (K : D V),
      (c (a ≫ b) d).hom.app K ≫ (c a b).hom.app ((U d).obj K) =
        eqToHom (congrArg (fun r ↦ (U r).obj K) (Category.assoc a b d)) ≫
          (c a (b ≫ d)).hom.app K ≫ (U a).map ((c b d).hom.app K))
    (θ : ∀ {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X},
      CommSq g' p' p g → (U g ⋙ U p' ≅ U p ⋙ U g'))
    (hθ : ∀ {X Y X' Y' : 𝒞} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
      (sq : CommSq g' p' p g) (K : D Y), (θ sq).hom.app K =
        (c p' g).inv.app K ≫ (eqToHom (congrArg (fun r ↦ U r) sq.w.symm)).app K ≫
          (c g' p).hom.app K)
    {P' M' P₁' M₁' P M P₁ M₁ : 𝒞} {iP : P' ⟶ P} {iM : M' ⟶ M} {iP₁ : P₁' ⟶ P₁}
    {iM₁ : M₁' ⟶ M₁} {f' : P' ⟶ M'} {g' : M' ⟶ M₁'} {k' : P' ⟶ P₁'} {e' : P₁' ⟶ M₁'}
    {f : P ⟶ M} {g : M ⟶ M₁} {k : P ⟶ P₁} {e : P₁ ⟶ M₁}
    (top : CommSq f' k' g' e') (bot : CommSq f k g e) (sf : CommSq iP f' f iM)
    (sg : CommSq iM g' g iM₁) (sk : CommSq iP k' k iP₁) (se : CommSq iP₁ e' e iM₁) (K : D M₁) :
    (θ top).hom.app ((U iM₁).obj K) ≫ (U f').map ((θ sg).hom.app K) ≫
        (θ sf).hom.app ((U g).obj K) =
      (U k').map ((θ se).hom.app K) ≫ (θ sk).hom.app ((U e).obj K) ≫
        (U iP).map ((θ bot).hom.app K) := by
  simp only [eqToHom_app] at hθ
  rw [← cancel_epi ((c k' (e' ≫ iM₁)).hom.app K ≫ (U k').map ((c e' iM₁).hom.app K))]
  simp only [Category.assoc]
  rw [reassoc_of% (square_app_obj_aux U c A θ hθ top iM₁ K),
    reassoc_of% (map_square_aux U c θ hθ sg f' K),
    square_app_obj_aux U c A θ hθ sf g K,
    reassoc_of% (map_square_aux U c θ hθ se k' K),
    reassoc_of% (square_app_obj_aux U c A θ hθ sk e K),
    map_square_aux U c θ hθ bot iP K]
  simp

/-- The monoidality of an abstract pullback comparison, as a diagram chase in a monoidal
category. -/
private lemma tensor_aux {C : Type*} [Category C] [MonoidalCategory C]
    {x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂ u v w a₁ a₂ : C}
    (cAB : x₀ ≅ x₁) (cA : y₀ ≅ y₁) (cB : z₀ ≅ z₁) (m₀ : x₀ ⟶ y₀ ⊗ z₀)
    (Mg : x₁ ⟶ a₁) (Mp' : a₁ ⟶ y₁ ⊗ z₁)
    (T₁ : m₀ ≫ (cA.hom ⊗ₘ cB.hom) = cAB.hom ≫ Mg ≫ Mp')
    (c'AB : u ≅ x₂) (c'A : v ≅ y₂) (c'B : w ≅ z₂) (m₁ : u ⟶ v ⊗ w)
    (Mp : x₂ ⟶ a₂) (Mg' : a₂ ⟶ y₂ ⊗ z₂)
    (T₂ : m₁ ≫ (c'A.hom ⊗ₘ c'B.hom) = c'AB.hom ≫ Mp ≫ Mg')
    (eAB : x₀ ⟶ u) (eA : y₀ ⟶ v) (eB : z₀ ⟶ w) (hE : m₀ ≫ (eA ⊗ₘ eB) = eAB ≫ m₁)
    (θAB : x₁ ⟶ x₂) (θA : y₁ ⟶ y₂) (θB : z₁ ⟶ z₂) (hAB : θAB = cAB.inv ≫ eAB ≫ c'AB.hom)
    (hA : θA = cA.inv ≫ eA ≫ c'A.hom) (hB : θB = cB.inv ≫ eB ≫ c'B.hom) :
    Mg ≫ Mp' ≫ (θA ⊗ₘ θB) = θAB ≫ Mp ≫ Mg' := by
  rw [← cancel_epi cAB.hom, ← reassoc_of% T₁, hA, hB, hAB, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, ← tensorHom_comp_tensorHom, reassoc_of% hE, T₂]
  simp

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

lemma testT1 (sq : CommSq g' p' p g) :
    (pullbackSquareComparison Λ sq).hom =
      (leftDerivedUpperStarComp Λ p' g).inv ≫ eqToHom (by rw [sq.w]) ≫
        (leftDerivedUpperStarComp Λ g' p).hom :=
  rfl

lemma testT2 (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app K =
      (leftDerivedUpperStarComp Λ p' g).inv.app K ≫
        (eqToHom (congrArg (fun (r : X' ⟶ Y) ↦ L((r)^*⟦Λ⟧)) sq.w.symm)).app K ≫
        (leftDerivedUpperStarComp Λ g' p).hom.app K := by
  rw [testT1]
  rfl

lemma testT3 (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app K =
      (leftDerivedUpperStarComp Λ p' g).inv.app K ≫
        eqToHom (by rw [sq.w]) ≫
        (leftDerivedUpperStarComp Λ g' p).hom.app K := by
  rw [testT1, NatTrans.comp_app, NatTrans.comp_app, eqToHom_app]

lemma testT5 {h h' : X' ⟶ Y} (e : h = h')
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    ((leftDerivedUpperStarTensor Λ h).app A).app B ≫
        ((eqToHom (congrArg (fun (r : X' ⟶ Y) ↦ L((r)^*⟦Λ⟧)) e)).app A ⊗ₘ
          (eqToHom (congrArg (fun (r : X' ⟶ Y) ↦ L((r)^*⟦Λ⟧)) e)).app B) =
      (eqToHom (congrArg (fun (r : X' ⟶ Y) ↦ L((r)^*⟦Λ⟧)) e)).app (A ⊗ B) ≫
        ((leftDerivedUpperStarTensor Λ h').app A).app B := by
  sorry

lemma testT6 {h h' : X' ⟶ Y} (e : h = h')
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    ((leftDerivedUpperStarTensor Λ h).app A).app B ≫
        (eqToHom (by rw [e]) ⊗ₘ eqToHom (by rw [e])) =
      eqToHom (by rw [e]) ≫ ((leftDerivedUpperStarTensor Λ h').app A).app B := by
  subst e
  simp only [eqToHom_refl, id_tensorHom_id, Category.comp_id, Category.id_comp]

/-- The components of the pullback comparison. -/
lemma pullbackSquareComparison_hom_app (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app K =
      (leftDerivedUpperStarComp Λ p' g).inv.app K ≫
        (eqToHom (congrArg (fun (r : X' ⟶ Y) ↦ L((r)^*⟦Λ⟧)) sq.w.symm)).app K ≫
        (leftDerivedUpperStarComp Λ g' p).hom.app K :=
  sorry

/-- The pullback comparison of the transposed square is the inverse of the pullback
comparison. -/
lemma pullbackSquareComparison_flip (sq : CommSq g' p' p g) :
    pullbackSquareComparison Λ sq.flip = (pullbackSquareComparison Λ sq).symm := by
  sorry

/-- The tensor comparison of the derived pullback along `h` composed with `eqToHom`s induced by
an equality `h = h'`. -/
lemma leftDerivedUpperStarTensor_app_app_comp_eqToHom {h h' : X' ⟶ Y} (e : h = h')
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    ((leftDerivedUpperStarTensor Λ h).app A).app B ≫
        ((eqToHom (congrArg (fun (r : X' ⟶ Y) ↦ L((r)^*⟦Λ⟧)) e)).app A ⊗ₘ
          (eqToHom (congrArg (fun (r : X' ⟶ Y) ↦ L((r)^*⟦Λ⟧)) e)).app B) =
      (eqToHom (congrArg (fun (r : X' ⟶ Y) ↦ L((r)^*⟦Λ⟧)) e)).app (A ⊗ B) ≫
        ((leftDerivedUpperStarTensor Λ h').app A).app B := by
  subst e
  rw [eqToHom_refl, NatTrans.id_app, NatTrans.id_app, NatTrans.id_app, id_tensorHom_id,
    Category.comp_id, Category.id_comp]

/-- **The pullback comparison is monoidal**: it is compatible with the tensor comparisons
`m : Lf^* (K ⊗ᴸ M) ⟶ Lf^* K ⊗ᴸ Lf^* M` of the derived pullbacks. -/
lemma pullbackSquareComparison_tensor (sq : CommSq g' p' p g)
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((p')^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ g).app A).app B) ≫
        ((leftDerivedUpperStarTensor Λ p').app _).app _ ≫
        ((pullbackSquareComparison Λ sq).hom.app A ⊗ₘ (pullbackSquareComparison Λ sq).hom.app B) =
      (pullbackSquareComparison Λ sq).hom.app (A ⊗ B) ≫
        L((g')^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ p).app A).app B) ≫
        ((leftDerivedUpperStarTensor Λ g').app _).app _ :=
  tensor_aux ((leftDerivedUpperStarComp Λ p' g).app (A ⊗ B))
    ((leftDerivedUpperStarComp Λ p' g).app A) ((leftDerivedUpperStarComp Λ p' g).app B) _ _ _
    (leftDerivedUpperStarTensor_comp Λ p' g A B)
    ((leftDerivedUpperStarComp Λ g' p).app (A ⊗ B))
    ((leftDerivedUpperStarComp Λ g' p).app A) ((leftDerivedUpperStarComp Λ g' p).app B) _ _ _
    (leftDerivedUpperStarTensor_comp Λ g' p A B) _ _ _
    (leftDerivedUpperStarTensor_app_app_comp_eqToHom Λ sq.w.symm A B) _ _ _
    (pullbackSquareComparison_hom_app Λ sq (A ⊗ B)) (pullbackSquareComparison_hom_app Λ sq A)
    (pullbackSquareComparison_hom_app Λ sq B)

end BaseChange

section Cube

variable {P' M' P₁' M₁' P M P₁ M₁ : Scheme.{u}} {iP : P' ⟶ P} {iM : M' ⟶ M} {iP₁ : P₁' ⟶ P₁}
  {iM₁ : M₁' ⟶ M₁} {f' : P' ⟶ M'} {g' : M' ⟶ M₁'} {k' : P' ⟶ P₁'} {e' : P₁' ⟶ M₁'}
  {f : P ⟶ M} {g : M ⟶ M₁} {k : P ⟶ P₁} {e : P₁ ⟶ M₁}

/-- **Cube coherence of the pullback comparisons**: for a commutative cube of schemes with top
face `top`, bottom face `bot` and side faces `sf`, `sg`, `sk`, `se`, the two composites
`Lk'^* Le'^* LiM₁^* ⟶ LiP^* Lf^* Lg^*` of the pullback comparisons of the faces agree. -/
lemma pullbackSquareComparison_cube (top : CommSq f' k' g' e') (bot : CommSq f k g e)
    (sf : CommSq iP f' f iM) (sg : CommSq iM g' g iM₁) (sk : CommSq iP k' k iP₁)
    (se : CommSq iP₁ e' e iM₁)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology M₁) Ab.{u + 1}) (condensedRingObj Λ M₁))) :
    (pullbackSquareComparison Λ top).hom.app (L((iM₁)^*⟦Λ⟧).obj K) ≫
        L((f')^*⟦Λ⟧).map ((pullbackSquareComparison Λ sg).hom.app K) ≫
        (pullbackSquareComparison Λ sf).hom.app (L((g)^*⟦Λ⟧).obj K) =
      L((k')^*⟦Λ⟧).map ((pullbackSquareComparison Λ se).hom.app K) ≫
        (pullbackSquareComparison Λ sk).hom.app (L((e)^*⟦Λ⟧).obj K) ≫
        L((iP)^*⟦Λ⟧).map ((pullbackSquareComparison Λ bot).hom.app K) :=
  cube_aux (fun f ↦ L((f)^*⟦Λ⟧)) (fun a b ↦ leftDerivedUpperStarComp Λ a b)
    (fun a b d K ↦ leftDerivedUpperStarComp_assoc_app Λ a b d K)
    (fun sq ↦ pullbackSquareComparison Λ sq) (fun sq K ↦ pullbackSquareComparison_hom_app Λ sq K)
    top bot sf sg sk se K

end Cube

end AlgebraicGeometry.ProEtale.CondensedRing
