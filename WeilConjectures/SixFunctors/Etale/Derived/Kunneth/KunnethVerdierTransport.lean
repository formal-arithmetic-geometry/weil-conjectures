/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMapIhom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExceptionalGeneral
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!

# The Künneth–Verdier map and its transport along exceptional inverse images

Fix a scheme `Y`, objects `N` and `ω` of `D(Y_ét)`, and the evaluation pairing
`ev : [N, ω] ⊗ᴸ N ⟶ ω` (`AlgebraicGeometry.Etale.evaluationPairing`). For a morphism
`φ : P ⟶ Y` the pulled back pairing `Lφ^*[N, ω] ⊗ᴸ Lφ^* N ≅ Lφ^*([N, ω] ⊗ᴸ N) ⟶ Lφ^* ω`
(`AlgebraicGeometry.Etale.pulledBackPairing`) has a Künneth map
`S ⊗ᴸ Lφ^*[N, ω] ⟶ RHom(Lφ^* N, S ⊗ᴸ Lφ^* ω)` for every `S ∈ D(P_ét)`
(`CategoryTheory.pairingKunnethMap`). For `P = X ×_k Y`, `φ` the second projection, `ω = ω_Y` and
`S = Lp^* M`, this is the Künneth–Verdier map `κ` of `thm-trf-kunneth-verdier`, up to the
identification `Rp^! M ≅ Lp^* M ⊗ᴸ Lq^* ω_Y`.

Along a morphism `g : P' ⟶ P` admitting a compactification, `Rg^!` carries the Künneth map of `φ`
at `S` to the Künneth map of `g ≫ φ` at `Rg^! S`, provided the tensor maps of `Rg^!` at
`(S, Lφ^*[N, ω])` and `(S, Lφ^* ω)` are invertible
(`AlgebraicGeometry.Etale.isIso_map_pairingKunnethMap_pulledBackPairing_iff`).

The statements are made for a general coefficient category: at `ModuleCat Λ`, instance search for
the internal hom of the derived category is very expensive.

## Main definitions

- `AlgebraicGeometry.Etale.evaluationPairing`, `AlgebraicGeometry.Etale.pulledBackPairing`

## Main statements

- `AlgebraicGeometry.Etale.isIso_map_pairingKunnethMap_iff_of_tensorMap`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product: otherwise the monoidal structures found by instance search differ from the
-- ones of the projection maps, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance] derivedBraidedCategory

variable {Y : Scheme.{u}} (N ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))

variable (A) in
/-- The evaluation pairing `[N, ω] ⊗ᴸ N ⟶ ω`. -/
noncomputable def evaluationPairing : (ihom N).obj ω ⊗ N ⟶ ω :=
  (β_ ((ihom N).obj ω) N).hom ≫ (ihom.ev N).app ω

variable (A) in
/-- The pairing `Lφ^*[N, ω] ⊗ᴸ Lφ^* N ≅ Lφ^*([N, ω] ⊗ᴸ N) ⟶ Lφ^* ω` pulled back along
`φ : P ⟶ Y`. -/
noncomputable def pulledBackPairing {P : Scheme.{u}} (φ : P ⟶ Y) :
    (L((φ)^*[A])).obj ((ihom N).obj ω) ⊗ (L((φ)^*[A])).obj N ⟶ (L((φ)^*[A])).obj ω :=
  inv (leftDerivedUpperStarTensorIso A φ ((ihom N).obj ω) N).hom ≫
    (L((φ)^*[A])).map (evaluationPairing A N ω)

/-- The Künneth map only depends on the morphism `φ`, not on its presentation. -/
lemma isIso_pairingKunnethMap_pulledBackPairing_congr {P : Scheme.{u}} {φ φ' : P ⟶ Y} (h : φ = φ')
    (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A)) :
    IsIso (pairingKunnethMap (pulledBackPairing A N ω φ) S) ↔
      IsIso (pairingKunnethMap (pulledBackPairing A N ω φ') S) := by
  subst h; rfl

/-- The pairing pulled back along `φ` and then along `g` is the pairing pulled back along
`g ≫ φ`, up to the composition isomorphism of derived pullbacks, which is monoidal
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`). -/
lemma isIso_pairingKunnethMap_pulledBackPairing_comp_iff {P P' : Scheme.{u}} (g : P' ⟶ P)
    (φ : P ⟶ Y) (S : _root_.DerivedCategory (Sheaf P'.smallEtaleTopology A)) :
    IsIso (pairingKunnethMap (inv (leftDerivedUpperStarTensorIso A g
        ((L((φ)^*[A])).obj ((ihom N).obj ω)) ((L((φ)^*[A])).obj N)).hom ≫
          (L((g)^*[A])).map (pulledBackPairing A N ω φ)) S) ↔
      IsIso (pairingKunnethMap (pulledBackPairing A N ω (g ≫ φ)) S) := by
  refine isIso_pairingKunnethMap_iff_of_iso_pairing _ _
    ((leftDerivedUpperStarComp A g φ).app N).symm
    ((leftDerivedUpperStarComp A g φ).app _).symm
    ((leftDerivedUpperStarComp A g φ).app ω).symm ?_ S
  have hc := leftDerivedUpperStarTensorComparison_comp A g φ (g ≫ φ) rfl ((ihom N).obj ω) N
  have hn := (leftDerivedUpperStarComp A g φ).inv.naturality (evaluationPairing A N ω)
  simp only [Iso.app_inv, Iso.symm_hom, pulledBackPairing, Functor.map_comp, Category.assoc,
    Functor.comp_map, Functor.map_inv] at hn ⊢
  rw [hn]
  simp only [← leftDerivedUpperStarTensorIso_hom] at hc
  rw [← whisker_exchange_assoc, ← tensorHom_def'_assoc, ← cancel_epi
    (leftDerivedUpperStarTensorIso A g _ _).hom, IsIso.hom_inv_id_assoc]
  rw [← cancel_epi ((L((g)^*[A])).map (leftDerivedUpperStarTensorIso A φ _ _).hom),
    IsIso.hom_inv_id_assoc]
  have hc' : (L((g)^*[A])).map (leftDerivedUpperStarTensorIso A φ ((ihom N).obj ω) N).hom ≫
      (leftDerivedUpperStarTensorIso A g _ _).hom =
        (leftDerivedUpperStarComp A g φ).inv.app _ ≫
          (leftDerivedUpperStarTensorIso A (g ≫ φ) ((ihom N).obj ω) N).hom ≫
          ((leftDerivedUpperStarComp A g φ).hom.app _ ⊗ₘ
            (leftDerivedUpperStarComp A g φ).hom.app _) := by
    rw [hc]; exact ((leftDerivedUpperStarComp A g φ).inv_hom_id_app_assoc _ _).symm
  rw [reassoc_of% hc', tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
    id_tensorHom_id, Category.id_comp, IsIso.hom_inv_id_assoc]
  rfl

section Transport

variable {P P' : Scheme.{u}} (g : P' ⟶ P) [HasCompactification g] [(R(g)_![A]).IsLeftAdjoint]
  [IsIso (projectionMap A g)]

/-- The general transport statement for `Rg^!`, given the associativity of the projection
formula of `Rg_!` (`sk-prop-sf-pf-coherence`). -/
lemma isIso_map_pairingKunnethMap_iff_of_tensorMap (hassoc : ProjectionMapAssociativity A g)
    {K D W : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A)} (ev : D ⊗ K ⟶ W)
    (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A))
    [IsIso (rightDerivedUpperShriekTensorMap g S D)]
    [IsIso (rightDerivedUpperShriekTensorMap g S W)] :
    IsIso ((R(g)^![A]).map (pairingKunnethMap ev S)) ↔
      IsIso (pairingKunnethMap (inv (leftDerivedUpperStarTensorIso A g D K).hom ≫
        (L((g)^*[A])).map ev) ((R(g)^![A]).obj S)) :=
  (rightDerivedUpperShriekAdjunction A g).isIso_map_pairingKunnethMap_iff
    (fun M N ↦ ((projectionMap A g).app M).app N)
    (projectionMap_app_app_naturality_left g) (projectionMap_app_app_naturality_right g)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A g N N').hom) hassoc.assoc ev S

/-- **Transport along `Rg^!`** of the Künneth map of a pulled back pairing: if `τ` is invertible
at `(S, Lφ^*[N, ω])` and `(S, Lφ^* ω)`, then `Rg^!` of the Künneth map of `φ` at `S` is invertible
if and only if the Künneth map of `g ≫ φ` at `Rg^! S` is. -/
lemma isIso_map_pairingKunnethMap_pulledBackPairing_iff (hassoc : ProjectionMapAssociativity A g)
    (φ : P ⟶ Y) (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A))
    [IsIso (rightDerivedUpperShriekTensorMap g S ((L((φ)^*[A])).obj ((ihom N).obj ω)))]
    [IsIso (rightDerivedUpperShriekTensorMap g S ((L((φ)^*[A])).obj ω))] :
    IsIso ((R(g)^![A]).map (pairingKunnethMap (pulledBackPairing A N ω φ) S)) ↔
      IsIso (pairingKunnethMap (pulledBackPairing A N ω (g ≫ φ)) ((R(g)^![A]).obj S)) :=
  (isIso_map_pairingKunnethMap_iff_of_tensorMap g hassoc _ S).trans
    (isIso_pairingKunnethMap_pulledBackPairing_comp_iff N ω g φ _)

/-- **Transport from the base.** The Künneth map of the evaluation pairing at the unit being an
isomorphism, the Künneth map of the pairing pulled back along `φ : P ⟶ Y` at `Rφ^! Λ` is an
isomorphism, provided `τ` is invertible at `(Λ, [N, ω])` and `(Λ, ω)`. -/
lemma isIso_pairingKunnethMap_pulledBackPairing_rightDerivedUpperShriek_unit (φ : P ⟶ Y)
    [HasCompactification φ] [(R(φ)_![A]).IsLeftAdjoint] [IsIso (projectionMap A φ)]
    (hassoc : ProjectionMapAssociativity A φ)
    [IsIso (rightDerivedUpperShriekTensorMap φ (𝟙_ _) ((ihom N).obj ω))]
    [IsIso (rightDerivedUpperShriekTensorMap φ (𝟙_ _) ω)] :
    IsIso (pairingKunnethMap (pulledBackPairing A N ω φ) ((R(φ)^![A]).obj (𝟙_ _))) := by
  have h : IsIso (pairingKunnethMap (evaluationPairing A N ω) (𝟙_ _)) :=
    isIso_pairingKunnethMap_unit N ω
  exact (isIso_map_pairingKunnethMap_iff_of_tensorMap φ hassoc (evaluationPairing A N ω)
    (𝟙_ _)).1 (Functor.map_isIso _ _)

end Transport

section KunnethVerdierMap

/-! The Künneth map of the pulled back evaluation pairing, written with `derivedTensor` and
`derivedHom`, so that it can be used at `A = ModuleCat Λ` without comparing monoidal instances
(see the implementation notes of `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`). -/

variable {P : Scheme.{u}}

variable (A) in
/-- The **Künneth–Verdier map** (`thm-trf-kunneth-verdier`) of `φ : P ⟶ Y` at `S ∈ D(P_ét)`:
`S ⊗ᴸ Lφ^* RHom(N, ω) ⟶ RHom(Lφ^* N, S ⊗ᴸ Lφ^* ω)`, the Künneth map of the pulled back
evaluation pairing. For `φ` the second projection of `X ×_k Y`, `ω = ω_Y` and `S = Lp^* M` it is
the map `κ : M ⊠ 𝔻_Y N ⟶ RHom(p_Y^* N, Lp^* M ⊗ᴸ Lq^* ω_Y)`. -/
noncomputable def kunnethVerdierMap (φ : P ⟶ Y)
    (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A)) :
    ((derivedTensor A P).obj S).obj ((L((φ)^*[A])).obj ((RHom(Y)[A].obj (op N)).obj ω)) ⟶
      (RHom(P)[A].obj (op ((L((φ)^*[A])).obj N))).obj
        (((derivedTensor A P).obj S).obj ((L((φ)^*[A])).obj ω)) :=
  pairingKunnethMap (pulledBackPairing A N ω φ) S

/-- Whether the Künneth–Verdier map is invertible only depends on `S` up to isomorphism
(`thm-trf-kunneth-verdier`). -/
lemma isIso_kunnethVerdierMap_iff_of_iso (φ : P ⟶ Y)
    {S S' : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A)} (e : S ≅ S') :
    IsIso (kunnethVerdierMap A N ω φ S) ↔ IsIso (kunnethVerdierMap A N ω φ S') :=
  isIso_pairingKunnethMap_iff_of_iso _ e

/-- The Künneth–Verdier map only depends on the morphism `φ` (`thm-trf-kunneth-verdier`). -/
lemma isIso_kunnethVerdierMap_congr {φ φ' : P ⟶ Y} (h : φ = φ')
    (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A)) :
    IsIso (kunnethVerdierMap A N ω φ S) ↔ IsIso (kunnethVerdierMap A N ω φ' S) := by
  subst h; rfl

/-- **Transport along `Rg^!`** of the Künneth–Verdier map (`thm-trf-kunneth-verdier`): if the
tensor maps of `Rg^!` at `(S, Lφ^* RHom(N, ω))` and `(S, Lφ^* ω)` are invertible, then `Rg^!` of
the Künneth–Verdier map of `φ` at `S` is invertible if and only if the Künneth–Verdier map of
`g ≫ φ` at `Rg^! S` is. -/
lemma isIso_map_kunnethVerdierMap_iff {P' : Scheme.{u}} (g : P' ⟶ P) [HasCompactification g]
    [(R(g)_![A]).IsLeftAdjoint] [IsIso (projectionMap A g)]
    (hassoc : ProjectionMapAssociativity A g) (φ : P ⟶ Y)
    (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A))
    (h₁ : IsIso (rightDerivedUpperShriekTensorMap g S
      ((L((φ)^*[A])).obj ((RHom(Y)[A].obj (op N)).obj ω))))
    (h₂ : IsIso (rightDerivedUpperShriekTensorMap g S ((L((φ)^*[A])).obj ω))) :
    IsIso ((R(g)^![A]).map (kunnethVerdierMap A N ω φ S)) ↔
      IsIso (kunnethVerdierMap A N ω (g ≫ φ) ((R(g)^![A]).obj S)) :=
  @isIso_map_pairingKunnethMap_pulledBackPairing_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N ω _ _ g _ _
    _ hassoc φ S h₁ h₂

/-- **The Künneth–Verdier map at `Rφ^! Λ`** (`thm-trf-kunneth-verdier`): it is invertible as soon
as the tensor maps of `Rφ^!` at `(Λ, RHom(N, ω))` and `(Λ, ω)` are, being the transport along
`Rφ^!` of the Künneth map of the evaluation pairing at the unit. -/
lemma isIso_kunnethVerdierMap_rightDerivedUpperShriek_unit (φ : P ⟶ Y)
    [HasCompactification φ] [(R(φ)_![A]).IsLeftAdjoint] [IsIso (projectionMap A φ)]
    (hassoc : ProjectionMapAssociativity A φ)
    (h₁ : IsIso (rightDerivedUpperShriekTensorMap φ (𝟙_ _) ((RHom(Y)[A].obj (op N)).obj ω)))
    (h₂ : IsIso (rightDerivedUpperShriekTensorMap φ (𝟙_ _) ω)) :
    IsIso (kunnethVerdierMap A N ω φ ((R(φ)^![A]).obj (𝟙_ _))) :=
  have : IsIso (rightDerivedUpperShriekTensorMap φ (𝟙_ _) ((ihom N).obj ω)) := h₁
  have := h₂
  isIso_pairingKunnethMap_pulledBackPairing_rightDerivedUpperShriek_unit N ω φ hassoc

/-- **Tensoring with a dualizable object** (`thm-trf-kunneth-verdier`): if `D` has a right dual
`F` on `X` and the Künneth–Verdier map of `φ` is invertible at `S`, then it is invertible at
`Lp^* D ⊗ᴸ S` for every `p : P ⟶ X`. -/
lemma isIso_kunnethVerdierMap_derivedTensor_of_exactPairing
    {X : Scheme.{u}} (φ : P ⟶ Y) (p : P ⟶ X)
    (D F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    [ExactPairing D F] (S : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A))
    (h : IsIso (kunnethVerdierMap A N ω φ S)) :
    IsIso (kunnethVerdierMap A N ω φ (((derivedTensor A P).obj ((L((p)^*[A])).obj D)).obj S)) := by
  obtain ⟨_⟩ := nonempty_monoidal_leftDerivedUpperStar A p
  let _ := ExactPairing.map L((p)^*[A]) D F
  have : HasRightDual ((L((p)^*[A])).obj D) := ⟨(L((p)^*[A])).obj F⟩
  have : IsIso (pairingKunnethMap (pulledBackPairing A N ω φ) S) := h
  exact isIso_pairingKunnethMap_tensor_left _ _ _

end KunnethVerdierMap

end Etale

end AlgebraicGeometry
