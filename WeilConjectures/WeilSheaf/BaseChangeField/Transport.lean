/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category

/-!
# Transport of Weil sheaves to a finite extension of the base field

Let `Y` be a `k₀`-scheme and `Y'` a `k₀'`-scheme, and let `θ : Ȳ ≅ Ȳ'` be an isomorphism of
their geometric fibers intertwining the `r`-th power of the geometric Galois Frobenius of `Ȳ`
with that of `Ȳ'`, `θ ≫ Fr' = Frʳ ≫ θ`. A pro-étale Weil sheaf `(K, φ)` on `Y` gives the
pro-étale Weil sheaf `(θ_* K, φ_r)` on `Y'`, whose Weil structure is the `r`-fold iterate of
`φ` (`AlgebraicGeometry.ProEtaleWeilSheaf.frobeniusPowIso`), transported along `θ`:

`Fr'^* θ_* K ≅ θ_* (Frʳ)^* K --θ_* φ_r--> θ_* K`.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.frobeniusPowIso`: the iterated Weil structure
  `φ_m : (Frᵐ)^* K ≅ K` of a pro-étale Weil sheaf.
- `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor`: `(K, φ) ↦ (K, φ_r)`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.transport`: `(K, φ) ↦ (θ_* K, θ_* φ_r)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

noncomputable section

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- The iterated Weil structure `φ_m : (Frᵐ)^* K ≅ K` of a pro-étale Weil sheaf, the ordered
composite `(Fr^{m+1})^* K ≅ Fr^* (Frᵐ)^* K --Fr^* φ_m--> Fr^* K --φ--> K`, with `φ_0` the
identification `𝟙^* K ≅ K`; the pullback along an automorphism `g` is the pushforward along
`g⁻¹`. This is `AlgebraicGeometry.WeilSheaf.frobeniusPowIso` for all pro-étale Weil sheaves. -/
def frobeniusPowIso (K : ProEtaleWeilSheaf k₀ l Y) : (m : ℕ) →
    ((((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv)_*ᵃ[l].obj K.carrier ≅
      K.carrier)
  | 0 => (adicLowerStarCongr l (by rw [pow_zero]; rfl)).app _ ≪≫ (adicLowerStarId l _).app _
  | m + 1 =>
    (adicLowerStarCongr l (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv])).app _ ≪≫
      (adicLowerStarComp l _ _).symm.app _ ≪≫
      (WeilSheaf.frobeniusPullback k₀ l Y).mapIso (K.frobeniusPowIso m) ≪≫ K.str

lemma _root_.AlgebraicGeometry.WeilSheaf.frobeniusPowIso_eq [Fact (ringChar k₀ ≠ l)]
    (F : WeilSheaf k₀ l Y) (m : ℕ) : F.frobeniusPowIso m = F.obj.frobeniusPowIso m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [WeilSheaf.frobeniusPowIso, frobeniusPowIso, ih]

/-- The iterated Weil structures are natural. -/
@[reassoc]
lemma frobeniusPowIso_hom_naturality {K K' : ProEtaleWeilSheaf k₀ l Y} (φ : K ⟶ K') (m : ℕ) :
    (((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv)_*ᵃ[l].map φ.hom.f ≫
        (K'.frobeniusPowIso m).hom =
      (K.frobeniusPowIso m).hom ≫ φ.hom.f := by
  induction m with
  | zero =>
    simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
    erw [NatTrans.naturality_assoc, NatTrans.naturality]
    rfl
  | succ m ih =>
    have h₁ := (WeilSheaf.frobeniusPullback k₀ l Y).congr_map ih
    rw [Functor.map_comp, Functor.map_comp] at h₁
    simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc]
    erw [NatTrans.naturality_assoc, NatTrans.naturality_assoc, reassoc_of% h₁]
    erw [φ.hom.h]
    rfl

variable (k₀ l Y) in
/-- The pushforward `((Frᵐ)⁻¹)_* = (Frᵐ)^*` along the inverse of the `m`-th power of the
geometric Galois Frobenius. -/
abbrev frobeniusPowPullback (m : ℕ) :
    AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  ((((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv)_*ᵃ[l])

variable (k₀ l Y) in
/-- The `r`-th power of a Weil structure: `(K, φ) ↦ (K, φ_r)`, a pro-étale sheaf with an
isomorphism `(Frʳ)^* K ≅ K`. -/
def powFunctor (r : ℕ) :
    ProEtaleWeilSheaf k₀ l Y ⥤ IsoAlgebra (frobeniusPowPullback k₀ l Y r) where
  obj K := IsoAlgebra.mk K.carrier (K.frobeniusPowIso r)
  map φ := ObjectProperty.homMk
    { f := φ.hom.f
      h := frobeniusPowIso_hom_naturality φ r }

@[simp]
lemma powFunctor_obj_carrier (r : ℕ) (K : ProEtaleWeilSheaf k₀ l Y) :
    ((powFunctor k₀ l Y r).obj K).carrier = K.carrier :=
  rfl

@[simp]
lemma powFunctor_obj_str (r : ℕ) (K : ProEtaleWeilSheaf k₀ l Y) :
    ((powFunctor k₀ l Y r).obj K).str = K.frobeniusPowIso r :=
  IsoAlgebra.mk_str _ _

@[simp]
lemma powFunctor_map_hom_f (r : ℕ) {K K' : ProEtaleWeilSheaf k₀ l Y} (φ : K ⟶ K') :
    ((powFunctor k₀ l Y r).map φ).hom.f = φ.hom.f :=
  rfl

instance (r : ℕ) : (powFunctor k₀ l Y r).Additive where

instance (r : ℕ) : PreservesFiniteLimits (powFunctor k₀ l Y r) := by
  have : PreservesFiniteLimits (powFunctor k₀ l Y r ⋙ IsoAlgebra.forget _) :=
    inferInstanceAs (PreservesFiniteLimits (IsoAlgebra.forget _))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

instance (r : ℕ) : PreservesFiniteColimits (powFunctor k₀ l Y r) := by
  have : PreservesFiniteColimits (powFunctor k₀ l Y r ⋙ IsoAlgebra.forget _) :=
    inferInstanceAs (PreservesFiniteColimits (IsoAlgebra.forget _))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

variable {k₀' : Type u} [Field k₀'] [Finite k₀']
  {Y' : Scheme.{u}} [Y'.Over (Spec (CommRingCat.of k₀'))]
  (θ : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.hom =
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)

include hθ in
lemma hom_comp_geometricGaloisFrobenius_inv :
    θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.inv =
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).inv ≫ θ.hom := by
  rw [← cancel_mono (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hθ, Iso.inv_hom_id_assoc]

/-- The commutation `θ_* ⋙ Fr'^* ≅ (Frʳ)^* ⋙ θ_*` of the pushforward along `θ` with the
Frobenius pullbacks, from `θ ≫ Fr'⁻¹ = Fr⁻ʳ ≫ θ`. -/
def transportCommIso :
    (θ.hom)_*ᵃ[l] ⋙ WeilSheaf.frobeniusPullback k₀' l Y' ≅
      frobeniusPowPullback k₀ l Y r ⋙ (θ.hom)_*ᵃ[l] :=
  adicLowerStarComp l _ _ ≪≫ adicLowerStarCongr l (hom_comp_geometricGaloisFrobenius_inv θ r hθ) ≪≫
    (adicLowerStarComp l _ _).symm

/-- The transport `(K, φ) ↦ (θ_* K, θ_* φ_r)` of pro-étale Weil sheaves on `Y` relative to `k₀`
to pro-étale Weil sheaves on `Y'` relative to `k₀'`, along an identification `θ : Ȳ ≅ Ȳ'` of the
geometric fibers with `θ ≫ Fr' = Frʳ ≫ θ`. -/
def transport : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀' l Y' :=
  powFunctor k₀ l Y r ⋙ IsoAlgebra.mapOfNatIso (transportCommIso θ r hθ)

@[simp]
lemma transport_obj_carrier (K : ProEtaleWeilSheaf k₀ l Y) :
    ((transport θ r hθ).obj K).carrier = (θ.hom)_*ᵃ[l].obj K.carrier :=
  rfl

@[simp]
lemma transport_map_hom_f {K K' : ProEtaleWeilSheaf k₀ l Y} (φ : K ⟶ K') :
    ((transport θ r hθ).map φ).hom.f = (θ.hom)_*ᵃ[l].map φ.hom.f :=
  rfl

lemma transport_obj_str (K : ProEtaleWeilSheaf k₀ l Y) :
    ((transport θ r hθ).obj K).str =
      (transportCommIso θ r hθ).app K.carrier ≪≫ (θ.hom)_*ᵃ[l].mapIso (K.frobeniusPowIso r) := by
  rw [transport, Functor.comp_obj, IsoAlgebra.mapOfNatIso_obj_str, powFunctor_obj_str]
  rfl

instance : (transport (l := l) θ r hθ).Additive := by
  unfold transport
  infer_instance

instance : PreservesFiniteLimits (transport (l := l) θ r hθ) := by
  unfold transport
  infer_instance

instance : PreservesFiniteColimits (transport (l := l) θ r hθ) := by
  unfold transport
  infer_instance

end AlgebraicGeometry.ProEtaleWeilSheaf
