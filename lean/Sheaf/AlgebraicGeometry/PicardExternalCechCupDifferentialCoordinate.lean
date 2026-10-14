/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.Paper.CechCupProduct

/-! # The external Alexander--Whitney differential calculation
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-differential).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Assemble specified bidegree maps by the tensor-total coproduct universal property.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cech-cup-differential-coordinate). -/
def picardExternalCechCupDegreeMaps
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q)) :
    ∀ n : ℕ, (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).X n ⟶ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n :=
  fun _n ↦ HomologicalComplex.mapBifunctorDesc
    (fun p q hpq ↦ l p q ≫ eqToHom (congrArg
      (fun j ↦ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X j) hpq))

/-- Each specified bidegree map is recovered by its tensor-total inclusion.
Source: the coproduct universal property, Stacks Project Tag 0BED.
(blueprint: lem-sc-picard-external-cech-cup-differential). -/
theorem picardExternalCechCupDegreeMaps_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (p q : ℕ) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q (p + q) rfl ≫
      picardExternalCechCupDegreeMaps f g U V F G l (p + q) = l p q := by
  dsimp only [picardExternalCechCupDegreeMaps]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp

/- Adjacent differential compatibility. -/
/-- Coordinate differential compatibility for one tensor-total summand.
Source: Stacks Project, Tag 07MB; this is the inclusion-level calculation
used to assemble the total differential identity.
(blueprint: lem-sc-picard-external-cech-cup-differential-coordinate).
Proof: Substitute hpq to work in degree p+q. Tensor-product extensionality reduces the equality
to a pure tensor a tensor b, and Cech product extensionality reduces it to a tuple y of length
p+q+2. Use the degree-map inclusion equation and hl to identify the target coordinates.
Naturality of each pullback adjunction unit identifies pulling a restricted section with
restricting its pullback; presheaf composition identifies successive restrictions, and tensor
sections commute with restriction. In d(a) cup b, the omitted-front terms indexed j=0,...,p
have coefficient (-1)^j and match target faces j=0,...,p. Its final term has coefficient
(-1)^(p+1). In (-1)^p a cup d(b), the first back term has coefficient (-1)^p and is the same
restricted tensor section as that final front term, so they cancel. The remaining back terms
indexed r=1,...,q+1 have coefficient (-1)^(p+r) and match target faces j=p+1,...,p+q+1. These
exhaust the target alternating differential. The tensor-total inclusion differential has
precisely the d(a) tensor b term and the (-1)^p a tensor d(b) term; its inclusion formulas and
the degree-map inclusion equation therefore give the same coordinates. Tensor and product
extensionality conclude the summand equality. The cancellation also applies when p=0 or q=0 and
in characteristic two. Empty index families give vacuous coordinate equalities; zero
coefficients give zero maps. -/
theorem picardExternalCechCupDegreeMaps_comm_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q))
    (n p q : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      picardExternalCechCupDegreeMaps f g U V F G l n ≫
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d n (n + 1) =
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).d n (n + 1) ≫
      picardExternalCechCupDegreeMaps f g U V F G l (n + 1) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
