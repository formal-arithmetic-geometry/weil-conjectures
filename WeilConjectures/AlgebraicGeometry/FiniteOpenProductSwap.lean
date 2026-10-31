/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOpenProductOperations
import WeilConjectures.AlgebraicGeometry.FiniteOpenProductRestriction
import WeilConjectures.AlgebraicGeometry.FiniteOpenProductSwapRestriction

/-! # Finite open external products and signed factor swap

Source: Stacks 0GL1, and the open-product part of blueprint main-20261015,
sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md.
(blueprint: lem-pur-finite-open-product-swap).

We use the fixed-scalar presentation `FiniteD` of the ordinary constant-coefficient
module derived category, with its canonical intrinsic realization from the open
normalization dependency. Exact inverse image is localized termwise and identified
with its K-flat left derived functor. Tensor and symmetry are the K-flat ones.

## Main definitions and statement

- `comparison` and `comparisonOp`: the two specified factorization chains.
- `transportedReverse`: the reversed construction transported by the actual swaps.
- `restrictionSource`: the identification supplied by the two specified open units.
- `finiteOpenProductSwap`: invertibility, restriction, equality and the signed swap equation.

`product` names Mathlib's chosen pullback without unfolding its construction during
kernel checking. Its two projections and swap are the existing Mathlib morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace WeilConjectures.FiniteOpenProduct

variable (A : Type (u + 1)) [CommRing A] [Finite A]

omit [Finite A] in
private theorem sigma_iso (Y : Scheme.{u}) (M N : FiniteD A Y) :
    IsIso (sigma A Y M N) := by
  unfold sigma proetSigma
  infer_instance
private theorem gamma_iso {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (M : FiniteD A U) (N : FiniteD A Y) : IsIso (gamma A j M N) := by
  unfold gamma finiteGamma
  infer_instance
private theorem rho_iso {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (M : FiniteD A Y) (N : FiniteD A U) : IsIso (rho A j M N) := by
  have := sigma_iso A Y M ((finiteShriek A j).obj N)
  have := gamma_iso A j N M
  have := sigma_iso A U N ((pull A j).obj M)
  unfold rho
  infer_instance
private theorem supported_restriction_injective
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {E : D} {K : C} (e : E ⟶ L.obj K) [IsIso e]
    {F : D} {x y : E ⟶ F} (h : R.map x = R.map y) : x = y := by
  apply (cancel_epi (inv e)).1
  apply (a.homEquiv K F).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, h]

private theorem leftComparison_iso {Xb Zb B X : Scheme.{u}}
    (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) [IsOpenImmersion j]
    (M : FiniteD A X) (N : FiniteD A Zb) : IsIso (leftComparison A a b j M N) := by
  have := gamma_iso A (leftOpen a b j) ((pull A (first (j ≫ a) b)).obj M)
    ((pull A (second a b)).obj N)
  unfold leftComparison leftBeta extendedProjectionTensor projectionTensor tensorMap
  infer_instance

private theorem rightComparison_iso {Xb Zb B Z : Scheme.{u}}
    (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb) [IsOpenImmersion k]
    (M : FiniteD A Xb) (N : FiniteD A Z) : IsIso (rightComparison A a b k M N) := by
  have := rho_iso A (rightOpen a b k) ((pull A (first a b)).obj M)
    ((pull A (second a (k ≫ b))).obj N)
  unfold rightComparison tensorMap
  infer_instance

private theorem comparison_iso {Xb Zb B X Z : Scheme.{u}}
    (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : FiniteD A X) (N : FiniteD A Z) :
    IsIso (comparison A a b j k M N) := by
  have := leftComparison_iso A a b j M ((finiteShriek A k).obj N)
  have := rightComparison_iso A (j ≫ a) b k M N
  unfold comparison
  infer_instance

private theorem comparisonOp_iso {Xb Zb B X Z : Scheme.{u}}
    (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : FiniteD A X) (N : FiniteD A Z) :
    IsIso (comparisonOp A a b j k M N) := by
  have := rightComparison_iso A a b k ((finiteShriek A j).obj M) N
  have := leftComparison_iso A a (k ≫ b) j M N
  unfold comparisonOp
  infer_instance

private theorem restrictionSource_iso {Xb Zb B X Z : Scheme.{u}}
    (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : FiniteD A X) (N : FiniteD A Z) :
    IsIso (restrictionSource A a b j k M N) := by
  have : IsIso (adj A j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
  have : IsIso (adj A k).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
  unfold restrictionSource tensorMap
  infer_instance


/-- Both actual external-product maps are isomorphisms, restrict to the identity,
agree, and commute with the actual product swap and signed tensor symmetry.
Source: Stacks 0GL1 and the open-product signed-symmetry reduction in blueprint
main-20261015, lem-sf-kunneth-coherence.proof.md
(blueprint: lem-pur-finite-open-product-swap).

Proof: (1) The fibre-product projection equations give the four Cartesian squares;
base change makes all four factor inclusions open. (2) The compositor is the unique
mate of restriction composition. Its unit is the composite of the two open units,
so its restriction is identity. (3) The right-extension tensor map is symmetry,
then gamma, then extension of symmetry. Its restriction is identity since the two
Koszul signs multiply to (-1)^(ab+ba)=1. (4) The definition of comparison is beta
for j, gamma for v, then inside v-shriek beta for k and rho for w, then the
compositor. All factors are invertible by openTensorNormalization. (5) Restricting
this chain gives identity at each stage; product/tensor composition coherence
identifies the result with the displayed unit equation. (6) comparisonOp uses the
other factorization: beta for k, rho for v-prime, then beta for j and gamma for
w-prime, and its compositor. Its restriction gives the same unit equation.
(7) To compare maps E to u-shriek D, compose with comparison inverse. Full
faithfulness of u-shriek and naturality of its invertible unit show that equal
restrictions imply equality. (8) Apply the construction with the two factors
interchanged and pull back by the actual two fibre-product symmetries. Normalized
base change identifies its restriction with identity on the reversed tensor.
(9) Conjugate with both signed symmetries. Their restrictions cancel, so Step 7
gives the final equation of actual maps. The cochain sign computation and K-flat
descent apply to arbitrary unbounded objects, including odd degrees. -/
theorem finiteOpenProductSwap (S : PurityFiniteSetting.{u})
    (Xb Zb B X Z : Over (Spec (CommRingCat.of S.field.k)))
    [IsSeparated Xb.hom] [LocallyOfFiniteType Xb.hom] [QuasiCompact Xb.hom]
    [IsSeparated Zb.hom] [LocallyOfFiniteType Zb.hom] [QuasiCompact Zb.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (a : Xb ⟶ B) (b : Zb ⟶ B)
    [IsSeparated a.left] [LocallyOfFiniteType a.left] [QuasiCompact a.left]
    [IsSeparated b.left] [LocallyOfFiniteType b.left] [QuasiCompact b.left]
    (j : X ⟶ Xb) (k : Z ⟶ Zb) [IsOpenImmersion j.left] [IsOpenImmersion k.left]
    (M : FiniteD S.Coefficient X.left) (N : FiniteD S.Coefficient Z.left) :
    IsIso (comparison S.Coefficient a.left b.left j.left k.left M N) ∧
    IsIso (comparisonOp S.Coefficient a.left b.left j.left k.left M N) ∧
    (restrictionSource S.Coefficient a.left b.left j.left k.left M N ≫
      (pull S.Coefficient (productOpen a.left b.left j.left k.left)).map
        (comparison S.Coefficient a.left b.left j.left k.left M N) =
      (adj S.Coefficient (productOpen a.left b.left j.left k.left)).unit.app
        (tensor S.Coefficient (product (j.left ≫ a.left) (k.left ≫ b.left))
          ((pull S.Coefficient (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)
          ((pull S.Coefficient (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N))) ∧
    (restrictionSource S.Coefficient a.left b.left j.left k.left M N ≫
      (pull S.Coefficient (productOpen a.left b.left j.left k.left)).map
        (comparisonOp S.Coefficient a.left b.left j.left k.left M N) =
      (adj S.Coefficient (productOpen a.left b.left j.left k.left)).unit.app
        (tensor S.Coefficient (product (j.left ≫ a.left) (k.left ≫ b.left))
          ((pull S.Coefficient (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)
          ((pull S.Coefficient (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N))) ∧
    comparison S.Coefficient a.left b.left j.left k.left M N =
      comparisonOp S.Coefficient a.left b.left j.left k.left M N ∧
    comparison S.Coefficient a.left b.left j.left k.left M N =
      sigma S.Coefficient _ _ _ ≫
        transportedReverse S.Coefficient a.left b.left j.left k.left M N ≫
          (finiteShriek S.Coefficient (productOpen a.left b.left j.left k.left)).map
            (sigma S.Coefficient _ ((pull S.Coefficient
                (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N)
              ((pull S.Coefficient
                (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)) := by
  have h1 := comparison_iso S.Coefficient a.left b.left j.left k.left M N
  have h2 := comparisonOp_iso S.Coefficient a.left b.left j.left k.left M N
  obtain ⟨h3, h4⟩ := finiteOpenProductRestriction S Xb Zb B X Z a b j k M N
  have h5 := finiteOpenProductSwapRestriction S Xb Zb B X Z a b j k M N
  have := restrictionSource_iso S.Coefficient a.left b.left j.left k.left M N
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · apply supported_restriction_injective
      (adj S.Coefficient (productOpen a.left b.left j.left k.left))
      (comparison S.Coefficient a.left b.left j.left k.left M N)
    exact (cancel_epi (restrictionSource S.Coefficient a.left b.left j.left k.left M N)).1
      (h3.trans h4.symm)
  · apply supported_restriction_injective
      (adj S.Coefficient (productOpen a.left b.left j.left k.left))
      (comparison S.Coefficient a.left b.left j.left k.left M N)
    exact (cancel_epi (restrictionSource S.Coefficient a.left b.left j.left k.left M N)).1
      (h3.trans h5.symm)


end WeilConjectures.FiniteOpenProduct
