/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularDualizingTwistCancellation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameClass
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality

/-! # The supported class obtained by contracting an oriented affine projection

Source: sk-thm-regular.proof.md, Step 4(iii). The orientation is input data.
The exceptional compositor and identity unitor determine the contraction.
(blueprint: def-pur-regular-projection-supported-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)]

/-- The contraction of a specified orientation by the zero section. All factors are
specified isomorphisms: exceptional image of the orientation, composition, and the
exceptional identity unitor. Source: sk-thm-regular.proof.md, Step 4(iii)
(blueprint: def-pur-regular-projection-supported-class). -/
def regularProjectionContraction (B : Scheme.{u}) (c : ℕ)
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B)]
    (α : dualizingComplex Λ (𝔸(ULift.{u} (Fin c); B) ↘ B) ≅
      (tateObject Λ 𝔸(ULift.{u} (Fin c); B) c)⟦2 * (c : ℤ)⟧) :
    (R(AffineSpace.zeroSection (ULift.{u} (Fin c)) B)^![Λ]).obj
      ((tateObject Λ 𝔸(ULift.{u} (Fin c); B) c)⟦2 * (c : ℤ)⟧) ≅
      constantComplex Λ B := by
  let X := 𝔸(ULift.{u} (Fin c); B)
  let p : X ⟶ B := X ↘ B
  let z := AffineSpace.zeroSection (ULift.{u} (Fin c)) B
  have hzp : z ≫ p = 𝟙 B := AffineSpace.zeroSection_comp_over (ULift.{u} (Fin c)) B
  letI : HasCompactification (z ≫ p) := by rw [hzp]; infer_instance
  let u₀ := ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition Λ z p).app
    (constantComplex Λ B)).symm
  let u₁ := (rightDerivedUpperShriekCongr Λ
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin c)) B)).app (constantComplex Λ B) ≪≫
      (rightDerivedUpperShriekIdIso Λ B).app (constantComplex Λ B)
  exact (rightDerivedUpperShriek Λ z).mapIso α.symm ≪≫ u₀ ≪≫ u₁

/-- The same comparison as a supported class, on the zero locus of the coordinates.
The support transport is the canonical one characterized by its counit equation.
Source: sk-thm-regular.proof.md, Step 4(iii)
(blueprint: def-pur-regular-projection-supported-class). -/
def regularProjectionSupportedClass (B : Scheme.{u}) (c : ℕ)
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B)]
    (α : dualizingComplex Λ (𝔸(ULift.{u} (Fin c); B) ↘ B) ≅
      (tateObject Λ 𝔸(ULift.{u} (Fin c); B) c)⟦2 * (c : ℤ)⟧) :
    let X := 𝔸(ULift.{u} (Fin c); B)
    let t : Fin c → Γ(X, ⊤) := fun j ↦ AffineSpace.coord B (ULift.up j)
    constantComplex Λ X ⟶
      (R(X.zeroLocusSubschemeι (Set.range t))_![ModuleCat.{u + 1} Λ]).obj
        ((R(X.zeroLocusSubschemeι (Set.range t))^![Λ]).obj
          ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) := by
  let X := 𝔸(ULift.{u} (Fin c); B)
  let t : Fin c → Γ(X, ⊤) := fun j ↦ AffineSpace.coord B (ULift.up j)
  let z := AffineSpace.zeroSection (ULift.{u} (Fin c)) B
  let L := (tateObject Λ X c)⟦2 * (c : ℤ)⟧
  have hr : Set.range z.base = Set.range (X.zeroLocusSubschemeι (Set.range t)).base := by
    rw [AffineSpace.range_zeroSection, Scheme.range_zeroLocusSubschemeι]
    ext x
    simp only [Set.mem_ofPred_eq, Scheme.mem_zeroLocus_iff, Set.forall_mem_range]
    constructor
    · intro h j
      exact h (ULift.up j)
    · intro h j
      exact h j.down
  exact (supportedClassMapEquiv Λ z L).symm
      (regularProjectionContraction Λ B c α).inv ≫
    (supportedTransportIso Λ z (X.zeroLocusSubschemeι (Set.range t)) hr L).hom

/-- The published diagonal/Rees normalization on an affine projection, transported
by the same ordered root comparison as the absolute smooth orientations.
Source: sk-thm-regular.proof.md, Step 4(iii)
(blueprint: def-pur-regular-projection-supported-class). -/
def regularProjectionOrientationNormalized
    (B : Scheme.{u}) [IsNoetherian B] (c : ℕ)
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B)]
    (α : dualizingComplex Λ (𝔸(ULift.{u} (Fin c); B) ↘ B) ≅
      (tateObject Λ 𝔸(ULift.{u} (Fin c); B) c)⟦2 * (c : ℤ)⟧) : Prop :=
  let X := 𝔸(ULift.{u} (Fin c); B)
  let p : X ⟶ B := X ↘ B
  letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  ∃ G : FiniteRingSectionDeformation.Geometry c
      (pullback.fst p p) (pullback.diagonal p),
    ∃ hX : IsUnit (ringChar Λ : Γ(X, ⊤)),
      FiniteSmoothPurity.OrientationNormalized Λ (ringChar Λ)
        (Nat.pos_of_ne_zero (NeZero.ne (ringChar Λ))) ringChar.Nat.cast_ringChar
        p c G hX (α ≪≫ regularTatePowerComparison Λ X c)

end AlgebraicGeometry.Etale
