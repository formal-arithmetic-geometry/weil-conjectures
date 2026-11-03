/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.StandardPasting.StandardSectionPastingData
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence

/-! # The second concrete affine section-pasting factor
(blueprint: lem-route-standard-section-pasting-base-change-second-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.StandardPasting
open DiagonalPasting

set_option maxHeartbeats 1500000 in
-- Derived pullback compositor expressions require a larger elaboration budget.
/-- The second input is compatible with the specified middle-projection mate.
Source: composition coherence Step 1, the second factor in Step 5 of the standard-pair
base-change calculation (blueprint: lem-route-standard-section-pasting-base-change-second-factor).
Proof: the zero section followed by the second block projection is the rank-e zero
section on both bases. The section-pullback locality composition equation identifies
the two ways of commuting the three pullbacks. Naturality of the primed compositor
moves the rank-e beta through it. This gives the required equality, with no cancellation
of a dimension or assumption that either base is nonempty.
-/
theorem second_factor_identity (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (d e : ℕ) (b : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (secondInput P d e B) ≪≫ secondChange P d e b aB =
      baseChange P e b aB ≪≫ secondInput P d e B' := by
  let := affineDimension e B
  let be := beta P.Coefficient P e (AffineSpace.isPullback_map b) (pr e B ≫ aB)
  have hc := Etale.section_pullback_locality_comp P.Coefficient b
    (zero e B) (zero e B') (zero (d+e) B) (zero (d+e) B')
    (q d e B) (q d e B') (AffineSpace.map (ULift.{u} (Fin e)) b)
    (AffineSpace.map (ULift.{u} (Fin (d+e))) b)
    (AffineSpace.zeroSection_comp_map b).symm
    (AffineSpace.zeroSection_comp_map b).symm
    (affineGeometry d e B).2.2.1 (affineGeometry d e B').2.2.1
    (geometry d e b).1 (Etale.dualizingComplex P.Coefficient (pr e B))
  have hn := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (zero (d+e) B') (q d e B') (zero e B')
    (affineGeometry d e B').2.2.1.symm).hom.naturality be.hom
  simp only [Functor.comp_map] at hn
  apply Iso.ext
  dsimp only [secondInput, secondChange, baseChange, Iso.trans_hom,
    Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hc, hn]

end WeilConjectures.PurityFiniteSetting.StandardPasting
