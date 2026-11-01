/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurGysinLocalizationPushforward
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummer
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! Triangle-specific hypotheses for the affine-line cohomology extraction. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

abbrev gysinTriangle (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (first : (closedTerm P (zeroSection Y)).obj (gysinEtaleInput P h Y) ⟶
      (middleTerm P (lineProjection Y)).obj (gysinEtaleInput P h Y))
    (δ : (openTerm P (lineProjection Y) (openImmersion Y)).obj
      (gysinEtaleInput P h Y) ⟶
      ((closedTerm P (zeroSection Y)).obj (gysinEtaleInput P h Y))⟦(1 : ℤ)⟧) :
    Triangle (DerivedCategory (ProSheaves P Y)) :=
  Triangle.mk first
    ((restriction P (lineProjection Y) (openImmersion Y)).app
      (gysinEtaleInput P h Y)) δ

/-- The hypotheses needed by the long exact sequence are attached to the pushed-forward
localization triangle itself.  The construction uses the two relative Kummer units, the
Kummer generator and its higher vanishing, the comparison isomorphism `e` of the
localization theorem, and `fix-prop-adjunctions` to prove invertibility of the middle
degree-zero arrow.  The remaining proof is the triangle-specific coefficient transport
substep in the proof of `lem-pur-gysin-structure` (blueprint: lem-pur-gysin-structure). -/
structure GysinExtractionHypotheses
    (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (T : Triangle (DerivedCategory (ProSheaves P Y))) where
  L : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)
  M : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)
  hB : ∀ m : ℤ, m ≠ 0 → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) m).obj T.obj₂)
  eB : Nonempty ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).obj T.obj₂ ≅ L)
  hC : ∀ m : ℤ, m ≠ 0 → m ≠ 1 → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) m).obj T.obj₃)
  eC₀ : Nonempty ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).obj T.obj₃ ≅ L)
  eC₁ : Nonempty ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 1).obj T.obj₃ ≅ M)
  hMor₂ : IsIso ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map T.mor₂)

/-
The comparison components are written out in the statement so that this split cannot be
instantiated with an unrelated distinguished triangle.  In particular, `he` is the
comparison supplied by `gysin_localization_pushforward`, rather than an arbitrary witness.
-/
theorem gysin_triangle_extraction_hypotheses
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (Y : Scheme.{u}) (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (first : (closedTerm P (zeroSection Y)).obj (gysinEtaleInput P h Y) ⟶
      (middleTerm P (lineProjection Y)).obj (gysinEtaleInput P h Y))
    (δ : (openTerm P (lineProjection Y) (openImmersion Y)).obj
      (gysinEtaleInput P h Y) ⟶
      ((closedTerm P (zeroSection Y)).obj (gysinEtaleInput P h Y))⟦(1 : ℤ)⟧)
    (δet : EtaleBoundary P (zeroSection Y) (openImmersion Y))
    (hT : gysinTriangle P h Y first δ ∈ distTriang (DerivedCategory (ProSheaves P Y)))
    (he : ∃ e : transportedTriangle P (lineProjection Y) (zeroSection Y)
        (openImmersion Y) δet (gysinEtaleInput P h Y) ≅ gysinTriangle P h Y first δ,
      e.hom.hom₁ = firstComparison P (lineProjection Y) (zeroSection Y)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)
        (gysinEtaleInput P h Y) ∧
      e.hom.hom₂ = imageComparison P (lineProjection Y) (gysinEtaleInput P h Y) ∧
      e.hom.hom₃ = thirdComparison P (lineProjection Y) (openImmersion Y)
        (gysinEtaleInput P h Y))
    (hK : P.RelativeKummerConclusions h Y a) :
    Nonempty (GysinExtractionHypotheses P Y (gysinTriangle P h Y first δ)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
