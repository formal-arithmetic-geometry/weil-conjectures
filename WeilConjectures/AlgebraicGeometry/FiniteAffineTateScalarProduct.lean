/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import all WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
import all WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarBalancingExistence
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ScalarSingleAdjointInsertion
import WeilConjectures.AlgebraicGeometry.TateTensorAdjunctionInsertion

/-! # Ordered positive Tate scalar products -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open WeilConjectures.PurityFiniteSetting
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
attribute [local implicit_reducible] Scheme.finiteEtaleTateSheaf
  Scheme.finiteEtaleTateTwist ordinaryFiniteDegreeZero

private theorem product_positive
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (r : ℕ) :
    (orderedTateProductIso R N hN hR T hT (r + 1)).hom =
      (singleFunctorObjTensorIso
        (Scheme.finiteEtaleTateSheaf R N T hR ((r + 1 : ℕ) : ℤ))
        (Scheme.finiteEtaleTateLine T N R hR)
        (twistFlat R N hN hR T hT (r + 1))).hom := by
  have hp := (Scheme.finiteEtaleTwistPullbackData R N hN hR).laws.2.2.2.2.2.2.2.2.2.2.1 T hT r
  have hp' : (Scheme.finiteEtaleTwistPullbackData R N hN hR).p
      T hT ((r + 1 : ℕ) : ℤ) 1 = Iso.refl _ := hp
  have hprod : twistSheafProduct R N hR
      (Scheme.finiteEtaleTwistPullbackData R N hN hR) T hT (r + 1) = Iso.refl _ := by
    unfold twistSheafProduct
    erw [hp']
    simp only [Iso.refl_trans]
    rfl
  unfold orderedTateProductIso singleProductGeneral
  erw [hprod]
  let e := singleFunctorObjTensorIso
    (Scheme.finiteEtaleTateSheaf R N T hR ((r + 1 : ℕ) : ℤ))
    (Scheme.finiteEtaleTateLine T N R hR)
    (twistFlat R N hN hR T hT (r + 1))
  change e.hom ≫ (DerivedCategory.singleFunctor _ 0).map (𝟙 _) = e.hom
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Ordered positive Tate scalar maps respect the actual derived single product.
Source: Charts, retained Step 4 of reduction-exceptional
(blueprint: lem-sp-finite-affine-tate-scalar-product).

Proof: the normalized ordinary product of a positive Tate power and the root line
is the identity, so its derived single product is singleFunctorObjTensorIso.
The ordinary chart family is recursively the oplax scalar tensorator followed by
its two lower balancing maps. Transpose under extension/restriction of scalars:
the adjunct at r+2 is the tensor of the two adjuncts followed by the lax tensorator
of restriction. Each derived chart map is the scalar-adjunction insertion of this
ordinary adjunct. Tate sheaves are flat because N is invertible. Apply the proved
flat single/tensor insertion square to these four sheaves and the two adjuncts.
The product remains ordered; no symmetry or flatness of B over A is used. -/
theorem finiteAffineTateScalar_product
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (r : ℕ) :
    (ExceptionalCoefficients.tensorIso φ T).hom.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist T N A hA (r + 1)), ordinaryFiniteLine A N hA T) ≫
      derivedTensorHom (ModuleCat.{u + 1} B)
        (finiteAffineTateScalarMap φ T N hA hB (r + 1))
        (finiteAffineTateScalarMap φ T N hA hB 1) ≫
      (orderedTateProductIso B N hN hB T hT (r + 1)).hom =
    (scalarExtension φ T).map (orderedTateProductIso A N hN hA T hT (r + 1)).hom ≫
      finiteAffineTateScalarMap φ T N hA hB (r + 2) := by
  let β := ProEtale.chartEtaleTateScalarIso φ T N hA hB
  let η (d : ℕ) := (purityScalarSheafAdjunction φ T).homEquiv _ _ (β d).hom
  have hi (d : ℕ) : finiteAffineTateScalarMap φ T N hA hB d =
      SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ (η d) := by
    exact FiniteSmoothPurity.scalarSingleMap_eq_scalarInsertion φ T _ _ _
  have hη : η (r + 2) = (η (r + 1) ⊗ₘ η 1) ≫
      Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ)
        (Scheme.finiteEtaleTateTwist T N B hB (r + 1))
        (Scheme.finiteEtaleTateLine T N B hB) := by
    exact balancingTensorAdjoint φ T _ _ _ _ (β (r + 1)).hom (β 1).hom
  have hflat (R : Type (u + 1)) [CommRing R] [Finite R] (hR : (N : R) = 0)
      (d : ℕ) : ObjectProperty.flat (Scheme.finiteEtaleTateTwist T N R hR d) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line T N hN (fun x ↦ by
      simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom) R hR d).2.2.1
  rw [product_positive, product_positive, hi, hi, hi, hη]
  exact tateTensor_scalarAdjointInsertion φ T _ _ _ _
    (hflat A hA (r + 1)) (hflat A hA 1)
    (hflat B hB (r + 1)) (hflat B hB 1) (η (r + 1)) (η 1)

end AlgebraicGeometry.Etale
