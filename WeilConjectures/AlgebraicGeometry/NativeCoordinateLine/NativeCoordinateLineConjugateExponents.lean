/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace

/-! # Native finite Kummer exponent compatibility

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, final paragraph, and
lem-pur-vector-integration-site-comparison, exponent independence.
(blueprint: lem-route-coordinate-line-conjugate-exponents).

The displayed maps use ordinary finite Kummer lines and their exact comparison
pullbacks. The affine-chart coordinate is removed using the existing canonical
Tate inverse-image comparison. All exponents below are indexed by predecessors:
`r` denotes the positive exponent `r + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.NativeCoordinateLine

open AffineLinePurity VectorIntegrationSite

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The ordinary finite power comparison rho_{b,a}, normalized on pure root tensors.
The existing unique comparison in twistCompatibility is characterized by
IsFiniteTateEtaleTransition: u tensor x maps to u^(ell^(b-a)) tensor x.
Source: def-coefficient-twists-detailed and vector-integration exponent comparison
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
def powerComparison (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    (a b : ℕ) (hab : a ≤ b)
    (ha : ((P.coefficients.l ^ (a + 1) : ℕ) : Ring P) = 0)
    (hb : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0) :
    Scheme.finiteEtaleTateTwist T (P.coefficients.l ^ (b + 1)) (Ring P) hb 1 ≅
      Scheme.finiteEtaleTateTwist T (P.coefficients.l ^ (a + 1)) (Ring P) ha 1 :=
  ((twistCompatibility P.coefficients.l P.extension (P.level - 1)).2.2
    T (primeUnit P T aT) a b hab ha hb 1).exists.choose

/-- The native transition tau_{s0,s1}: inverse rho_{M,s0}, then rho_{M,s1}.
Here M=max(s0,s1); predecessor indexing commutes with maximum. No coefficient
extension or reduction is taken in this construction.
Source: the common-exponent transition in the node's statement
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
def transition (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    (r s : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0) :
    Scheme.finiteEtaleTateTwist T (P.coefficients.l ^ (r + 1)) (Ring P) hr 1 ≅
      Scheme.finiteEtaleTateTwist T (P.coefficients.l ^ (s + 1)) (Ring P) hs 1 :=
  (powerComparison P T aT r (max r s) (Nat.le_max_left r s) hr
    ((Nat.cast_pow P.coefficients.l (max r s + 1)).trans
      (pow_eq_zero_of_le (Nat.add_le_add_right (Nat.le_max_left r s) 1)
        ((Nat.cast_pow P.coefficients.l (r + 1)).symm.trans hr)))).symm ≪≫
  powerComparison P T aT s (max r s) (Nat.le_max_right r s) hs
    ((Nat.cast_pow P.coefficients.l (max r s + 1)).trans
      (pow_eq_zero_of_le (Nat.add_le_add_right (Nat.le_max_left r s) 1)
        ((Nat.cast_pow P.coefficients.l (r + 1)).symm.trans hr)))

/-- The native compared shifted Kummer coefficient C_T B_{s,T}[2].
Source: the definition of Phi_s in the node
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
abbrev line (T : Scheme.{u}) (r : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :=
  (VectorIntegrationSite.comparison (Ring P) T).obj
    ((Etale.ordinaryFiniteLine (Ring P) (P.coefficients.l ^ (r + 1)) hr T)⟦(2 : ℤ)⟧)

/-- The existing affine-chart coordinate identified with C_X B_{s,X}[2].
Source: the specified Tate inverse-image comparison for the standard chart
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
def chartComparison (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    (r : ℕ) (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :
    coefficient P.coefficients.l P.extension (P.level - 1) T r hr ≅
      line P (AffineSpace PUnit.{u + 1} T) r hr :=
  eqToIso (coefficient_comparison_eq P.coefficients.l P.extension (P.level - 1) T r hr) ≪≫
    (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).mapIso
      (eqToIso (etaleCoefficient_eq P.coefficients.l P.extension (P.level - 1) T r hr)) ≪≫
    comparedLinePullback (Ring P) (P.coefficients.l ^ (r + 1))
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hr
      (ProjectiveLine.affineChart T)
      (by simpa only [Nat.cast_pow] using
        (primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT)).pow (r + 1))

/-- Phi_s in native Kummer coordinates. The existing affineLinePurityComparison
is the specified normalized projection-formula/integration transpose in chart
coordinates. Tensoring the inverse canonical chart comparison expresses it on
C_X B_{s,X}[2]. Equivalently this is gamma after tensoring alpha_s[2]; no
arbitrary purity isomorphism is selected.
Source: the affine-line comparison display and the definition of Phi_s
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
def conjugate (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (r : ℕ) (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    projectionSourceObject (Ring P) (AffineSpace PUnit.{u + 1} T ↘ T)
      (line P (AffineSpace PUnit.{u + 1} T) r hr) K.obj ⟶
      (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification T)).obj K.obj :=
  (CoordinateLine.tensorCoefficientIso (Ring P) T _ _
    (chartComparison P T aT r hr).symm K.obj).hom ≫
    affineLinePurityComparison P T r hr aT K Ke hKe eK

end AlgebraicGeometry.ProEtale.NativeCoordinateLine
