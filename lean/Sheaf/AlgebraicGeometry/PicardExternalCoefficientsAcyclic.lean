/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.Paper.HigherDirectImagePresheaf

/-! # Acyclicity of external tensor coefficients

Source: Stacks Project, Varieties, Tag 0BED, acyclic Leray base case.
(blueprint: lem-sc-picard-external-coefficients-acyclic).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- The external tensor product of two acyclic quasi-coherent modules is acyclic.
Source: Stacks Project, Varieties, Tag 0BED, acyclic base case after
`equation-kunneth-on-cech`.
(blueprint: lem-sc-picard-external-coefficients-acyclic).

Proof: Choose a finite affine cover of X. Its finite intersections are affine
because X has affine diagonal. For each affine open V of Y, affine pullback and
tensor section formulas identify the Cech complex of X times V with Cech(X,F)
tensor G(V). Exactness of field tensor and affine Cech comparison show that its
positive cohomology vanishes and its degree-zero cohomology is Gamma(X,F) tensor
G(V), naturally on the affine basis. The higher-direct-image presheaf description
then gives zero higher direct images under pr2 and identifies pr2_* of the external
coefficients with Gamma(X,F) tensor G. A basis of Gamma(X,F) identifies this sheaf
with a direct sum of copies of G. The affine diagonal of Y implies quasi-separatedness.
Cohomology on qcqs Y commutes with these direct sums, so hG makes this direct image
acyclic. Thus H^p(Y,R^q pr2_* E) vanishes for every p>0 and q: for q=0
use this direct-sum acyclicity, and for q>0 use the zero higher direct images.
The degenerate Leray edge therefore identifies H^n(X times Y,E) with
Gamma(Y,R^n pr2_* E), which is zero for n>0. No basis
is required to be finite. Empty schemes and zero coefficients give zero sheaves
and satisfy the same conclusion. -/
theorem picardExternalCupCoefficients_acyclic
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F))
    (hG : ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G)) (n : ℕ) (hn : 0 < n) :
    IsZero ((RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace n).obj
      (externalCupCoefficients f g F G)) := by sorry

end AlgebraicGeometry.Scheme.Modules
