/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso
import WeilConjectures.AlgebraicGeometry.LocalizedTensorBraidingNaturality
import WeilConjectures.AlgebraicGeometry.IntegralSystemReductionFullyFaithful

/-! # Naturality of the specified common-stage Koszul symmetry

Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.11 and Proposition 6.8.14;
the signed-symmetry descent argument of common-stage transposition, step 6
(blueprint: lem-sf-common-tensor-braiding-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
  [∀ x : X, Invertible (l : X.residueField x)]

attribute [local irreducible] commonStageDerivedTensor commonStageDerivedInternalHom
  commonStageTensorComparison commonStageHomComparison

/-- The specified common-stage Koszul braiding is natural for every pair of arrows.
Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 6.8.14;
lem-sf-adic-common-stage-hom-transpose, step 6
(blueprint: lem-sf-common-tensor-braiding-naturality).

Proof: choose a common finite field containing the stages of M, M', N and N',
the four tensor objects, and representatives of f and g. Such a field exists by
finite composita and the representative criterion. The defining representative
formula of common-stage tensor computes its maps by conjugating the rational
tensor maps with commonStageTensorComparison. The defining normalization of the
common-stage braiding computes it by the same comparisons surrounding the
rational braiding. At this field apply naturality of rational braiding: integrally
it is the natural Koszul swap of the completed tensor, and bilinearity extends
its naturality to all rational arrows, including sums of fractions. Cancel the
middle tensor comparisons in both composites. The resulting equality of rational
representatives gives equality of common-stage classes. All choices and further
extensions are harmless because the defining formulas hold at every common
larger field; no injectivity of the transition maps is used. The swap's degree
sign is unchanged by coefficient extension because coefficients have degree zero.
This includes zero arrows, identity arrows, and repeated or unequal entry fields. -/
theorem commonTensorBraiding_naturality
    (M M' N N' : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (f : M ⟶ M') (g : N ⟶ N') :
    (commonStageDerivedTensor l Ω X).map (Prod.mkHom f g) ≫
        (pullbackTensorCommonBraiding l Ω X M' N').hom =
      (pullbackTensorCommonBraiding l Ω X M N).hom ≫
        (commonStageDerivedTensor l Ω X).map (Prod.mkHom g f) := by sorry

end WeilConjectures
