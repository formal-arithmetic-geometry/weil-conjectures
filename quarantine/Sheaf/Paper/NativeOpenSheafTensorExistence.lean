/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.NativeOpenTensorComparisonData

/-! # The native sheaf open tensor calculation

Source: Stacks 0E8I and 03DJ; equivariant refinement, steps 1--4 of
lem-sf-native-open-derived-tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The normalized sheaf adjunction and balanced tensor comparisons, with
preservation of categorical two-sided K-flatness.

Source: Stacks 0E8I, 03DJ, 03D8; steps 1--4 of the native open tensor argument
(blueprint: lem-sf-native-open-sheaf-tensor-existence).

Proof: Identify the geometric open site with the slice. Its coefficient sheaf is
the restriction of the ambient coefficient sheaf: both are the same locally
finite coefficient functions. Lift the extension/restriction adjunction to Weil
sheaves. On local sections the unit is x maps to [x] and the counit is [x] maps
to x; Frobenius reindexes the same factoring objects, so both maps intertwine
the Weil structures. Invertibility of the lifted unit is proved separately in the assembling
theorem, using faithful conservative forgetting. The restriction/tensor comparison is
the balanced map taking x tensor y to x|U tensor y|U. The open tensor comparison
takes [x] tensor y to [x tensor y|U]. Its inverse is the transpose of tensoring
with the open unit, followed by inverse restriction/tensor comparison. Check
balancing, inverse identities, naturality, and Frobenius equivariance on pure
tensors. Apply these maps in each bidegree and take direct sums; both differential
composites on degree (p,q) are dx tensor y + (-1)^p x tensor dy. This gives the
natural chain comparison. For a K-flat P on the open, restrict an arbitrary
ambient quasi-isomorphism, tensor with P, and extend; exactness and the chain
comparison show that extension preserves K-flatness. For a K-flat ambient T,
extend a quasi-isomorphism on the open and tensor with T. The chain comparison
identifies this with extension of its tensor with restriction of T. Restrict
back, using the invertible open unit, to reflect the quasi-isomorphism. Symmetry
gives the other tensor variable in each test. Thus the recorded two-sided
categorical K-flat predicates are preserved; no boundedness or flat-term
assumption is imposed on these tests. -/
theorem native_open_sheaf_tensor_existence :
    ∃ (adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j)
      (sheafRestriction : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
        (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
          tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M))
      (sheafGamma : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
        tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) ≅
          (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M)),
      (∀ M, (adj.unit.app M).hom.f =
        (ProEtale.adicOpenImmersionLowerShriekAdjunction l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier) ∧
      (∀ N, (adj.counit.app N).hom.f =
        (ProEtale.adicOpenImmersionLowerShriekAdjunction l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier) ∧
      (∀ M N, HEq ((sheafRestriction M N).hom.hom.f)
        ((ProEtale.adicUpperStarTensorLeftIso l
          (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)) ∧
      (∀ M N, HEq (adj.homEquiv _ _ ((sheafGamma M N).inv))
        ((tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
          (sheafRestriction ((extensionByZero k₀ l j).obj M) N).inv)) ∧
      (∀ P, NativeIsKFlat k₀ l U P → NativeIsKFlat k₀ l Z
        (((extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ T, NativeIsKFlat k₀ l Z T → NativeIsKFlat k₀ l U
        (((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).obj T)) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
