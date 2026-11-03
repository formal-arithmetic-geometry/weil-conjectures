/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.CondensedExceptionalUnitCoordinates
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Constant

/-! # Native homology comparison for an exceptional unit

The exact coefficient encoding and the native derived adjunction comparison identify
native homology of a constructed native right adjoint with the pair homology of a normalized
ordinary exceptional unit.
Source: `lem-sf-native-adic-encoding-ordinary-operations`,
`def-weil-weil-sheaf-complex`, and the heart comparison in
`lem-sf-native-condensed-cohomology-coordinates` (blueprint:
lem-sf-native-exceptional-native-homology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.NativeCondensedCohomology

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ell : ℕ) [Fact ell.Prime]
  [Fact (ringChar k₀ ≠ ell)]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  [IsSeparated (X ↘ Spec (.of k₀))] [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
  [QuasiCompact (X ↘ Spec (.of k₀))]
  [IsSeparated (Y ↘ Spec (.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (.of k₀))]
  [QuasiCompact (Y ↘ Spec (.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification (fiberMap k₀ f).hom.left)
  (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj ell)
    (AlgebraicClosure k₀))

/-- A native right adjoint with the ordinary pair cohomology exists.

Source: sk-def-sf-weil-complexes, the exceptional-adjoint paragraph of
lem-fix-weil-operations.proof.md, and ordinary six-operation constructible preservation.

Proof: work first in the full subcategory of native derived objects whose ordinary
underlying object lies in the geometric localizing closure. Use exact coefficient
encoding to compare inverse image, open extension and proper image, with the actual
unit and counit maps. Use the normalized compactification refinement comparison
to compare the native chosen compactification with c; H.laws fixes this comparison
and its exchange square. For each compact geometric generator C, derived free Laurent
induction I(C) is compact: Hom(I(C), -) is Hom(C, U(-)), and exact forgetting U
preserves coproducts. These free objects detect zero because U is conservative and
the geometric generators detect zero. Their underlying objects are sums of Frobenius
translates of C, so they belong to the stated closure. This closure is therefore
compactly generated. The native compact-support functor is exact and preserves
coproducts there. Brown representability gives a native right adjoint J.

Compare compact support with free induction using the exact operation comparisons
and the Laurent two-term induced resolution, retaining its connecting map. This is
a comparison of native derived functors, not a faithful strict-pair realization.
For geometric A and native M, the chain
Hom(A, U(J M)) = Hom(I(A), J M) = Hom(F_native(I(A)), M)
= Hom(I(F(A)), M) = Hom(F(A), U(M)) = Hom(A, R(U(M)))
is natural in A and M. Yoneda gives U(J M) isomorphic to R(U(M)), with the actual
counit compatibility. Independent ordinary six-operation constructible preservation
shows that this is bounded constructible when M is. Exact conservative forgetting
reflects these properties. Restrict the adjunction through the full inclusions to
WeilComplex. No purity or biduality theorem is used.

Evaluate at the native constant unit and use its specified coefficient-unit
comparison. The counit compatibility identifies its Frobenius map with E.theta:
apply E.theta_unique, or equivalently E.pairIsoOfCounit. Exact homology then gives
the displayed heart isomorphism in every degree. For an identity map these
comparisons are the adjunction unitors; for an empty source the zero functor is the
required right adjoint.
(blueprint: lem-sf-native-exceptional-native-homology). -/
theorem exceptional_unit_native_homology (E : ExceptionalUnit k₀ ell f c H) :
    ∃ (J : WeilComplex k₀ ell Y ⥤ WeilComplex k₀ ell X),
      Nonempty (WeilComplex.derivedLowerShriek k₀ ell f ⊣ J) ∧ ∀ n : ℤ,
      Nonempty
        ((nativeHomology k₀ ell X n).obj
            (J.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ ell Y))) ≅
          (pairHomology k₀ ell X n).obj E.pair) := by
  sorry

end WeilConjectures.NativeCondensedCohomology
