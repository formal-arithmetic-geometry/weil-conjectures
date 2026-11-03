/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.CondensedExceptionalUnitCoordinates
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Constant
import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.NativeExceptionalUnitExistence
import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.NativeExceptionalBrownData
import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.NativeExceptionalNativeHomology
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Exceptional cohomology under the ordinary condensed encoding

This is a comparison for every degree and every separated finite-type map. It has no
smoothness hypothesis and contains no purity or Tate-line identification.
Source: sk-def-sf-weil-complexes, heart comparison, and the exceptional adjunction
in sk-thm-existence. (blueprint: lem-sf-native-exceptional-condensed-cohomology).
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

set_option linter.unusedVariables false in
/-- Native exceptional cohomology agrees, in the Weil heart, with ordinary condensed
exceptional cohomology carrying the counit-normalized Frobenius map.

Source: sk-def-sf-weil-complexes, comparison with the triangulated native category;
sk-thm-existence, ordinary exceptional adjunction; compact-support exchange in
sk-thm-sf-comp-composition. No smooth purity is used.
(blueprint: lem-sf-native-exceptional-condensed-cohomology).

Proof in words. Construct the ordinary right adjoint on the localizing constructible
closure by Brown representability. The unit belongs to Dctf and hence to this closure.
Take the mate of normalized geometric-Frobenius compact-support exchange. Since both
horizontal pullbacks are equivalences, this mate is invertible; its value on the unit,
followed by the unit's canonical datum, is theta. The mate equation is E.normalized.

The exact native coefficient encoding identifies ordinary inverse images, open extension
by zero and proper direct images, with their unit and counit normalizations. Thus it
identifies the underlying compact-support composite and its Frobenius square. Apply the
native derived adjunction comparison, computing the derived invariants of the Laurent
action by its two-term induced resolution with its connecting map retained, to identify
the underlying exceptional value with the ordinary Brown value.
The counit equation identifies its Frobenius map with theta. The unique right-adjoint
comparison handles every supplied native J and adjunction. Exact coefficient encoding
commutes with cohomology, giving the displayed heart isomorphisms in every degree.
The argument uses the native derived category throughout the adjunction comparison;
it does not replace its Hom groups by morphisms of strict pairs. At an identity map
these are the unitors; on empty schemes the same adjunction identities still apply. -/
theorem native_exceptional_condensed_cohomology :
    ∃ E : ExceptionalUnit k₀ ell f c H,
      ∀ (J : WeilComplex k₀ ell Y ⥤ WeilComplex k₀ ell X)
        (adj : WeilComplex.derivedLowerShriek k₀ ell f ⊣ J) (n : ℤ),
        Nonempty
          ((nativeHomology k₀ ell X n).obj
              (J.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ ell Y))) ≅
            (pairHomology k₀ ell X n).obj E.pair) := by
  obtain ⟨R, ⟨adjR⟩, hu⟩ := exceptional_brown_data k₀ ell f c H
  obtain ⟨theta, htheta⟩ := exceptional_unit_frobenius k₀ ell f c H R adjR hu
  let E : ExceptionalUnit k₀ ell f c H := ⟨R, adjR, hu, theta, htheta⟩
  obtain ⟨J₀, ⟨adj₀⟩, hJ₀⟩ := exceptional_unit_native_homology k₀ ell f c H E
  refine ⟨E, fun J adj n ↦ ?_⟩
  obtain ⟨e⟩ := hJ₀ n
  exact ⟨(nativeHomology k₀ ell X n).mapIso
    ((adj.rightAdjointUniq adj₀).app
      (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ ell Y))) ≪≫ e⟩

end WeilConjectures.NativeCondensedCohomology
