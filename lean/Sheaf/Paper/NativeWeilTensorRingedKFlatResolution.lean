/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.NativeWeilTensorRingedBridgeData
import Sheaf.Algebra.Homology.QuasiIsoFractionObstruction
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.WeilSheaf.Constant

/-! # Native K-flat resolutions

The native acyclic-test K-flat predicate is resolving: every complex admits a
quasi-isomorphism from a complex satisfying the predicate.  This is the density
input for the localization equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]

/-- Every native complex has a native K-flat quasi-isomorphic replacement.
Source: Stacks 06YS, the unbounded K-flat replacement construction.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-resolution)

The construction resolves an arbitrary complex by the telescope of its bounded
truncation replacements.  Each truncation replacement has native K-flat terms;
the countable telescope remains native K-flat by closure under sums and cones,
and its augmentation to the original complex is a quasi-isomorphism.  The
construction is unbounded and also applies to the zero complex.
-/
-- STATEMENT-DISPUTED: strict right fraction cancellation forces every native complex
-- to be acyclic; see native_weil_tensor_ringed_kflat_resolution_obstruction below.
-- The valid Mathlib fraction calculus is on HomotopyCategory, not on complexes.
theorem native_weil_tensor_ringed_kflat_resolution :
    let W₀ := HomologicalComplex.quasiIso
      (ProEtaleWeilSheaf k₀ l X) (.up ℤ)
    W₀.HasRightCalculusOfFractions ∧
      let P : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
        NativeTensorKFlat k₀ l X T
      ∀ K : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
        ∃ (P' : P.FullSubcategory) (s : P.ι.obj P' ⟶ K), W₀ s := by
  sorry

omit [Fact (ringChar k₀ ≠ l)] in
/-- On a nonempty scheme the proposed strict fraction package is false.
Source: Stacks 014D and 04VC; the cone-of-identity cancellation obstruction.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-resolution-obstruction)

Proof: the first conjunct asserts a strict calculus of fractions for
quasi-isomorphisms on complexes. Apply the general mapping-cone obstruction to
the complex consisting of the native constant sheaf in degree zero. Its zeroth
homology is that constant sheaf, so the latter would be zero. Forgetting its
Frobenius structure and its adic module structure would make the constant
coefficient sheaf zero, contradicting its nonzero section 1 on the nonempty
geometric fiber. The tensor and the K-flat replacement conjunct play no role. -/
theorem native_weil_tensor_ringed_kflat_resolution_obstruction [Nonempty X] :
    ¬ (let W₀ := HomologicalComplex.quasiIso
        (ProEtaleWeilSheaf k₀ l X) (.up ℤ)
      W₀.HasRightCalculusOfFractions ∧
        let P : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
          NativeTensorKFlat k₀ l X T
        ∀ L : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
          ∃ (P' : P.FullSubcategory) (s : P.ι.obj P' ⟶ L), W₀ s) := by
  intro h
  let K := (HomologicalComplex.single (ProEtaleWeilSheaf k₀ l X) (.up ℤ) 0).obj
    (adicConstant k₀ l X)
  have hK := CochainComplex.acyclic_of_quasiIso_hasRightCalculusOfFractions h.1 K
  have hz : IsZero (adicConstant k₀ l X) :=
    (hK 0).isZero_homology.of_iso
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (adicConstant k₀ l X)).symm
  have hf := (Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback k₀ l X)).map_isZero hz
  have := Scheme.Hom.nonempty_geometricFiber k₀ X
  exact ProEtale.not_isZero_adicConstantSheaf l _
    ((ProEtale.AdicSheaf.forget _).map_isZero hf)

end AlgebraicGeometry.ProEtaleWeilSheaf
