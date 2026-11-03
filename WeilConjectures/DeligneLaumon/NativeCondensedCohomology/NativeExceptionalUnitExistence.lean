/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.CondensedExceptionalUnitCoordinates

/-! # Brown exceptional unit

The mate of compact-support Frobenius exchange equips the value of a given
ordinary Brown adjoint on the constant unit with its normalized Frobenius datum.
Source: sk-thm-existence and the exceptional-adjoint paragraph of
`lem-fix-weil-operations.proof.md` (blueprint: lem-sf-native-exceptional-unit-existence).
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

/-- Given the ordinary Brown adjunction, its unit value has an invertible Frobenius
map satisfying the actual compact-support counit normalization.
Source: the exceptional-adjoint paragraph of lem-fix-weil-operations.proof.md.
(blueprint: lem-sf-native-exceptional-unit-existence).
Proof: H.pullback_preserves restricts geometric Frobenius and inverse Frobenius
pullback to each localizing closure. Conjugate exact heart pullback composition by
actionDerivedComparison to restrict the inverse equations. Denote these restricted
autoequivalences by F_X and F_Y. Fullness of the target inclusion lifts the actual
supportExchange to eL : localSupport composed with F_Y is isomorphic to F_X composed
with localSupport; faithfulness proves the inverse equations and naturality.

Take eR := IsoAlgebra.mateIso adj eL. Its hom is the actual mate of eL.inv, and it
is invertible since F_X and F_Y are equivalences. The coefficient unit U belongs
to the target closure by hu; lift unitTheta by its fully faithful inclusion.
Set theta to the underlying isomorphism eR.app U followed by R.mapIso unitTheta.
The equality IsoAlgebra.map_counit_app_comp_str for this unit algebra, using
mateEquiv_natTrans_eq_mateIso_hom, gives the displayed normalization. Apply the
full inclusion to that equality and use the definitions of the restricted functors
to obtain exactly supportExchange and the stated ambient counit components.
For an identity map the same mate identities give the unitors. The empty source
case uses the unique maps of the zero category. No native comparison is needed.
(blueprint: lem-sf-native-exceptional-unit-existence). -/
theorem exceptional_unit_frobenius
    (R : (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
        (Y ↘ Spec (.of k₀)).geometricFiber).FullSubcategory ⥤
      (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
        (X ↘ Spec (.of k₀)).geometricFiber).FullSubcategory)
    (adj : localSupport k₀ ell f c H ⊣ R)
    (hu : localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
      (Y ↘ Spec (.of k₀)).geometricFiber (unitObject k₀ ell Y)) :
    ∃ theta : (derivedAction k₀ ell X).obj (R.obj ⟨unitObject k₀ ell Y, hu⟩).obj ≅
        (R.obj ⟨unitObject k₀ ell Y, hu⟩).obj,
      (derivedAction k₀ ell Y).map (adj.counit.app ⟨unitObject k₀ ell Y, hu⟩).hom ≫
          (unitTheta k₀ ell Y).hom =
        (supportExchange k₀ ell f c H).hom.app (R.obj ⟨unitObject k₀ ell Y, hu⟩) ≫
          (support k₀ ell f c).map theta.hom ≫
            (adj.counit.app ⟨unitObject k₀ ell Y, hu⟩).hom := by
  sorry

end WeilConjectures.NativeCondensedCohomology
