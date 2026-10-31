/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- The invertibility half of the locally closed scalar Hom generator calculation.
Source: blueprint det-prop-scalar-six-tensor-hom.proof.md, The generator and It is v.
(blueprint: lem-sfb-native-scalar-hom-generator-comparison).
Proof: factor the immersion through its scheme-theoretic image and use the support
adjunction to rewrite the ambient evaluation mate as the direct image of a local
internal Hom. On each locally perfect chart, finite-projective scalar models are
retracts of finite free models; the finite-free comparison follows from the unit
and biproduct comparison, and retract and finite-filtration closure extend it to
bounded complexes. The chartwise identifications commute with scalar change and
with the specified support pairing, by scalarInternalAdjunctionPairingChange.
Conservativity of the pro-etale cover and the relative immersion comparison then
assemble these local isomorphisms into the displayed native ihomComparison.
-/
theorem scalarSixHom_generator_comparison
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (M : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (S : Scheme.{u}) (b : S ⟶ X.left) (hb : IsImmersion b)
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hP : IsLocallyPerfectScalarModel Λ.X S P) :
    IsIso ((Functor.LaxMonoidal.ihomComparison (scalarSixChange a X.left)
      ((sfbLocallyClosedDerivedExtension Λ b hb).obj P)).natTrans.app M.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
