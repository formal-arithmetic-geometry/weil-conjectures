/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.SixFunctors.ScalarSixHomGeneratorConstructible
import WeilConjectures.SixFunctors.ScalarSixHomGeneratorTorWindow

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- The bounded constructibility and finite-Tor half of the locally closed scalar Hom
generator calculation.
Source: blueprint det-prop-scalar-six-tensor-hom.proof.md, The generator and It is v.
(blueprint: lem-sfb-native-scalar-hom-generator-finiteness).
Proof: factor the immersion and apply the support localization formula to express
RHom of the extension against M as a direct image of RHom from the local support
model. The locally perfect charts identify this local Hom with the dual of a
finite-projective scalar complex tensored with the support object, so its Tor
interval is the interval supplied by the two bounded factors. Establish the
constructibility and interval uniformly after the separably closed base change,
where the relative immersion stability theorem applies; exact conservative
pullback descends the stratification and bounds. Finally apply relative
immersion direct-image stability and the support adjunction to obtain the two
properties for the displayed ambient Hom.
-/
theorem scalarSixHom_generator_finiteness
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (M : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (S : Scheme.{u}) (b : S ⟶ X.left) (hb : IsImmersion b)
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hP : IsLocallyPerfectScalarModel Λ.X S P) :
    (constantModelBoundedConstructible Λ.X X.left
      (((derivedHom Λ.X X.left).obj
        (.op ((sfbLocallyClosedDerivedExtension Λ b hb).obj P))).obj M.obj) ∧
      DerivedCategory.finiteTorAmplitude _
        (((derivedHom Λ.X X.left).obj
          (.op ((sfbLocallyClosedDerivedExtension Λ b hb).obj P))).obj M.obj)) := by
  let _ := (constantModelConstructibleFiniteTor_wellDefined Λ.X X.left).2.1
  obtain ⟨Q, hQ, ⟨e⟩⟩ :=
    scalarSixHom_generator_constructible ell k a ha X M S b hb P hP
  have hE := scalarSixHom_generator_torWindow ell k a ha X M S b hb Q hQ
  exact ⟨
    (constantModelBoundedConstructible Λ.X X.left).prop_of_iso e.symm hE.1,
    (DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm hE.2⟩

end AlgebraicGeometry.ProEtale.CondensedRing
