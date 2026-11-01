/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.NumberTheory.Padics.Complex
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.ProperBaseChange.CondensedFieldLfpLocalTriviality
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import all WeilConjectures.ProperBaseChange.CondensedFiniteFreeTensorExact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseRestriction
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
public import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian

/-!
# Finite Tor amplitude over the full continuous algebraic closure

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change, the equality
Dctf = Dbc for rational coefficients, specialized to the all-continuous-map coefficient.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
/-- Bounded constant-model constructible complexes over the full continuous-map
algebraic closure have finite Tor amplitude.

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change, equality Dctf = Dbc
for rational coefficients; sk-def-sfb-constructible, finite Tor amplitude.
(blueprint: det-sf-comp-continuous-algcl-constructible-tor).

Proof: a locally finitely presented module over a totally disconnected normed field
is locally finite free. In a finite presentation, specialization preserves every
matrix entry and hence the corank; descent makes this corank locally constant.
Gaussian elimination then gives free cokernels on a pro-etale refinement. Apply this
to the universe lift of PadicAlgCl, using its continuous coefficient isomorphism.
On each constructible stratum, a finite constant local model is locally finitely
presented, hence locally finite free. Its tensor functor is exact. Pullback commutes
with tensor, and the finite jointly surjective family of stratum immersions detects
equality of maps. Thus the tensor functor on the original scheme preserves
monomorphisms, and right exactness makes every constructible module flat. Finally,
a bounded complex is an iterated extension of its shifted cohomology modules.
A flat module in degree zero has Tor amplitude [0,0]; finite Tor amplitude is
stable under shifts, isomorphisms and extensions. This also covers an empty scheme
and the zero complex. -/
theorem continuousAlgCl_bounded_finiteTor
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X)))
    (hK : constantModelBoundedConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X K) :
    DerivedCategory.finiteTorAmplitude _ K := by
  let Λ := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let Q : ObjectProperty (DerivedCategory C) := DerivedCategory.finiteTorAmplitude C
  have : Q.IsTriangulated :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).2.2.2.2.2.2.2.1
  have : Q.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).2.2.2.1
  obtain ⟨d, hd⟩ := DerivedCategory.exists_iteratedExtensions_of_bounded
    (ObjectProperty.flat (A := C)) K hK.1
    (fun n ↦ continuousAlgCl_constructible_flat ℓ X _ (hK.2 n))
  apply DerivedCategory.iteratedExtensions_le (ObjectProperty.flat (A := C))
    (Q := Q) ?_ d K hd
  rintro L ⟨n, M, hM, ⟨e⟩⟩
  have h0 : DerivedCategory.finiteTorAmplitude C
      ((DerivedCategory.singleFunctor C 0).obj M) :=
    ⟨0, 0, DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hM⟩
  have hn : DerivedCategory.finiteTorAmplitude C
      (((DerivedCategory.singleFunctor C 0).obj M)⟦-n⟧) :=
    (DerivedCategory.finiteTorAmplitude C).le_shift (-n) _ h0
  exact (DerivedCategory.finiteTorAmplitude C).prop_of_iso
    (e ≪≫ (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by lia)).app M).symm).symm hn

end AlgebraicGeometry.ProEtale
