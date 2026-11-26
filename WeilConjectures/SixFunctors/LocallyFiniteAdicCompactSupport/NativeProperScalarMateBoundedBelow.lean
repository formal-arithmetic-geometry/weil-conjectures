/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMateBoundedBelowRestricted

/-! # The bounded-below completed-to-native proper scalar mate

## Implementation details

The map from completed integral coefficients to native coefficients factors as the
localization to the finite rational coefficient field followed by that field's inclusion
into the locally finite algebraic-closure coefficient ring. The proper scalar mate is
correspondingly the composite of the localized direct-image comparison (invertible on
bounded-below inputs for quasi-compact quasi-separated morphisms) and the bounded proper
push comparison for the finite field's inclusion into the algebraic closure.

## References

* [Bhatt--Scholze, Remark 6.8.15]
* [Hemo--Richarz--Scholbach, Lemma 5.3(1)]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- The completed-to-native proper scalar mate is invertible on bounded-below inputs. -/
theorem native_proper_scalar_mate_bounded_below
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T)
    {U V : Scheme.{u}} (g : U ⟶ V) [IsProper g]
    (M : DerivedCategory (pbcModules U
      ((PurCompactSupport.completed l (Coefficient.{u} l (PadicAlgCl l) E)).ring U)))
    (hM : DerivedCategory.TStructure.t.plus M) :
    IsIso ((PurCompactSupport.properComparison a g).app M) := by
  have hrestricted := native_proper_scalar_mate_bounded_below_restricted
    l E a ha g M hM
  let F := pbcRestrict (a.map V)
  have hF : F.ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (a.map V)).2.2
  haveI : F.ReflectsIsomorphisms := hF
  haveI : F.mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun {X Y} f hf => ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro q
    have hq : IsIso (F.map ((DerivedCategory.homologyFunctor _ q).map f)) := by
      have := (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso q) f).2
        (by rw [Functor.comp_map]; infer_instance)
      exact this
    exact isIso_of_reflects_iso _ F
  haveI : IsIso (F.mapDerivedCategory.map
      ((PurCompactSupport.properComparison a g).app M)) := hrestricted
  exact isIso_of_reflects_iso _ F.mapDerivedCategory

end WeilConjectures.LocallyFiniteAdicCompactSupport
