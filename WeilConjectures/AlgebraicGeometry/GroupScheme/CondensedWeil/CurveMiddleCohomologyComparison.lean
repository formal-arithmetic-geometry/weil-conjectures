/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCurveWeights.NativeCurveMiddleUpper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FieldSmoothDuality.CondensedFieldSmoothDuality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Comparison of the two recorded compact cohomology presentations

Source: the identity-open application in sk-cor-wft-curve-upper, using the
cohomology convention def-weil-ordinary-compact-cohomology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedWeil

local instance (l : ℕ) [Fact l.Prime] :
    RingHomInvPair (ULift.ringEquiv.symm.toRingHom :
        PadicAlgCl l →+* CohomologyScalar.{u} l)
      ULift.ringEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm
    (ULift.ringEquiv : CohomologyScalar.{u} l ≃+* PadicAlgCl l)
local instance (l : ℕ) [Fact l.Prime] :
    RingHomInvPair (ULift.ringEquiv.toRingHom : CohomologyScalar.{u} l →+* PadicAlgCl l)
      ULift.ringEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv
    (ULift.ringEquiv : CohomologyScalar.{u} l ≃+* PadicAlgCl l)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (U₀ C₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
  [SmoothOfRelativeDimension 1 C₀.hom]
  (j : U₀ ⟶ C₀) [IsOpenImmersion j.left] [IsDominant j.left]
  (F : NativeL2.WeilModule D l U₀)
  (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)

/-- The strict degree-zero realization of the actual middle Weil image.
Source: sk-thm-wft-curve-middle-upper, its recorded strict-pair construction
(blueprint: lem-a1-middle-compact-cohomology-comparison). -/
def strictMiddle : strictWeilComplexCategory D l hl C₀ WeilCoefficient.qbar :=
  let N := NativeL2.middleWeilImage D l j F
  let Kobj := CategoryTheory.Endofunctor.IsoAlgebra.mk
    ((condensedWeilModuleForget (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius C₀).hom).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj N))
    ((condensedWeilDerivedStructure (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius C₀).hom).app
      ((DerivedCategory.singleFunctor _ 0).obj N))
  ⟨Kobj, NativeCurveWeights.middleImage_strict_bounded D l hl U₀ C₀ j F hF⟩

/-- The cohomology presentation used by the middle-extension weight theorem.
Source: sk-thm-wft-curve-middle-upper, displayed compact cohomology
(blueprint: lem-a1-middle-compact-cohomology-comparison). -/
abbrev globalMiddleH (c₀ : Compactification C₀.hom) (r : ℤ) :=
  (ModuleCat.restrictScalars (Profinite.PadicAlgCl.constRingHom l)).obj
    ((condensedRingCompactCohomology (Profinite.padicAlgClRingObj l)
      (compactBase D C₀ c₀) r).obj (strictMiddle D l hl U₀ C₀ j F hF).obj.carrier)

/-- The global Frobenius operator in that same presentation.
Source: sk-thm-wft-curve-middle-upper, recorded global operator
(blueprint: lem-a1-middle-compact-cohomology-comparison). -/
abbrev globalMiddleOperator (c₀ : Compactification C₀.hom) (r : ℤ) :
    End (globalMiddleH D l hl U₀ C₀ j F hF c₀ r) :=
  (ModuleCat.restrictScalars (Profinite.PadicAlgCl.constRingHom l)).map
    (GlobalGeometricFrobenius.globalGeometricFrobeniusOnCohomology D l hl C₀
      WeilCoefficient.qbar (compactBase D C₀ c₀)
      (strictMiddle D l hl U₀ C₀ j F hF) r).2

/-- The explicit scalar comparison between the two cohomology presentations.
Source: def-weil-ordinary-compact-cohomology, H^r of exact point evaluation.
(blueprint: lem-a1-middle-compact-cohomology-comparison). -/
def middleCohomologyComparison (c₀ : Compactification C₀.hom) (r : ℤ) :
    globalMiddleH D l hl U₀ C₀ j F hF c₀ r ≃ₛₗ[
      (ULift.ringEquiv.symm.toRingHom : PadicAlgCl l →+* CohomologyScalar.{u} l)]
      compactH D l C₀ c₀ (NativeL2.middleWeilImage D l j F) r := by
  let N := NativeL2.middleWeilImage D l j F
  let S := condensedRingCoefficientSections (Profinite.padicAlgClRingObj l)
    (Spec (.of D.k))
  have : PreservesFiniteLimits S := (finite_point_sections_exact _ D.k).1
  have : PreservesFiniteColimits S := (finite_point_sections_exact _ D.k).2
  let R := ModuleCat.restrictScalars
    ((Profinite.PadicAlgCl.constRingHom l).comp
      (ULift.ringEquiv.toRingHom : CohomologyScalar.{u} l →+* PadicAlgCl l))
  let C := rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
    (compactBase D C₀ c₀)
  let e := R.mapIso ((S.rightDerivedFunctorHomologyFunctorIso r).symm.app
    (C.obj (strictMiddle D l hl U₀ C₀ j F hF).obj.carrier))
  let e' := (condensedCompactCohomology l (compactBase D C₀ c₀) r).mapIso
    (((condensedWeilModuleForget (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius C₀).hom).mapDerivedCategorySingleFunctor 0).app N)
  let t : globalMiddleH D l hl U₀ C₀ j F hF c₀ r ≃ₛₗ[
      (ULift.ringEquiv.symm.toRingHom : PadicAlgCl l →+* CohomologyScalar.{u} l)]
      R.obj ((DerivedCategory.homologyFunctor _ r).obj
        (S.rightDerivedFunctor.obj
          (C.obj (strictMiddle D l hl U₀ C₀ j F hF).obj.carrier))) :=
    { __ := AddEquiv.refl _
      map_smul' := fun _ _ ↦ rfl }
  exact t.trans (e.toLinearEquiv.trans e'.toLinearEquiv)

end WeilConjectures.CondensedWeil
