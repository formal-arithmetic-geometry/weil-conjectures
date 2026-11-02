/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology

/-! # Native condensed conventions for weight theory

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done/def-tw-conventions.md
(blueprint: def-tw-conventions).

The finite-field and geometric data specialize the existing ordinary condensed
pro-etale module derived category and its bounded constructible full subcategory.
The coefficient ring is the finite-subextension-valued condensed Qbar ring, and
compact cohomology is the recorded compact-support sections followed by homology.

## Main definitions

* `CondensedTwConventions` fixes the field, prime and geometric data.
* `CondensedTwConventions.coefficientCategory` is the bounded constructible category.
* `CondensedTwConventions.inclusion` is its full inclusion in the ambient category.
* `CondensedTwConventions.compactlySupportedCohomology` is constant compact cohomology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The prime-power finite field, its chosen algebraic closure, a distinct coefficient
prime, and the separated finite-type scheme of the weight conventions.
The Qbar coefficient field is the existing `PadicAlgCl ell` of the condensed setting.
Source: latest blueprint, def-tw-conventions, first three sentences
(blueprint: def-tw-conventions). -/
structure CondensedTwConventions where
  datum : FiniteFieldDatum.{u}
  ell : ℕ
  [prime : Fact ell.Prime]
  different : ell ≠ datum.p
  X : Over (Spec (CommRingCat.of datum.k₀))
  [finite_type : LocallyOfFiniteType X.hom]
  [quasi_compact : QuasiCompact X.hom]
  [separated : IsSeparated X.hom]

/-- The chosen algebraic closure of the finite field is algebraically closed.
Source: latest blueprint, def-tw-conventions, algebraic closure
(blueprint: def-tw-conventions). -/
instance isAlgClosed (T : CondensedTwConventions.{u}) : IsAlgClosed T.datum.k :=
  IsAlgClosure.isAlgClosed T.datum.k₀

attribute [instance] CondensedTwConventions.prime CondensedTwConventions.finite_type
  CondensedTwConventions.quasi_compact CondensedTwConventions.separated

namespace CondensedTwConventions

/-- The actual geometric base change `X ×_k kbar`, with its structure map.
Source: latest blueprint, def-tw-conventions, geometric base change
(blueprint: def-tw-conventions). -/
abbrev geometricBaseChange (T : CondensedTwConventions.{u}) :=
  T.datum.geometricFiber T.X

/-- Finite type of the geometric structure map, inherited by base change.
Source: latest blueprint, def-tw-conventions, separated finite-type hypothesis
(blueprint: def-tw-conventions). -/
instance geometricFiniteType (T : CondensedTwConventions.{u}) :
    LocallyOfFiniteType (T.geometricBaseChange.left ↘ Spec (.of T.datum.k)) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd T.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))))

/-- Quasi-compactness of the geometric structure map, inherited by base change.
Source: latest blueprint, def-tw-conventions, finite-type hypothesis
(blueprint: def-tw-conventions). -/
instance geometricQuasiCompact (T : CondensedTwConventions.{u}) :
    QuasiCompact (T.geometricBaseChange.left ↘ Spec (.of T.datum.k)) :=
  inferInstanceAs (QuasiCompact (pullback.snd T.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))))

/-- Separatedness of the geometric structure map, inherited by base change.
Source: latest blueprint, def-tw-conventions, separated hypothesis
(blueprint: def-tw-conventions). -/
instance geometricSeparated (T : CondensedTwConventions.{u}) :
    IsSeparated (T.geometricBaseChange.left ↘ Spec (.of T.datum.k)) :=
  inferInstanceAs (IsSeparated (pullback.snd T.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))))

/-- Separatedness, stated for the structure morphism of the geometric fibre.
Source: latest blueprint, def-tw-conventions, separated hypothesis
(blueprint: def-tw-conventions). -/
instance geometricSeparatedHom (T : CondensedTwConventions.{u}) :
    IsSeparated T.geometricBaseChange.hom := by
  change IsSeparated (T.geometricBaseChange.left ↘ Spec (.of T.datum.k))
  infer_instance

/-- Local finite type, stated for the structure morphism of the geometric fibre.
Source: latest blueprint, def-tw-conventions, finite-type hypothesis
(blueprint: def-tw-conventions). -/
instance geometricFiniteTypeHom (T : CondensedTwConventions.{u}) :
    LocallyOfFiniteType T.geometricBaseChange.hom := by
  change LocallyOfFiniteType (T.geometricBaseChange.left ↘ Spec (.of T.datum.k))
  infer_instance

/-- Quasi-compactness, stated for the structure morphism of the geometric fibre.
Source: latest blueprint, def-tw-conventions, finite-type hypothesis
(blueprint: def-tw-conventions). -/
instance geometricQuasiCompactHom (T : CondensedTwConventions.{u}) :
    QuasiCompact T.geometricBaseChange.hom := by
  change QuasiCompact (T.geometricBaseChange.left ↘ Spec (.of T.datum.k))
  infer_instance

/-- The pulled-back finite-subextension-valued condensed Qbar ring on `X_kbar`.
Source: latest blueprint, def-tw-conventions, def-sf-setting coefficient convention
(blueprint: def-tw-conventions). -/
abbrev coefficientRing (T : CondensedTwConventions.{u}) :=
  ProEtale.condensedRingObj (Profinite.padicAlgClRingObj T.ell) T.geometricBaseChange.left

/-- The ordinary scalar ring `Qbar(*)` of singleton sections of the condensed Qbar ring.
Source: latest blueprint, def-tw-conventions, Qbar-coefficient cohomology
(blueprint: def-tw-conventions). -/
abbrev scalarRing (T : CondensedTwConventions.{u}) :=
  MonObj.Γ (Profinite.padicAlgClRingObj T.ell)

/-- The derived category of scalar modules exists (Grothendieck abelian category).
Source: latest blueprint, def-tw-conventions, Qbar-coefficient cohomology
(blueprint: def-tw-conventions). -/
instance scalarHasDerived (T : CondensedTwConventions.{u}) :
    HasDerivedCategory (ModuleCat T.scalarRing) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The derived category of `Qbar(*)`-modules, where cohomology complexes take values.
Source: latest blueprint, def-tw-conventions, Qbar-coefficient cohomology
(blueprint: def-tw-conventions). -/
abbrev scalarDerived (T : CondensedTwConventions.{u}) :=
  DerivedCategory (ModuleCat T.scalarRing)

/-- The ordinary unbounded derived category of modules over the condensed coefficient ring.
Source: latest blueprint, def-tw-conventions, displayed ambient derived category
(blueprint: def-tw-conventions). -/
abbrev ambientCategory (T : CondensedTwConventions.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T.geometricBaseChange.left) Ab.{u + 1})
    T.coefficientRing)

/-- The bounded constructible full subcategory, with ambient derived morphisms and no
completeness condition.
Source: latest blueprint, def-tw-conventions, displayed bounded constructible category
(blueprint: def-tw-conventions). -/
abbrev coefficientCategory (T : CondensedTwConventions.{u}) :=
  ProEtale.BoundedConstructible T.coefficientRing

/-- The canonical inclusion of bounded constructible complexes into the ambient category.
Source: latest blueprint, def-tw-conventions, displayed inclusion
(blueprint: def-tw-conventions). -/
abbrev inclusion (T : CondensedTwConventions.{u}) :
    T.coefficientCategory ⥤ T.ambientCategory :=
  (ProEtale.boundedConstructible T.coefficientRing).ι

/-- The constant coefficient object is the pulled-back regular module in degree zero.
Source: latest blueprint, def-tw-conventions, constant-coefficient compact cohomology
(blueprint: def-tw-conventions). -/
abbrev coefficientObject (T : CondensedTwConventions.{u}) : T.ambientCategory :=
  (DerivedCategory.singleFunctor _ 0).obj (Mod.regular T.coefficientRing)

/-- `Fib_s`: the derived terminal sections over the geometric point `Spec kbar`, with the
scalar action of the condensed Qbar ring (`condensedRingCoefficientSections`).
Source: latest blueprint, def-weil-ordinary-compact-cohomology, Fib_s
(blueprint: def-tw-conventions). -/
abbrev pointFiber (T : CondensedTwConventions.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of T.datum.k)))
      Ab.{u + 1})
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj T.ell)
        (Spec (.of T.datum.k)))) ⥤ T.scalarDerived :=
  (AlgebraicGeometry.ProEtale.CondensedRing.condensedRingCoefficientSections
    (Profinite.padicAlgClRingObj T.ell) (Spec (.of T.datum.k))).rightDerivedFunctor

/-- The Nagata compactification of the geometric structure map, used for compact support.
Source: latest blueprint, def-weil-ordinary-compact-cohomology, compactification in RΓ_c
(blueprint: def-tw-conventions). -/
abbrev compactification (T : CondensedTwConventions.{u}) :
    Compactification T.geometricBaseChange.hom :=
  NagataCompactification T.geometricBaseChange.hom

/-- `RΓ(X_kbar, -) = Fib_s ∘ Ra_*`: the ordinary coefficient complex of
def-weil-ordinary-compact-cohomology for the Qbar ring and the geometric structure map.
Source: latest blueprint, def-weil-ordinary-compact-cohomology, RΓ formula
(blueprint: def-tw-conventions). -/
abbrev ordinaryCoefficientComplex (T : CondensedTwConventions.{u}) :
    T.ambientCategory ⥤ T.scalarDerived.{u} :=
  AlgebraicGeometry.ProEtale.CondensedRing.condensedRingOrdinaryCoefficientComplex
    (Profinite.padicAlgClRingObj T.ell) T.geometricBaseChange.hom

/-- `RΓ_c(X_kbar, -) = Fib_s ∘ Ra_!`: the compact coefficient complex of
def-weil-ordinary-compact-cohomology on the Nagata compactification.
Source: latest blueprint, def-tw-conventions, compact-support convention, and
def-weil-ordinary-compact-cohomology, displayed RΓ_c formula
(blueprint: def-tw-conventions). -/
abbrev compactSections (T : CondensedTwConventions.{u}) :
    T.ambientCategory ⥤ T.scalarDerived.{u} :=
  AlgebraicGeometry.ProEtale.CondensedRing.condensedRingCompactCoefficientComplex
    (Profinite.padicAlgClRingObj T.ell) T.compactification

/-- Compactly supported cohomology of the constant condensed Qbar coefficient object,
in every integer degree, over the ordinary scalar ring Qbar(*).
Source: latest blueprint, def-tw-conventions, final clause, and
def-weil-ordinary-compact-cohomology, displayed Hc formula
(blueprint: def-tw-conventions). -/
abbrev compactlySupportedCohomology (T : CondensedTwConventions.{u}) (i : ℤ) :=
  (AlgebraicGeometry.ProEtale.CondensedRing.condensedRingCompactCohomology
    (Profinite.padicAlgClRingObj T.ell) T.compactification i).obj T.coefficientObject

end CondensedTwConventions
end WeilConjectures
