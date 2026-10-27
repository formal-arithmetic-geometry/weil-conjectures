/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.Paper.TameInertiaContinuousKoszul
public import Sheaf.CategoryTheory.CondensedDerivedInvariants
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Scalar tensor and unit-normalized mate data for tame inertia

Source: paragraph (3) of the direct-image stability proof and Stacks Tag 07A6
(blueprint: def-sfb-tame-inertia-scalar-mate-data).

These are the existing scalar-mate definitions, extracted unchanged so that the
ordinary and derived tensor computations can be stated without circular imports.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.TameInertiaScalarMate

open TameInertiaKoszul

variable (E Ω : Type u) [NormedField E] [NormedField Ω] [Algebra E Ω]
  (h : Continuous (algebraMap E Ω))

/-- The actual balanced internal scalar tensor, using the existing coequalizer.
Source: C_Omega tensor_{C_E} -
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
abbrev tensor : CondensedAction.Modules (ring E) ⥤ CondensedAction.Modules (ring Ω) :=
  Mod.extendScalars (coefficientMap E Ω h).hom

/-- The section represented by z tensor x. The ordinary scalar unit is literally
`Mod.extendUnit`, so this generator belongs to the existing balanced tensor object.
Source: the displayed degreewise representative
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def tensorGenerator (A : CondensedAction.Modules (ring E)) (S : Profinite.{u})
    (z : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (ring Ω).X).obj (op S))
    (x : CondensedAction.sectionModule (ring E) A S) :
    CondensedAction.sectionModule (ring Ω) ((tensor E Ω h).obj A) S :=
  z • (show CondensedAction.sectionModule (ring Ω) ((tensor E Ω h).obj A) S from
    (((Mod.extendUnit (coefficientMap E Ω h).hom A).hom.hom.app (op S)).hom x))

variable [(coefficientRestriction E Ω h).Additive]
  [PreservesFiniteLimits (coefficientRestriction E Ω h)]
  [PreservesFiniteColimits (coefficientRestriction E Ω h)]

/-- A universal left derived pair for the existing scalar tensor and its unit-normalized
adjunction to exact scalar restriction. This specifies the transported adjunction of
`SheafOfModules.sheafRingDerivedCoefficientAdjunction`, not an arbitrary adjunction.
The unit equation holds after the canonical comparison on every complex, and thus
fixes the derived adjunction, including its scalar unit.
Source: Stacks 07A6, as used in steps 4-5 of the scalar-mate calculation
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
structure DerivedTensor where
  /-- Ordinary unbounded total left derived scalar extension. -/
  functor : DerivedCategory (CondensedAction.Modules (ring E)) ⥤
    DerivedCategory (CondensedAction.Modules (ring Ω))
  /-- Its canonical computation comparison, directed from derived to ordinary tensor. -/
  comparison : DerivedCategory.Qh ⋙ functor ⟶
    (tensor E Ω h).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  /-- The universal property at all quasi-isomorphisms. -/
  universal : functor.IsLeftDerivedFunctor comparison
    (HomotopyCategory.quasiIso (CondensedAction.Modules (ring E)) (.up ℤ))
  /-- Adjunction to the actual termwise scalar restriction. -/
  adjunction : functor ⊣ (coefficientRestriction E Ω h).mapDerivedCategory
  /-- The actual scalar unit, with exact-functor transports displayed. -/
  unit : ∀ P : HomotopyCategory (CondensedAction.Modules (ring E)) (.up ℤ),
    adjunction.unit.app (DerivedCategory.Qh.obj P) ≫
      (coefficientRestriction E Ω h).mapDerivedCategory.map (comparison.app P) ≫
      (coefficientRestriction E Ω h).mapDerivedCategoryFactorsh.hom.app
        (((tensor E Ω h).mapHomotopyCategory (.up ℤ)).obj P) =
    DerivedCategory.Qh.map
      (((Mod.extendRestrictAdjunction (coefficientMap E Ω h).hom).mapHomotopyCategory
        (.up ℤ)).unit.app P)

variable (p ℓ r : ℕ) [ActionAbelianData p r E] [ActionAbelianData p r Ω]
  [Context p r E] [Context p r Ω] [ScalarRestriction E p r Ω h]
  [RestrictionUniversal E p r Ω h]
  (dE : Realization E p ℓ r E) (dΩ : Realization E p ℓ r Ω)
  (m : CoefficientMaps E p ℓ r Ω h dE dΩ)

/-- The chain map adjunct to the literal coefficient inclusion. Thus neither the chain
map nor its source is an arbitrary isomorphic replacement.
Source: t in step 3 (blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def tensorMap (M : Inputs E p ℓ r) :
    ((tensor E Ω h).mapHomologicalComplex (.up ℤ)).obj (dE.koszul.obj M) ⟶
      dΩ.koszul.obj M :=
  (((Mod.extendRestrictAdjunction (coefficientMap E Ω h).hom).mapHomologicalComplex
    (.up ℤ)).homEquiv _ _).symm (m.koszul.app M)

/-- The actual derived scalar-adjunction adjunct of the recorded coefficient unit
followed by the invariant/scalar-restriction comparison.
Source: sigma_M in the statement
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def mate (s : DerivedTensor E Ω h) (M : Inputs E p ℓ r) :
    s.functor.obj ((derivedInvariants E p ℓ r E dE).obj M) ⟶
      (derivedInvariants E p ℓ r Ω dΩ).obj M :=
  (s.adjunction.homEquiv _ _).symm
    (representationCoefficient E p ℓ r Ω h dE dΩ m M)

end Profinite.TameInertiaScalarMate
