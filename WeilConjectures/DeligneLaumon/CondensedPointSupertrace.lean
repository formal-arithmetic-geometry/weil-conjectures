/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval

/-! # Ordinary condensed complexes on a geometric point: splitting and supertrace

Source: latest Weil blueprint, sec-deligne-laumon-a1,
`sk-p-dl-a1-some-weight/lem-fd-realness-pushforward.proof.md`, Step 1
(blueprint: lem-fd-condensed-point-supertrace).

The section spaces below are literally evaluation of cohomology at the terminal
small pro-etale object. Their scalar action is transported through the canonical
map sending a homomorphism from the regular module to its value at one.
All derived objects belong to the ordinary internal-module derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- The existing Hom presentation of point sections, with the harmless scalar ULift removed.
Source: blueprint fibre calculation, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
abbrev fdPointHomSections : PointMod ℓ k ⥤ ModuleCat.{u + 1} (PadicAlgCl ℓ) :=
  pointSections ℓ k ⋙ ModuleCat.restrictScalars
    (ULift.ringEquiv.symm.toRingHom : PadicAlgCl ℓ →+* ULift.{u + 1} (PadicAlgCl ℓ))

/-- Literal terminal-object sections of a module, before scalar transport.
Source: blueprint definition of V_i, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
def fdPointTerminalSections (M : PointMod ℓ k) : Type (u + 1) :=
  M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

/-- The additive group on terminal sections is the original evaluated additive group.
Source: blueprint definition of V_i, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
instance fdPointTerminalSectionsAddCommGroup (M : PointMod ℓ k) :
    AddCommGroup (fdPointTerminalSections ℓ k M) :=
  inferInstanceAs (AddCommGroup
    (M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))))

/-- Evaluate a regular-module homomorphism at the coefficient unit section one.
The sheaf-to-presheaf unit comparison provides that section without a choice.
Source: blueprint terminal-section convention, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
def fdPointEvaluateOne (M : PointMod ℓ k) (f : (fdPointHomSections ℓ k).obj M) :
    fdPointTerminalSections ℓ k M :=
  (Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId (Spec (.of k))) M.X)
    ((MonObj.one : 𝟙_ _ ⟶ condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))) ≫ f.hom)

/-- The canonical evaluation at one is additive and bijective onto terminal sections.
Source: blueprint terminal-section convention, Step 1
(blueprint: lem-fd-condensed-point-supertrace).
Proof: regular-module homomorphisms are uniquely determined by composition with
one, by Mod.regular_hom_ext, with inverse Mod.regularLift. Morphisms from the
integer tensor unit into an abelian sheaf are its global sections. On a site with
terminal object these are its sections at that object: restrict the given section
along the unique arrow from each test object. Sheafification adjunction identifies
this prescription with the displayed evaluation through its unit comparison.
All these maps are additive because the actions and restrictions are additive. -/
theorem fdPointEvaluateOne_properties (M : PointMod ℓ k) :
    Function.Bijective (fdPointEvaluateOne ℓ k M) ∧
      ∀ f g : (fdPointHomSections ℓ k).obj M,
        fdPointEvaluateOne ℓ k M (f + g) =
          fdPointEvaluateOne ℓ k M f + fdPointEvaluateOne ℓ k M g := by
  let e := (CategoryTheory.Mod.regularHomAddEquiv M).trans
    (Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId (Spec (.of k))) M.X)
  exact ⟨e.bijective, e.map_add⟩

/-- The additive equivalence whose forward map is the explicitly specified evaluation.
Source: blueprint terminal-section convention, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
def fdPointSectionsEquiv (M : PointMod ℓ k) :
    (fdPointHomSections ℓ k).obj M ≃+ fdPointTerminalSections ℓ k M :=
  { Equiv.ofBijective (fdPointEvaluateOne ℓ k M)
      (fdPointEvaluateOne_properties ℓ k M).1 with
    map_add' := (fdPointEvaluateOne_properties ℓ k M).2 }

/-- Scalars on terminal sections are the constant coefficient scalars, via evaluation at one.
Source: blueprint terminal-section convention, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
instance fdPointTerminalSectionsModule (M : PointMod ℓ k) :
    Module (PadicAlgCl ℓ) (fdPointTerminalSections ℓ k M) :=
  (fdPointSectionsEquiv ℓ k M).symm.module (PadicAlgCl ℓ)

/-- Terminal sections as a vector space canonically identified with regular-module Hom.
Source: blueprint definition of V_i, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
def fdPointSectionsLinearEquiv (M : PointMod ℓ k) :
    fdPointTerminalSections ℓ k M ≃ₗ[PadicAlgCl ℓ] (fdPointHomSections ℓ k).obj M :=
  (fdPointSectionsEquiv ℓ k M).symm.linearEquiv (PadicAlgCl ℓ)

/-- V_i is literally the terminal evaluation of H^i(P), with its coefficient action.
Source: blueprint fibre calculation, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
abbrev fdPointCohomologySections (P : DerivedCategory (PointMod ℓ k)) (i : ℤ) :=
  fdPointTerminalSections ℓ k ((DerivedCategory.homologyFunctor (PointMod ℓ k) i).obj P)

/-- The induced linear endomorphism of terminal cohomology sections.
Source: blueprint fibre calculation, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
def fdPointCohomologyEnd (P : DerivedCategory (PointMod ℓ k)) (v : P ⟶ P) (i : ℤ) :
    Module.End (PadicAlgCl ℓ) (fdPointCohomologySections ℓ k P i) :=
  (fdPointSectionsLinearEquiv ℓ k
    ((DerivedCategory.homologyFunctor (PointMod ℓ k) i).obj P)).symm.conj
      ((fdPointHomSections ℓ k).map
        ((DerivedCategory.homologyFunctor (PointMod ℓ k) i).map v)).hom

/-- Constant scalar multiplication on the actual ordinary derived tensor unit.
Source: blueprint canonical unit endomorphism ring, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
def fdPointScalar : PadicAlgCl ℓ →+* End (𝟙_ (DerivedCategory (PointMod ℓ k))) :=
  (DerivedCategory.singleFunctorObjUnitIso (PointMod ℓ k)).conjRingEquiv.toRingHom.comp
    (((DerivedCategory.singleFunctor (PointMod ℓ k) 0).mapEndRingHom
      (𝟙_ (PointMod ℓ k))).comp (pointUnitEndRingHom ℓ k))

/-- The categorical trace with the recorded native derived Koszul braiding and a chosen dual.
Source: blueprint fibre calculation, Step 1; sk-d-trace
(blueprint: lem-fd-condensed-point-supertrace). -/
def fdPointTrace (P : DerivedCategory (PointMod ℓ k)) (dual : HasRightDual P)
    (v : P ⟶ P) : End (𝟙_ (DerivedCategory (PointMod ℓ k))) :=
  @CategoryTheory.MonoidalCategory.trace _ _ _
    (ModuleObjectRingedComparison.internalBraiding (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of k))) P dual v

/-- A finite power of the shifted derived tensor unit.
Source: blueprint finite shifted sum, Step 1
(blueprint: lem-fd-condensed-point-supertrace). -/
def fdPointShiftPower (i : ℤ) (n : ℕ) : DerivedCategory (PointMod ℓ k) :=
  ⨁ (fun _ : Fin n => (shiftFunctor (DerivedCategory (PointMod ℓ k)) (-i)).obj
    (𝟙_ (DerivedCategory (PointMod ℓ k))))

/-- Finiteness, splitting, dualizability, unit scalars and the cohomological supertrace.
Source: latest blueprint, lem-fd-realness-pushforward.proof.md, Step 1
(blueprint: lem-fd-condensed-point-supertrace).
Proof:
1. Apply def-weil-finite-coefficient-point in its ordinary condensed interpretation
and lem-weil-point-proetale-sections-exact. Exact terminal sections commute naturally
with cohomology, giving finite-dimensional V_i with finite support.
2. Apply lem-trf-field-complex-cohomology-splitting over Omega, choose bases of V_i,
and transport its zero-differential model back to the actual coefficient sheaf.
This gives the displayed finite sum. Full faithfulness on the unit identifies its
endomorphism ring with Omega, with scalar multiplication giving the canonical map.
3. The model and its degree-reversed linear dual have finite free terms and are
K-flat by lem-sfb-bounded-above-flat-kflat. Coevaluation is the sum of basis/dual-basis
pairs, and evaluation is the Kronecker pairing. Both triangular identities follow
by contraction, proving existence of a right dual for the given relative tensor.
4. The symmetry def-sfb-native-derived-koszul-braiding contributes (-1)^(i*(-i)),
which equals (-1)^i in every integer degree. Evaluation of the trace composite is
therefore the sum of signed diagonal matrix entries, namely the displayed supertrace.
5. Transport the dual along the splitting isomorphism. Naturality of the braiding
cancels that isomorphism in the trace composite. Independence of the chosen dual
is lem-zl-dualizable-categorical-trace-conjugacy applied to the identity isomorphism.
Support in degree zero or one leaves respectively the positive or negative trace;
empty support gives the zero object and the empty sum. All coefficients are ordinary
pulled-back condensed coefficients throughout. -/
theorem condensed_point_supertrace
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hne : ℓ ≠ D.p)
    (P : DerivedCategory (PointMod ℓ D.k))
    (_hP : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of D.k))) P) :
    (∀ i : ℤ, FiniteDimensional (PadicAlgCl ℓ) (fdPointCohomologySections ℓ D.k P i)) ∧
    (∃ s : Finset ℤ,
      (∀ i : ℤ, i ∉ s → Subsingleton (fdPointCohomologySections ℓ D.k P i)) ∧
      Nonempty (P ≅ ⨁ fun i : s =>
        fdPointShiftPower ℓ D.k i
          (Module.finrank (PadicAlgCl ℓ) (fdPointCohomologySections ℓ D.k P i)))) ∧
    IsDualizable P ∧
    Function.Bijective (fdPointScalar ℓ D.k) ∧
    (∀ (dual : HasRightDual P) (v : P ⟶ P),
      fdPointTrace ℓ D.k P dual v = fdPointScalar ℓ D.k
        (∑ᶠ i : ℤ, (i.negOnePow : ℤ) •
          LinearMap.trace (PadicAlgCl ℓ) (fdPointCohomologySections ℓ D.k P i)
            (fdPointCohomologyEnd ℓ D.k P v i))) ∧
    (∀ (dual : HasRightDual P) (v : P ⟶ P),
      (∀ i : ℤ, i ≠ 0 → IsZero
        ((DerivedCategory.homologyFunctor (PointMod ℓ D.k) i).obj P)) →
      fdPointTrace ℓ D.k P dual v = fdPointScalar ℓ D.k
        (LinearMap.trace (PadicAlgCl ℓ) (fdPointCohomologySections ℓ D.k P 0)
          (fdPointCohomologyEnd ℓ D.k P v 0))) ∧
    (∀ (dual : HasRightDual P) (v : P ⟶ P),
      (∀ i : ℤ, i ≠ 1 → IsZero
        ((DerivedCategory.homologyFunctor (PointMod ℓ D.k) i).obj P)) →
      fdPointTrace ℓ D.k P dual v = fdPointScalar ℓ D.k
        (-LinearMap.trace (PadicAlgCl ℓ) (fdPointCohomologySections ℓ D.k P 1)
          (fdPointCohomologyEnd ℓ D.k P v 1))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
