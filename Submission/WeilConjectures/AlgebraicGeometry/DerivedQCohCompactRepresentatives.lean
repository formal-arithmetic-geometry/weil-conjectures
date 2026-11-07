/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Submission.WeilConjectures.CategoryTheory.CompactObject
import Submission.WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplexRepresentatives
public import Mathlib.AlgebraicGeometry.Noetherian
import Submission.WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import Submission.WeilConjectures.AlgebraicGeometry.SupportedDerivedGeneratedPerfect
import Submission.WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import Submission.WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import Submission.WeilConjectures.AlgebraicGeometry.PerfectThickClosure
import Submission.WeilConjectures.CategoryTheory.CompactGeneratorAmbientThick

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Small representatives of compact quasi-coherent derived objects

Source: Stacks Project, Tags 09M1 and 09IS; perfect-complex representative argument.
(blueprint: lem-sc-derived-qcoh-compact-representatives).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Derived categories exist on all open subschemes of a Noetherian scheme.
Source: Grothendieck abelianity of sheaves of modules on a small ringed site
and `HasDerivedCategory.ofIsGrothendieckAbelian`.
(blueprint: lem-sc-derived-qcoh-compact-open-categories) -/
theorem noetherian_open_derived_categories_exists (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    Nonempty (∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) := by
  exact nonempty_derivedOpenLocalization X

/-- Perfectness is unchanged by an isomorphism of ambient derived objects. -/
private theorem perfect_of_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E F : schemeDerivedCategory X} (e : E ≅ F) (hE : Scheme.IsPerfect X E) :
    Scheme.IsPerfect X F := by
  intro x
  obtain ⟨U, hx, K, hK, ⟨eK⟩⟩ := hE x
  exact ⟨U, hx, K, hK, ⟨((SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e.symm) ≪≫ eK⟩⟩

/-- The concrete perfect-complex closure theorem supplies Mathlib's thick-property API. -/
private theorem perfect_thick_property (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (G : schemeDerivedCategory X) (hG : Scheme.IsPerfect X G) :
    (Scheme.perfectSubcategory X).IsTriangulated ∧
      (Scheme.perfectSubcategory X).IsStableUnderRetracts := by
  let : Zero (schemeDerivedCategory X) := HasZeroObject.zero' (schemeDerivedCategory X)
  obtain ⟨htri, hsum, hshift, _⟩ := Scheme.perfect_thick_closure.{u, w, u} X
  let Q := Scheme.perfectSubcategory X
  have hiso : Q.IsClosedUnderIsomorphisms := by
    constructor
    intro E F e hE
    exact perfect_of_iso X e hE
  let := hiso
  have hret : Q.IsStableUnderRetracts := by
    constructor
    intro E F r hF
    obtain ⟨Z, a, b, ht⟩ := Pretriangulated.distinguished_cocone_triangle r.i
    let T := Pretriangulated.Triangle.mk r.i a b
    have hb : T.mor₃ = 0 :=
      T.mor₃_eq_zero_of_mono₁ ht (show Mono r.i from inferInstance)
    obtain ⟨e, _, _⟩ := Pretriangulated.exists_iso_binaryBiproduct_of_distTriang T ht hb
    exact (hsum E Z (perfect_of_iso X e hF)).1
  let := hret
  have hzero : Q.ContainsZero :=
    ⟨0, isZero_zero _, Q.prop_of_retract ((isZero_zero _).retract G) hG⟩
  let := hzero
  have hsh : Q.IsStableUnderShift ℤ := by
    constructor
    intro n
    exact ObjectProperty.IsStableUnderShiftBy.mk (fun E hE ↦ hshift E n hE)
  let := hsh
  have hcone : Q.IsTriangulatedClosed₂ := by
    apply ObjectProperty.IsTriangulatedClosed₂.mk'
    intro T ht h₁ h₃
    exact (htri T ht).2.2 h₁ h₃
  let := hcone
  exact ⟨ObjectProperty.IsTriangulated.mk, hret⟩

/-- Perfect objects on a Noetherian scheme are compact in its QCoh derived category.
Source: Stacks Project, Tag 09M1, the perfect-to-compact implication, using
tensor-Hom duality and preservation of coproducts.
(blueprint: lem-sc-derived-qcoh-perfect-compact-noetherian)
This is the Noetherian specialization of `perfectObjectCompact`; all local
derived-category and quasi-compactness infrastructure is discharged in the
intermediate theorem. -/
theorem noetherian_perfect_compact (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hOpen : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ (P : schemeDerivedQCohCategory X), Scheme.IsPerfect X P.obj → IsCompactObject P := by
  exact perfectObjectCompact X

end AlgebraicGeometry
