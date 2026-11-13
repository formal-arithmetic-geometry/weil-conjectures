/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.AlgebraicGeometry.SupportedPerfectGenerator
import WeilConjectures.AlgebraicGeometry.SupportedDerivedGeneratedPerfectCore
import WeilConjectures.AlgebraicGeometry.PerfectObjectCompact

/-! # Existence of a single perfect generator

## References

* Stacks Project, Derived Categories of Schemes, Tag 09IS.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a quasi-compact and quasi-separated scheme, a single perfect complex generates the
quasi-coherent derived category (Stacks, Tag 09IS). -/
theorem exists_perfect_generator (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ P : schemeDerivedCategory X, Scheme.IsPerfect X P ∧ schemeDerivedQCohProperty X P ∧
      (∀ E : schemeDerivedQCohCategory X,
        IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P⟦n⟧ ⟶ E.obj)) ∧
      ∀ Q : ObjectProperty (schemeDerivedCategory X),
        Q.IsTriangulated → Q.IsStableUnderRetracts →
        (∀ I : Type u, Q.IsClosedUnderColimitsOfShape (Discrete I)) →
        Q P → ∀ E : schemeDerivedQCohCategory X, Q E.obj := by
  classical
  obtain ⟨htri, P, hP, _, hgen⟩ :=
    supported_perfect_generator X Set.univ isClosed_univ (by simp)
  have hdetect : ∀ E : schemeDerivedQCohCategory X,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P.obj⟦n⟧ ⟶ E.obj) := by
    intro E
    exact hgen E (by simp)
  refine ⟨P.obj, hP, P.property, hdetect, ?_⟩
  intro Q hQtri _ hQsums hQP E
  let := hQtri
  have htri' : ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory X ↦
      schemeDerivedQCohProperty X K ∧
        ∀ (k : ℤ) (x : X), x ∉ ((⊥ : X.Opens) : Set X)ᶜ →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) k).obj K).val.presheaf x))) := by
    simpa using htri
  obtain ⟨K, t, hzero, hsteps, S, ⟨hS⟩, s, q, r, _, hT⟩ :=
    supported_derived_generated_perfect_core X ⊥ P E htri'
      (perfectObjectCompact X P hP) (by simp)
      (fun M _ ↦ hdetect M) (by simp)
  have hsum (I : Type u) (A : I → schemeDerivedCategory X)
      (c : Cofan A) (hc : IsColimit c) (hA : ∀ i, Q (A i)) : Q c.pt := by
    let := hQsums I
    exact Q.prop_of_isColimit hc (fun i ↦ hA i.as)
  have hK : ∀ n, Q (K n).obj := by
    intro n
    induction n with
    | zero => exact Q.prop_of_isZero hzero
    | succ n ih =>
      obtain ⟨I, m, c, ⟨hc⟩, a, b, ht⟩ := hsteps n
      have hC : Q c.pt := hsum I _ c hc (fun i ↦ Q.le_shift (m i) _ hQP)
      exact Q.ext_of_isTriangulatedClosed₂ _ ht ih hC
  let S' : Cofan (fun n : ULift.{u} ℕ ↦ (K n.down).obj) :=
    Cofan.mk S.pt (fun n ↦ S.inj n.down)
  have hS' : IsColimit S' := (Cofan.isColimitEquivOfEquiv Equiv.ulift S) hS
  have hQS : Q S.pt := hsum (ULift.{u} ℕ) _ S' hS' (fun n ↦ hK n.down)
  exact Q.ext_of_isTriangulatedClosed₃ _ hT hQS hQS

end AlgebraicGeometry
