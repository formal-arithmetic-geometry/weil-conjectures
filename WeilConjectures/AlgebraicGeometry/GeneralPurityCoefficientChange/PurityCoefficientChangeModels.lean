/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit

/-! # Finite coefficient-field models for the coefficient-change proposition

Source: sk-thm-sfb-qlbar-two-colimit (3), applied in Step 7 of the proof of
`det-sp-purity-coefficient-change` (blueprint: lem-pur-coefficient-closure-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange

/-- Every constructible finite-Tor object over the algebraic closure of the coefficient
field descends to a finite coefficient field, with the ordinary derived scalar functor.
Source: sk-thm-sfb-qlbar-two-colimit (3), coefficient-change proof Step 7
(blueprint: lem-pur-coefficient-closure-models).
Proof: apply the finite coefficient-descent theorem to the bounded constructible
underlying object. Its last clause identifies the rational constructible category with
its finite-Tor subcategory, so the descended object has the required Tor amplitude.
The scalar functor is the same ordinary left derived extension along the finite-field
inclusion. No model or isomorphism is chosen in a definition. -/
theorem closure_models (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : (Coefficient.closure (ell := ell)).ctf ell X.left) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
      (K₀ : (Coefficient.rational E).ctf ell X.left),
      Nonempty ((scalarSixChange
        (⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩ :
          (Coefficient.rational E).bundled ell ⟶
            (Coefficient.closure (ell := ell)).bundled ell) X.left).obj K₀.obj ≅ K.obj) := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  let : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  have h := finiteCoefficientDescentTwoColimit k (ringChar k) ell
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ell) X.left
  obtain ⟨E, M, ⟨e⟩⟩ := h.2.2.1 ⟨K.obj, K.property.1⟩
  have hM : property ell (.rational E) X.left M.obj := by
    exact (congrFun (h.2.2.2.1 E).2 M.obj).mpr M.property
  exact ⟨E, ⟨M.obj, hM⟩, ⟨e⟩⟩

end AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange
