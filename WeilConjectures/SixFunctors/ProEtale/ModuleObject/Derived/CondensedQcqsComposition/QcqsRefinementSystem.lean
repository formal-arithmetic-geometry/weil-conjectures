/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs

/-! Coherent compactification system for one qcqs morphism.
(blueprint: new-p3-qcqs-refinement-system)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
open CompactSupportComposition
variable (ℓ : ℕ) [Fact ℓ.Prime]
def RefinementSystemData {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Nonempty (System ℓ f)

/-- Extract the coherent system already contained in the bounded qcqs theorem.
Source: `condensedShriekBoundedQcqs`, its preservation and coherent-comparison clauses. -/
private theorem systemOfBoundedQcqs
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] : RefinementSystemData ℓ f.left := by
  have h := condensedShriekBoundedQcqs ℓ k f
  obtain ⟨hcomp, htriX, htriY, hpres, htri, hopen, ⟨τ, hτr, hτid, hτcoc⟩,
    hvan, hneg⟩ := h
  change Nonempty (System ℓ f.left)
  exact ⟨System.mk hpres τ hτr hτid hτcoc⟩

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
