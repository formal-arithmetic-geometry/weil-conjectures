/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis

/-! # Condensed cosupport over a finite or algebraically closed field

Source: latest blueprint, def-per-support-condition; Wei Yang #1441 item 36.
(blueprint: def-per-support-condition).
This extends the recorded interface to all the authorized algebraically closed fields.
No condition that every nonzero field element has finite multiplicative order is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified exceptional image of the coefficient unit along the structure map.
Finite cohomological dimension follows from finiteness or algebraic closedness alone.
Source: def-per-support-condition, dualizing-object paragraph; Wei Yang #1441 item 36
(blueprint: def-per-support-condition). -/
def finiteOrClosedDualizingObject (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k) (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)) :=
  letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
  let hcd : BaseFieldFiniteCD ell k := hk.elim
    (fun h ↦ @BaseFieldFiniteCD.of_finite ell _ k _ h)
    (fun h ↦ @BaseFieldFiniteCD.of_isAlgClosed ell _ k _ h)
  ((ctfExceptionalInverseImage (Profinite.padicAlgClRingObj ell) ell k hcd
      (Over.mkIdTerminal.from X)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))))).obj
    ⟨𝟙_ _, condensedCoefficientUnit_mem (Profinite.padicAlgClRingObj ell) (Spec (.of k))⟩).obj

/-- Actual relative derived internal Hom into the specified structural dualizing object.
Source: def-per-support-condition, displayed Verdier dual
(blueprint: def-per-support-condition). -/
def finiteOrClosedPerverseDual (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k) (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)) :=
  ((derivedHom (Profinite.padicAlgClRingObj ell) X.left).obj (op K.obj)).obj
    (finiteOrClosedDualizingObject ell hk X)

/-- Cosupport is the registered ambient support inequality applied to the actual dual.
Source: def-per-support-condition, final equivalence
(blueprint: def-per-support-condition). -/
def FiniteOrClosedCosupportCondition (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k) (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)) : Prop :=
  CondensedAmbientSupportCondition (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)
    (finiteOrClosedPerverseDual ell hk X K)

end AlgebraicGeometry.ProEtale.CondensedRing
