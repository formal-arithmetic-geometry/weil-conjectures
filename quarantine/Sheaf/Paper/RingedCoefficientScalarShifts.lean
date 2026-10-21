/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # Counit-normalized shifts for derived scalar extension

Source: Stacks Project, Derived Categories, Tag 05SU
(blueprint: lem-pur-coefficient-scalar-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory
namespace SheafOfModules.RingedCoefficientProjection

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (p : Scalars.{c, v, r} J)

/-- A coherent integer shift on each scalar extension, normalized by its universal
computation counit. Source: Stacks 05SU
(blueprint: lem-pur-coefficient-scalar-shifts). -/
structure ScalarShifts where
  [scalar : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).derived.CommShift ℤ]
  canonical : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (p a).counit ℤ

/-- The scalar universal counits determine coherent integer shifts.
Source: Stacks Project, Derived Categories, Tag 05SU
(blueprint: lem-pur-coefficient-scalar-shifts).

Proof: the ordinary additive scalar functor induces a termwise functor on the
homotopy category, hence commutes coherently with every integer shift. The
localization Qh has its canonical shift structure. A left derived functor is a
right Kan extension along Qh. Apply coherent shift transport for right Kan
extensions to this counit for every coefficient map. Kan uniqueness determines
all shift comparisons and their zero and addition coherence, with precisely the
required counit compatibility. No flatness of a coefficient map is used. -/
theorem coefficientScalarShifts : Nonempty (ScalarShifts p) := by
  classical
  have h {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
      ∃ hshift : (p a).derived.CommShift ℤ,
        letI := hshift
        NatTrans.CommShift (p a).counit ℤ := by
    let := (p a).universal
    exact Functor.rightKanExtension_coherentShift
      ((p a).ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      DerivedCategory.Qh (p a).derived (p a).counit
      (Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
        (HomotopyCategory.quasiIso _ (.up ℤ)))
  let hs {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
      (p a).derived.CommShift ℤ := (h a).choose
  exact ⟨{ scalar := fun a ↦ hs a, canonical := fun a ↦ (h a).choose_spec }⟩

end SheafOfModules.RingedCoefficientProjection
