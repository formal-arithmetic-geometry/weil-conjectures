/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedDgRestrictionDescent
public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedDgGoodExtension
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-! The derived adjunction and its normalized counit and transpose.

Source: Stacks sdga, Tags 0FTR and 0FTF
(blueprint: lem-sfb-ringed-dg-derived-adjunction-data).

Proof in words: apply the absolute derived-adjunction theorem to the ordinary
balanced tensor/restriction adjunction.  The comparison on good resolutions
identifies the counit with the action map; the two triangle identities give the
inverse transpose formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v u

open CategoryTheory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The normalized adjunction between already constructed derived functors. -/
structure DerivedAdjunctionData {O : Sheaf J CommRingCat.{u}}
    {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B]
    (ordinary : OrdinaryExtension φ)
    (r : RestrictionDescentData φ)
    (e : GoodExtensionData φ ordinary r) where
  adjunction : e.extension ⊣ r.restriction
  counit (N : Module B) :
    adjunction.counit.app ((Q B).obj N) =
      e.extension.map (r.restrictionIso.hom.app N) ≫
        e.comparison.app ((RingedSiteDg.restriction φ).obj N) ≫
        (Q B).map (ordinary.adjunction.counit.app N)
  inverseTranspose (M : Derived A) (N : Derived B) (f : M ⟶ r.restriction.obj N) :
    (adjunction.homEquiv M N).symm f = e.extension.map f ≫ adjunction.counit.app N

/-- Construct the derived adjunction, cancel the inverse restriction comparison
in its counit formula, and identify the inverse Hom transpose.
Source: Stacks sdga 0FTR; Mathlib Derived/Adjunction.lean
(blueprint: lem-sfb-ringed-dg-derived-adjunction-data). -/
theorem derived_adjunction_data_exists
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B] (ordinary : OrdinaryExtension φ)
    (r : RestrictionDescentData φ) (e : GoodExtensionData φ ordinary r) :
    Nonempty (DerivedAdjunctionData φ ordinary r e) := by
  let := e.derived
  let := e.derivedPostRestriction
  let : r.restriction.IsRightDerivedFunctor r.restrictionIso.inv
      (quasiIsomorphisms B) :=
    Functor.isRightDerivedFunctor_of_inverts (quasiIsomorphisms B)
      r.restriction r.restrictionIso
  let γ : Q B ⋙ (r.restriction ⋙ e.extension) ≅
      (RingedSiteDg.restriction φ ⋙ Q A) ⋙ e.extension :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight r.restrictionIso e.extension
  let : (r.restriction ⋙ e.extension).IsRightDerivedFunctor
      (Functor.whiskerRight r.restrictionIso.inv e.extension ≫
        (Functor.associator _ _ _).hom) (quasiIsomorphisms B) := by
    simpa only [γ, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv] using
      (Functor.isRightDerivedFunctor_of_inverts (quasiIsomorphisms B) _ γ)
  let adj := ordinary.adjunction.derived (quasiIsomorphisms A)
    (quasiIsomorphisms B) e.comparison r.restrictionIso.inv
  refine ⟨{ adjunction := adj, counit := ?_, inverseTranspose := ?_ }⟩
  · intro N
    have h := ordinary.adjunction.derivedε_fac_app (quasiIsomorphisms B)
      e.comparison r.restrictionIso.inv N
    change e.extension.map (r.restrictionIso.inv.app N) ≫
      adj.counit.app ((Q B).obj N) = _ at h
    calc
      adj.counit.app ((Q B).obj N) =
          e.extension.map (r.restrictionIso.hom.app N) ≫
            (e.extension.map (r.restrictionIso.inv.app N) ≫
              adj.counit.app ((Q B).obj N)) := by
        rw [← Category.assoc, ← e.extension.map_comp]
        simp
      _ = _ := by rw [h]
  · intro M N f
    exact adj.homEquiv_counit M N f

end CategoryTheory.RingedSiteDg
