/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.FormalFunctionsCompleteBase
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Separation by proper infinitesimal quotient sections

## References

* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over a complete Noetherian base, sections of a coherent module on a proper
scheme are separated by all positive infinitesimal quotient projections
(Stacks, Tag 087U). -/
theorem proper_complete_quotient_sections_jointly_monic
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of A)) [IsProper p]
    (F : CoherentModules Z) {M : ModuleCat.{u} A}
    (a b : M ⟶ (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      ((Scheme.Modules.pushforward p).obj F.obj))
    (hab : ∀ n : ℕ,
      a ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        ((Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (J.comap p) (n + 1) F.obj)) =
      b ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        ((Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (J.comap p) (n + 1) F.obj))) : a = b := by
  let Γ := moduleSpecΓFunctor (R := CommRingCat.of A)
  let C := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom
  let t : Scheme.Modules.pushforward p ⋙ Γ ≅ C := by
    refine NatIso.ofComponents (fun H ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro a
      ext x
      rfl
    · intro H K f
      ext x
      rfl
  obtain ⟨e, he⟩ := globalSections_formalFunctions_complete_base I p F
  subst J
  apply (cancel_mono ((t.app F.obj).hom ≫ e.hom)).1
  apply limit.hom_ext
  intro j
  obtain ⟨n, rfl⟩ := op_surjective j
  simp only [Category.assoc, he n]
  have ht := t.hom.naturality
    (formalModuleQuotientπ
      ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap p) (n + 1) F.obj)
  have hh := congrArg (fun f ↦ f ≫ t.hom.app
    (formalModuleQuotient
      ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap p) (n + 1) F.obj)) (hab n)
  change a ≫ t.hom.app F.obj ≫ C.map _ = b ≫ t.hom.app F.obj ≫ C.map _
  rw [← ht]
  simpa only [Category.assoc, Functor.comp_map, Γ] using hh

end AlgebraicGeometry
