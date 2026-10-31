/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # The obstruction to strict fractions on cochain complexes

Quasi-isomorphisms have a calculus of fractions after passage to the homotopy
category. Strict cancellation on complexes would force every complex to be acyclic.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Strict right fraction cancellation for quasi-isomorphisms forces acyclicity.
Source: the mapping-cone construction in Stacks, Derived Categories, Tag 014D,
and the cancellation axiom for a right calculus of fractions, Tag 04VC.
(blueprint: lem-sf-cochain-quasiiso-fraction-obstruction)

Proof: the inclusion of K into the cone of its identity is degreewise split monic.
The cone is acyclic, so its zero endomorphism is a quasi-isomorphism and equalizes
the inclusion and zero. Right fraction cancellation would supply a
quasi-isomorphism t into K killed by the inclusion. Monicity forces t = 0.
The homology maps of t are therefore both zero and isomorphisms, so the homology
objects of K vanish. This argument applies equally to bounded and unbounded K;
it asserts no contradiction when K is acyclic or the category is zero. -/
theorem acyclic_of_quasiIso_hasRightCalculusOfFractions
    {C : Type u} [Category.{v} C] [Abelian C]
    (hW : (HomologicalComplex.quasiIso C (.up ℤ)).HasRightCalculusOfFractions)
    (K : CochainComplex C ℤ) : K.Acyclic := by
  let i := mappingCone.inr (𝟙 K)
  have hi : Mono i := HomologicalComplex.mono_of_mono_f i
    (fun n ↦ mono_of_mono_fac (mappingCone.inr_f_snd_v (𝟙 K) n))
  have hcone : (mappingCone (𝟙 K)).Acyclic :=
    (mappingCone.quasiIso_iff_acyclic (𝟙 K)).1 inferInstance
  have hs : (HomologicalComplex.quasiIso C (.up ℤ))
      (0 : mappingCone (𝟙 K) ⟶ mappingCone (𝟙 K)) := by
    exact ⟨fun n ↦ (quasiIsoAt_iff_exactAt _ n (hcone n)).2 (hcone n)⟩
  obtain ⟨Z, t, ht, heq⟩ := hW.ext i 0 0 hs (by simp)
  have ht0 : t = 0 := (cancel_mono i).1 (by simpa using heq)
  have : QuasiIso (0 : Z ⟶ K) := by simpa [ht0] using ht
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz : IsIso (0 : Z.homology n ⟶ K.homology n) := by
    simpa using (inferInstance : IsIso (HomologicalComplex.homologyMap (0 : Z ⟶ K) n))
  exact ((isIsoZero_iff_source_target_isZero _ _).1 hz).2

end CochainComplex
