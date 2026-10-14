/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Defs
import Sheaf.AlgebraicGeometry.PicardFpqcLocalEquality

/-! # Fpqc separatedness of the relative Picard sheaf

Source: Stacks Project, Tags 0D28, 0D2B and 023T.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-- The relative Picard sheaf is fpqc-separated when the structure sheaf has universally
trivial direct image.

Proof: represent each of two sections on a common fppf covering by invertible modules.
If the sections agree on an fpqc sieve, their representatives agree as Picard classes
fpqc-locally: the sheafification map is locally injective for fppf, hence also for fpqc.
The ratio-cocycle descent argument then shows that the representatives differ by a
module from the base, so their images in the relative Picard sheaf agree. Finally use
fppf separatedness on the common representative covering. No rational point is needed.
Source: Stacks Project, Tags 0D28, 0D2B and 023T.
(blueprint: lem-pd-picard-fpqc-separated) -/
theorem isSeparated_fpqc_picardFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (pullback.snd f T.hom))) :
    Presieve.IsSeparated (fpqcTopology.over S) (picardFunctor f).obj := by
  let J := fppfTopology.over S
  let K := fpqcTopology.over S
  let φ := toPicardFunctor f
  have hJK : J ≤ K := fun T R hR ↦ fppfTopology_le_fpqcTopology _ hR
  have : Presheaf.IsLocallyInjective K φ :=
    ⟨fun L L' h ↦ hJK _ (Presheaf.equalizerSieve_mem J φ L L' h)⟩
  intro T R hR x t₁ t₂ h₁ h₂
  let A := Presheaf.imageSieve φ t₁ ⊓ Presheaf.imageSieve φ t₂
  have hA : A ∈ J T :=
    J.intersection_covering (Presheaf.imageSieve_mem J φ t₁)
      (Presheaf.imageSieve_mem J φ t₂)
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 (picardFunctor f).property).isSeparated
    A hA).ext
  intro Y g hg
  obtain ⟨L, hL⟩ := hg.1
  obtain ⟨L', hL'⟩ := hg.2
  have hE : Presheaf.equalizerSieve (F := (picardFunctor f).obj)
      (φ.app (op Y) L) (φ.app (op Y) L') ∈ K Y := by
    apply K.superset_covering (fun Z a ha ↦ ?_) (K.pullback_stable g hR)
    change (picardFunctor f).obj.map a.op (φ.app (op Y) L) =
      (picardFunctor f).obj.map a.op (φ.app (op Y) L')
    rw [hL, hL', ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
    exact (h₁ (a ≫ g) ha).trans (h₂ (a ≫ g) ha).symm
  have hE' := Presheaf.equalizerSieve_mem_of_equalizerSieve_app_mem K φ L L' hE
  exact hL.symm.trans ((toPicardFunctor_app_eq_of_fpqc_equalizer f hf L L' hE').trans hL')

end AlgebraicGeometry
