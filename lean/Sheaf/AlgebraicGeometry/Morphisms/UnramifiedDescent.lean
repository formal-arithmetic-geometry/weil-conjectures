/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc descent of unramified morphisms

Source: Stacks Project, Descent, Lemma 02VM, first assertion
(blueprint: lem-galois-fpqc-descend-unramified).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-galois-fpqc-descend-unramified) Stacks Project, Descent, Lemma 02VM,
first assertion. An unramified morphism descends along an fpqc covering of its target.
Generate the covering sieve and apply the source library's covering-family descent theorem
separately to local finite type and formal unramifiedness. Mathlib supplies their Zariski
locality, base-change stability, and descent along surjective flat quasi-compact morphisms.
The open diagonal of each base change implies formal unramifiedness. After descent,
local finite type and formal unramifiedness give an open diagonal, using the equivalence
of More on Morphisms 02HE and Morphisms 02GE. -/
theorem locallyOfFiniteType_and_openDiagonal_of_fpqcCover
    {S X : Scheme.{u}} {I : Type v} {S' : I → Scheme.{u}}
    (f : X ⟶ S) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, LocallyOfFiniteType (pullback.snd f (g i)) ∧
      IsOpenImmersion (pullback.diagonal (pullback.snd f (g i)))) :
    LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f) := by
  have hcover : Sieve.ofArrows S' g ∈ Scheme.fpqcTopology S :=
    Precoverage.generate_mem_toGrothendieck hg
  have hlft : LocallyOfFiniteType f :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @LocallyOfFiniteType)
      hcover f (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
      (fun i ↦ IsPullback.of_hasPullback f (g i)) (fun i ↦ (h i).1)
  have hunramified : FormallyUnramified f :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @FormallyUnramified)
      hcover f (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
      (fun i ↦ IsPullback.of_hasPullback f (g i)) (fun i ↦ by
        have := (h i).2
        infer_instance)
  exact ⟨hlft, inferInstance⟩

end AlgebraicGeometry
