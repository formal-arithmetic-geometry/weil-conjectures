/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.EventuallyFinite
import Sheaf.AlgebraicGeometry.LocallyFiniteTypeLimitClosedFp

/-!
# Finite schemes as limits of finite finitely presented closed models

Source: Stacks Project, Limits, Tag 09YY, lemma-finite-in-finite-and-finite-presentation
(blueprint: lem-weil-pbc-finite-closed-fp-approximation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite morphism to a quasi-compact quasi-separated scheme is a directed inverse limit
of finite morphisms of finite presentation with closed immersion transition maps.

Source: Stacks Project, Limits, Tag 09YY, lemma-finite-in-finite-and-finite-presentation
(blueprint: lem-weil-pbc-finite-closed-fp-approximation).

Proof plan:
1. By lem-weil-pbc-finite-iff-integral-lft, `p` is integral and locally of finite type.
   It is affine, hence quasi-compact and quasi-separated by
   lem-weil-pbc-affine-morphism-permanence. By lem-weil-pbc-qcqs-morphism-permanence,
   `T` is quasi-compact and quasi-separated. Apply lem-weil-pbc-lft-limit-closed-fp
   (Tag 09ZQ) to obtain finitely presented models with closed transitions and limit `T`.
2. Finitely presented models are locally of finite type. Closed transitions are finite by
   lem-weil-pbc-closed-immersion-integral-separated-uc. Apply lem-weil-pbc-eventually-finite
   (Tag 09ZN), using integrality of `p`, to find an index beyond which all models are finite.
3. Restrict to the nonempty directed tail above that index. Its limit is still `T`:
   extend any cone on the tail to the full system by choosing a common upper bound with
   the tail's initial index. Independence of the choice follows by passing to a further
   common upper bound. The full limit property then gives the tail limit property.
   The stage properties, closed transitions, and compatibility over `S` are inherited. -/
theorem exists_finite_closed_fp_approximation
    {T S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (p : T ⟶ S) [IsFinite p] :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ Scheme.{u}) (q : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (π : (Functor.const Iᵒᵖ).obj T ⟶ D),
      (∀ i : Iᵒᵖ, IsFinite (q.app i) ∧ LocallyOfFinitePresentation (q.app i) ∧
        QuasiCompact (q.app i) ∧ QuasiSeparated (q.app i)) ∧
      (∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsClosedImmersion (D.map f)) ∧
      Nonempty (IsLimit (Cone.mk T π)) ∧
      ∀ i : Iᵒᵖ, π.app i ≫ q.app i = p := by
  classical
  let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated p
  obtain ⟨I, hI, hne, hdir, D, q, π, hfp, hqcqs, hclosed, hcompat, ⟨hlim⟩, _⟩ :=
    exists_locallyFiniteType_limit_closed_finitePresentation p
  let : Preorder I := hI
  let : Nonempty I := hne
  let : IsDirected I (· ≤ ·) := hdir
  let (i : Iᵒᵖ) : CompactSpace (D.obj i) := (hqcqs i).1
  let (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := (hqcqs i).2
  let (i : Iᵒᵖ) : LocallyOfFinitePresentation (q.app i) := (hfp i).1
  let {i j : Iᵒᵖ} (f : i ⟶ j) : IsClosedImmersion (D.map f) := hclosed i j f
  obtain ⟨i₀, hfinite⟩ := eventually_finite S D q (Cone.mk T π) hlim p hcompat
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let t : J ⥤ I := (show Monotone (fun j : J ↦ j.val) from fun _ _ h ↦ h).functor
  let : t.op.Initial := Functor.initial_of_exists_of_isCofiltered t.op
    (fun i ↦ by
      obtain ⟨j, h₀, hi⟩ := exists_ge_ge i₀ i.unop
      exact ⟨Opposite.op ⟨j, h₀⟩, ⟨(homOfLE hi).op⟩⟩)
    (fun {_ _} f g ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  refine ⟨J, inferInstance, inferInstance, inferInstance, t.op ⋙ D,
    Functor.whiskerLeft t.op q, Functor.whiskerLeft t.op π, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hfinite i.unop.val i.unop.property, hfp (t.op.obj i)⟩
  · intro i j f
    exact hclosed _ _ (t.op.map f)
  · exact ⟨(Functor.Initial.isLimitWhiskerEquiv t.op (Cone.mk T π)).symm hlim⟩
  · intro i
    exact hcompat (t.op.obj i)

end AlgebraicGeometry
