/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# The small étale site is not essentially small

Mathlib knows that the small *affine* étale site `AlgebraicGeometry.Scheme.AffineEtale` is
essentially small (`Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`), and constructs
sheafification on the small étale site from that, through the dense subsite
`AlgebraicGeometry.Scheme.AffineEtale.Spec`. This file records why the detour through the
affine slice is *necessary*: the small étale site itself is not essentially small.

The obstruction is the disjoint union. For any `I : Type u`, the fold map
`∐_{i : I} X ⟶ X` is étale — it restricts to the identity on each summand and `@Etale` is
Zariski-local at the source — so `AlgebraicGeometry.Scheme.Etale.sigmaCopies` produces an
object of `X.Etale` for every `I`. When `X` has exactly one point (e.g. `X = Spec K` for a
field `K`) the underlying set of `∐_{i : I} X` is in bijection with `I`, so these objects
are pairwise non-isomorphic for pairwise non-equinumerous `I`, and the skeleton of
`X.Etale` contains a copy of `Cardinal.{u}`, which is not `Small.{u}`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.sigmaCopies`: `I` disjoint copies of `X`, as an étale
  `X`-scheme.
- `AlgebraicGeometry.Scheme.not_essentiallySmall_etale`: the small étale site of a
  one-point scheme is not essentially small.
- `AlgebraicGeometry.Scheme.not_essentiallySmall_etale_spec`: in particular the small
  étale site of the spectrum of a field is not essentially small.
-/

@[expose] public section

universe u

open CategoryTheory Limits Cardinal MorphismProperty

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- `I` disjoint copies of `X`, as an étale `X`-scheme: the structure morphism is the fold
map `∐_{i : I} X ⟶ X`, which is étale because it restricts to the identity on each summand
and `@Etale` is Zariski-local at the source. -/
def Etale.sigmaCopies (I : Type u) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (Sigma.desc fun _ : I ↦ 𝟙 X)
    (IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance)

/-- If `X` has exactly one point, the underlying set of `Etale.sigmaCopies X I` is in
bijection with `I`. -/
lemma Etale.mk_sigmaCopies [Subsingleton X] [Nonempty X] (I : Type u) :
    #((Etale.sigmaCopies X I).left : Type u) = #I := by
  change #((∐ fun _ : I ↦ X : Scheme.{u}) : Type u) = #I
  rw [← Cardinal.mk_congr (AlgebraicGeometry.sigmaMk (fun _ : I ↦ X)).toEquiv, Cardinal.mk_sigma]
  simp [Cardinal.mk_eq_one]

/-- The small étale site of a one-point scheme is **not** essentially small: the disjoint
unions `Etale.sigmaCopies X I` give a copy of `Cardinal.{u}` inside its skeleton.

This is why sheafification on the small étale site is obtained in mathlib from the
essentially small *affine* étale site through a dense subsite, rather than from essential
smallness of the small étale site itself. -/
theorem not_essentiallySmall_etale [Subsingleton X] [Nonempty X] :
    ¬ EssentiallySmall.{u} X.Etale := by
  intro h
  have hsmall : Small.{u} (Skeleton X.Etale) := ((essentiallySmall_iff _).1 h).1
  have hinj : Function.Injective
      (fun c : Cardinal.{u} ↦ toSkeleton (Etale.sigmaCopies X c.out)) := by
    intro c₁ c₂ hc
    obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 hc
    have he : #((Etale.sigmaCopies X c₁.out).left : Type u) =
        #((Etale.sigmaCopies X c₂.out).left : Type u) :=
      Cardinal.mk_congr (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
        ((MorphismProperty.Over.forget (@Etale) ⊤ X ⋙
          CategoryTheory.Over.forget X).mapIso e))).toEquiv
    rwa [Etale.mk_sigmaCopies, Etale.mk_sigmaCopies, Cardinal.mk_out, Cardinal.mk_out] at he
  exact not_small_cardinal.{u, u} (small_of_injective hinj)

/-- The small étale site of the spectrum of a field is not essentially small. -/
theorem not_essentiallySmall_etale_spec (K : Type u) [Field K] :
    ¬ EssentiallySmall.{u} (Spec (.of K)).Etale :=
  not_essentiallySmall_etale _

end AlgebraicGeometry.Scheme
