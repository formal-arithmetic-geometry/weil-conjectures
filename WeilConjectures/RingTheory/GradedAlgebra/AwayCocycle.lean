/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Coherence of the standard chart rings of `Proj`

For homogeneous `f` and `g`, the ring `Away 𝒜 (f * g)` is the common restriction of the chart
rings `Away 𝒜 f` and `Away 𝒜 g` to `D₊(f) ∩ D₊(g) = D₊(fg)`, via the restriction maps
`HomogeneousLocalization.awayMap` (for positive degrees these are localizations, see
`HomogeneousLocalization.Away.isLocalization_mul`).

## Main definitions

- `HomogeneousLocalization.Away.congr` — the canonical isomorphism `Away 𝒜 x ≃+* Away 𝒜 y`
  for `x = y`.
- `HomogeneousLocalization.Away.overlapEquiv` — the identification
  `Away 𝒜 (f * g) ≃+* Away 𝒜 (g * f)` of the overlap ring computed from either chart.

## Main results

- `HomogeneousLocalization.awayMap_awayMap` — restriction maps compose.
- `HomogeneousLocalization.Away.overlapEquiv_self`, `Away.overlapEquiv_symm`,
  `Away.overlapEquiv_cocycle` — identity, symmetry and cocycle condition
  (blueprint: `lemma-nagata-proj-chart-ring-cocycle`).

The general facts about `Away.congr` and `awayMap_awayMap` belong in
`WeilConjectures/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean`.
-/

@[expose] public section

namespace HomogeneousLocalization

section ChartCocycle

variable {ι σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- The canonical isomorphism `Away 𝒜 x ≃+* Away 𝒜 y` for `x = y`. -/
def Away.congr {x y : A} (h : x = y) : Away 𝒜 x ≃+* Away 𝒜 y := by
  subst h
  exact RingEquiv.refl _

@[simp]
lemma Away.congr_rfl {x : A} : Away.congr 𝒜 (rfl : x = x) = RingEquiv.refl _ :=
  rfl

@[simp]
lemma Away.congr_symm {x y : A} (h : x = y) :
    (Away.congr 𝒜 h).symm = Away.congr 𝒜 h.symm := by
  subst h
  rfl

@[simp]
lemma Away.congr_trans {x y z : A} (h : x = y) (h' : y = z) :
    (Away.congr 𝒜 h).trans (Away.congr 𝒜 h') = Away.congr 𝒜 (h.trans h') := by
  subst h h'
  rfl

lemma Away.congr_mk {d : ι} {x y : A} (h : x = y) (hx : x ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    Away.congr 𝒜 h (Away.mk 𝒜 hx n a ha) = Away.mk 𝒜 (h ▸ hx) n a ha := by
  subst h
  rfl

/-- `Away.congr` is compatible with the restriction maps `awayMap`. -/
lemma Away.congr_awayMap {e : ι} {f g x y : A} (hg : g ∈ 𝒜 e) (hx : x = f * g) (h : x = y)
    (a : Away 𝒜 f) :
    Away.congr 𝒜 h (awayMap 𝒜 hg hx a) = awayMap 𝒜 hg (h.symm.trans hx) a := by
  subst h
  rfl

/-- `Away.congr` is compatible with the restriction maps `awayMap` out of the overlap ring. -/
lemma Away.awayMap_congr {e : ι} {g x y z : A} (hg : g ∈ 𝒜 e) (h : x = y) (hz : z = y * g)
    (a : Away 𝒜 x) :
    awayMap 𝒜 hg hz (Away.congr 𝒜 h a) = awayMap 𝒜 hg (hz.trans (h ▸ rfl)) a := by
  subst h
  rfl

/-- **Restriction maps between chart rings compose**: restricting a section of the chart
`D₊(f)` first to `D₊(fg)` and then to `D₊(fgh)` is the same as restricting it directly to
`D₊(f(gh))`. Both sides are the same map into the localization at `fgh`. -/
lemma awayMap_awayMap {d e e' : ι} {f g h x y : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hh : h ∈ 𝒜 e') (hx : x = f * g) (hy : y = x * h) (a : Away 𝒜 f) :
    awayMap 𝒜 hh hy (awayMap 𝒜 hg hx a) =
      awayMap 𝒜 (SetLike.mul_mem_graded hg hh) (by rw [hy, hx, mul_assoc]) a := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf a
  simp only [awayMap_mk]
  apply val_injective
  simp only [Away.val_mk]
  congr 1
  rw [mul_pow, mul_assoc]

/-- The canonical identification of the overlap rings of the charts `D₊(f)` and `D₊(g)`
computed from either side: `Away 𝒜 (f * g) ≃+* Away 𝒜 (g * f)`.
(blueprint: `lemma-nagata-proj-chart-ring-cocycle`) -/
def Away.overlapEquiv (f g : A) : Away 𝒜 (f * g) ≃+* Away 𝒜 (g * f) :=
  Away.congr 𝒜 (mul_comm f g)

/-- The overlap equivalence identifies the two restrictions of the chart ring at `f`.
(blueprint: `lemma-nagata-proj-chart-ring-cocycle`) -/
lemma Away.overlapEquiv_awayMap_left {e : ι} {f g : A} (hg : g ∈ 𝒜 e) (a : Away 𝒜 f) :
    Away.overlapEquiv 𝒜 f g (awayMap 𝒜 hg rfl a) = awayMap 𝒜 hg (mul_comm g f) a :=
  Away.congr_awayMap 𝒜 hg rfl _ a

/-- The overlap equivalence identifies the two restrictions of the chart ring at `g`.
(blueprint: `lemma-nagata-proj-chart-ring-cocycle`) -/
lemma Away.overlapEquiv_awayMap_right {d : ι} {f g : A} (hf : f ∈ 𝒜 d) (a : Away 𝒜 g) :
    Away.overlapEquiv 𝒜 f g (awayMap 𝒜 hf (mul_comm f g) a) = awayMap 𝒜 hf rfl a :=
  Away.congr_awayMap 𝒜 hf _ _ a

/-- The overlap equivalence of a chart with itself is the identity.
(blueprint: `lemma-nagata-proj-chart-ring-cocycle`) -/
@[simp]
lemma Away.overlapEquiv_self (f : A) : Away.overlapEquiv 𝒜 f f = RingEquiv.refl _ :=
  Away.congr_rfl 𝒜

/-- The overlap equivalences are inverse under exchanging `f` and `g`.
(blueprint: `lemma-nagata-proj-chart-ring-cocycle`) -/
@[simp]
lemma Away.overlapEquiv_symm (f g : A) :
    (Away.overlapEquiv 𝒜 f g).symm = Away.overlapEquiv 𝒜 g f :=
  Away.congr_symm 𝒜 _

/-- Restricting along the overlap equivalence does not change the restriction map into a
further overlap ring. -/
lemma Away.awayMap_overlapEquiv {e : ι} {f g h z : A} (hh : h ∈ 𝒜 e) (hz : z = f * g * h)
    (hz' : z = g * f * h) (a : Away 𝒜 (f * g)) :
    awayMap 𝒜 hh hz' (Away.overlapEquiv 𝒜 f g a) = awayMap 𝒜 hh hz a :=
  Away.awayMap_congr 𝒜 hh (mul_comm f g) hz' a

/-- **Cocycle condition for the chart rings of `Proj`**: on the triple overlap
`D₊(fgh)`, i.e. after composing with the restriction maps into `Away 𝒜 z` for `z = fgh`,
each of the overlap equivalences `φ_{fg}`, `φ_{gh}`, `φ_{fh}` becomes the identity. Hence
`φ_{gh} ∘ φ_{fg} = φ_{fh}` on the triple overlap.
(blueprint: `lemma-nagata-proj-chart-ring-cocycle`) -/
theorem Away.overlapEquiv_cocycle {d e e' : ι} {f g h z : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hh : h ∈ 𝒜 e') (hz : z = f * g * h) :
    (awayMap 𝒜 hh (hz.trans (by ring) : z = g * f * h)).comp
        (Away.overlapEquiv 𝒜 f g).toRingHom = awayMap 𝒜 hh hz ∧
      (awayMap 𝒜 hf (hz.trans (by ring) : z = h * g * f)).comp
        (Away.overlapEquiv 𝒜 g h).toRingHom =
          awayMap 𝒜 hf (hz.trans (by ring) : z = g * h * f) ∧
      (awayMap 𝒜 hg (hz.trans (by ring) : z = h * f * g)).comp
        (Away.overlapEquiv 𝒜 f h).toRingHom =
          awayMap 𝒜 hg (hz.trans (by ring) : z = f * h * g) := by
  refine ⟨RingHom.ext fun a ↦ ?_, RingHom.ext fun a ↦ ?_, RingHom.ext fun a ↦ ?_⟩ <;>
  exact Away.awayMap_overlapEquiv 𝒜 _ (hz.trans (by ring)) (hz.trans (by ring)) a

end ChartCocycle

end HomogeneousLocalization
