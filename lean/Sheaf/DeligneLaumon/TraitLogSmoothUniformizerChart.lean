/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

import Sheaf.GroupTheory.DivisibleUnitLatticeExtension

/-!
# Uniformizer charts for log smooth schemes over a trait

Source: ILO, Exposé XVI, Definition 3.6.1 and Proposition 3.6.3, printed p.252
(blueprint: lem-per-trait-log-smooth-uniformizer-chart).

The canonical trait log structure is specified by its global uniformizer chart `β`.
Its structural image is `π ^ n`, so the associated log structure is precisely the
subsheaf of functions invertible over the generic point. The conclusion uses the
existing `FSLogChart`: its base neighbourhood is the identity, its base monoid is
identified with `ℕ`, and its base chart is the prescribed `β` under that identification.
The source monoid called `P` in the node is the field `c.Q` in this interface.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Uniformizer charts over the original trait, without a change of the base.
Source: ILO XVI, Definition 3.6.1 and Proposition 3.6.3, printed p.252
(blueprint: lem-per-trait-log-smooth-uniformizer-chart).

The hypotheses `hβ` and `hβπ` specify the canonical log structure by the associated
log structure of the uniformizer chart, rather than by choosing an unrelated log
structure on `Spec R`. The monoids use multiplicative notation: the standard monoid
is `Multiplicative (ULift ℕ)`, and its group completion is canonically `ℤ`.

Proof (the four steps of the DAG):
1. Keep the fixed chart `ℕ → R`, `1 ↦ π`; its group completion is free of rank one.
   Apply `lem-per-log-smooth-differential-generators` at the geometric point. In the
   geometric local ring `A`, the quotient `C = Mᵍᵖ / Aˣ` is torsion-free; the units
   are `n`-divisible for an integer `n ≥ 1` invertible in `A`. The differential basis
   yields a map `L = ℤʳ ⊕ ℤ → C` with finite cokernel killed by `n`.
2. Apply `lem-per-divisible-unit-lattice-extension` to the map `L → Mᵍᵖ` and its
   subgroup of units. It extends through an injection `i : L → G` into a finite free
   abelian group, surjects onto `C`, and has `G / i(L)` killed by `n ^ a`.
3. Set `P` equal to the inverse image of `M` in `G`. The prescribed-lattice version
   `lem-per-kato-lattice-chart-realization` gives an fs chart on an étale neighbourhood,
   compatible with the original base chart, with étale canonical comparison.
   Its group completion is `G`, hence torsion-free; `i` restricts to an injection
   from `ℕ`. The base neighbourhood is the identity, as recorded by `c.W` below.
4. For a torsion class of `G / i(0,ℤ)`, write `n ^ a * g = i(b,z)`. A multiple of
   this lies in `i(0,ℤ)`, so injectivity and torsion-freeness of `ℤʳ` give `b = 0`.
   Thus this torsion is killed by `n ^ a`. Writing `w = i(0,1) ≠ 0` in a finite
   free basis identifies the torsion with `(G ∩ ℚw) / ℤw`, a subgroup of
   `(1 / |wⱼ|)ℤ / ℤ` for a nonzero coordinate `wⱼ`. It is finite cyclic of order
   dividing `n ^ a`. Shrink the neighbourhood so that `n` is invertible, using
   `def-weil-pbc-geometric-stalks`; its torsion order is then invertible as well.
   Finally étale implies smooth by `def-sbc-smooth-morphisms`.
-/
theorem exists_uniformizer_chart
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span ({π} : Set R))
    (hdim : ringKrullDim R = 1)
    (S V : FineSaturatedLogScheme.{u}) (eS : S.scheme ≅ Spec (.of R))
    (β : Multiplicative (ULift.{u} ℕ) →*
      S.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 S.scheme))))
    (hβ : S.logStructure.IsChart (Scheme.Etale.mk (𝟙 S.scheme)) β)
    (hβπ : ∀ n : Multiplicative (ULift.{u} ℕ),
      S.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 S.scheme))) (β n) =
        eS.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv (π ^ n.toAdd.down)))
    (f : EtaleLogHom V S) (hf : f.IsLogSmooth) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V.scheme),
      ∃ c : FSLogChart f,
        (Scheme.SpecToEquivOfField Ω V.scheme v).1 ∈ Set.range c.V.hom ∧
        c.W = Scheme.Etale.mk (𝟙 S.scheme) ∧
        (∃ e : c.P ≃* Multiplicative (ULift.{u} ℕ),
          HEq c.chartY (β.comp e.toMonoidHom)) ∧
        Function.Injective c.g ∧
        IsAddTorsionFree (Additive (Algebra.GrothendieckGroup c.Q)) ∧
        Finite (CommGroup.torsion c.cokernel) ∧
        (∀ x : c.V.left, IsUnit
          (Nat.card (CommGroup.torsion c.cokernel) : c.V.left.presheaf.stalk x)) ∧
        Etale c.comparison ∧ Smooth c.comparison := by
  sorry

end AlgebraicGeometry
