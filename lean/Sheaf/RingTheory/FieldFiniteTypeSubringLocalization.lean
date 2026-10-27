module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Field.IsField

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Jacobson.Ring
import WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty

/-! # A field of finite type over a subring

Source: Stacks Project, Algebra, Tag 00FY (lemma-field-finite-type-over-domain)
(blueprint: lem-sfb-field-finite-type-over-subring-localization).
-/

@[expose] public section

universe u

namespace Subring

/-- A field of finite type over a subring is finite over a principal localization of that
subring which is a field. The localization map is the canonical extension of the inclusion,
so it sends `r / s ^ n` to `r * s⁻¹ ^ n` in the ambient field.

Source: Stacks Project, Algebra, Tag 00FY (lemma-field-finite-type-over-domain)
(blueprint: lem-sfb-field-finite-type-over-subring-localization).

Proof:
1. The subring is a domain, with generic point the zero ideal. The inclusion induces
   `Spec K → Spec R`, whose image is the singleton consisting of the zero ideal.
   By lem-weil-pbc-lft-pointwise-criterion this map is locally of finite type; its
   one-point source makes it quasi-compact (def-weil-finite-type-morphism).
   Apply lem-sbc-generic-closed-subset-fibre-nonempty to the whole closed source
   and the zero ideal to obtain an open neighbourhood contained in that singleton.
2. By lem-weil-pbc-spec-localization-away-basic-open choose a nonzero `s` with
   `D(s)` contained in this neighbourhood, hence equal to that singleton. Set
   `A = R[1/s]` (def-weil-ring-localization-away). Its canonical map into `K`
   sends fractions to the indicated quotients and is injective: a zero quotient
   has zero numerator. Thus `A` is a nonzero domain, and the same basic-open
   lemma identifies its prime spectrum with `D(s)`, a singleton.
3. If a nonzero element of `A` were not a unit, its proper principal ideal would
   lie in a maximal ideal by lem-weil-pbc-proper-ideal-contained-in-maximal.
   Every maximal ideal is prime: write `1 = u + vb` when `b` is outside it and
   multiply by `c` to prove primality. The unique prime is zero, contradicting
   membership of the chosen nonzero element. Therefore `A` is a field
   (def-weil-field).
4. Finite algebra generators of `K` over `R` also generate it over `A`, since
   `R` embeds in `A`. Apply lem-weil-pbc-zariski-lemma to these two fields to
   conclude that `K` is finite-dimensional over `A` via the canonical map. -/
theorem exists_isField_away_finite_of_finiteType
    {K : Type u} [Field K] (R : Subring K) (hfinite : R.subtype.FiniteType) :
    ∃ (s : R) (hs : s ≠ 0), IsField (Localization.Away s) ∧
      Function.Injective (IsLocalization.Away.lift (S := Localization.Away s) s
        (g := R.subtype) (isUnit_iff_ne_zero.mpr (Subtype.coe_injective.ne hs))) ∧
      RingHom.Finite (IsLocalization.Away.lift (S := Localization.Away s) s
        (g := R.subtype) (isUnit_iff_ne_zero.mpr (Subtype.coe_injective.ne hs))) := by
  sorry

end Subring
