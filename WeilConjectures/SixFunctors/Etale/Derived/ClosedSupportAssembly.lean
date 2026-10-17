/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportTorAmplitude

/-!
# The preservation clauses for closed immersions are theorems

Over a field `k`, the open-complement condition holds for every quasi-compact open immersion
into a scheme of finite type and of dimension at most `d`, with the constant `2d`, for every
finite coefficient ring whose exponent is invertible in `k`
(`AlgebraicGeometry.Etale.openComplementCondition_two_mul_of_finite`, blueprint
`rem-pur-assembly-status`). Consequently the exceptional inverse image along a closed immersion
into such a scheme exists on the ambient derived category and preserves bounded constructibility
and finite Tor amplitude, with explicit bounds, without any hypothesis
(`AlgebraicGeometry.Etale.closedImmersion_exceptional_admissibility`, blueprint
`rem-pur-ambient-only`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-- Blueprint `rem-pur-assembly-status`: Status of the assembly.

The open-complement condition (`def-exc-open-complement-bound`) is a theorem, not an assumption:
for a field `k`, a `k`-scheme `T` of finite type and of dimension at most `d` and a quasi-compact
open immersion `j : V ⟶ T`, every finite ring `Λ` whose exponent is invertible in `k` satisfies
the open-complement condition for `j` with the constant `c = 2d`, which does not depend on `Λ`.

This is `AlgebraicGeometry.Etale.openComplementCondition_two_mul`
(`lem-exc-open-complement-known`), derived from the two clauses of the direct-image finiteness
input (`thm-exc-direct-image-input-holds`): the finite-type constructibility theorem
`thm-dg-finite-type-constructibility` and the cohomological dimension bound
`thm-sc-finite-type-torsion-cd`. The remaining claims of the remark concern the general
admissibility theorems `thm-pur-general-admissibility` and `cor-pur-general-admissibility-datum`,
which are not formalised here; for closed immersions see
`AlgebraicGeometry.Etale.closedImmersion_exceptional_admissibility`. -/
theorem openComplementCondition_two_mul_of_finite {k : Type u} [Field k] {V T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT] (j : V ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] (d : ℕ)
    (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    OpenComplementCondition Λ j (2 * d) :=
  openComplementCondition_two_mul aT j d hT

/-- Blueprint `rem-pur-ambient-only`: The ambient datum of this chapter is a theorem on its
coefficients — the closed-immersion case.

Let `k` be a field, `T` a `k`-scheme of finite type and of dimension at most `d`, `i : Z ⟶ T` a
closed immersion with open complement `j : U ⟶ T`, and `Λ` a finite ring whose exponent is
invertible in `k`. Then, without any further hypothesis:

1. (the ambient datum) `Ri_!` is a left adjoint on the unbounded derived categories, so that the
   exceptional inverse image `Ri^!` exists (`thm-amb-etale-exceptional-adjoint`);
2. (the constructibility clause) `Ri^!` carries `D_c^{[a, b]}(T, Λ)` into
   `D_c^{[a, b + 2d + 1]}(Z, Λ)` (`lem-exc-closed-amplitude`);
3. (the finite-Tor clause) `Ri^!` carries bounded constructible complexes of Tor amplitude in
   `[a, b]` to bounded constructible complexes of Tor amplitude in `[a, b + 2d + 1]`
   (`prop-exc-closed-tor`).

The open-complement condition used by clauses (2) and (3) is supplied by
`AlgebraicGeometry.Etale.openComplementCondition_two_mul` (`lem-exc-open-complement-known`). The
smooth case of the remark (`cor-pur-smooth-admissibility`) and the general separated case
(`thm-pur-general-admissibility`) are not formalised here. -/
theorem closedImmersion_exceptional_admissibility {k : Type u} [Field k] {Z T U : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT] (d : ℕ)
    (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (i : Z ⟶ T) [IsClosedImmersion i]
    [HasCompactification i] (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    (R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint ∧
      (∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) T a b K →
          DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Z a (b + (2 * d : ℕ) + 1)
            ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)) ∧
      ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K →
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z
              ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) ∧
            torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + (2 * d : ℕ) + 1)
              ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have h := openComplementCondition_two_mul (Λ := Λ) aT j d hT
  exact ⟨inferInstance, fun a b K hK ↦ constructibleIn_rightDerivedUpperShriek i j hij h hK,
    fun a b K hK hta ↦ boundedConstructible_torAmplitudeIn_rightDerivedUpperShriek i j hij h hK hta⟩

end Etale

end AlgebraicGeometry
