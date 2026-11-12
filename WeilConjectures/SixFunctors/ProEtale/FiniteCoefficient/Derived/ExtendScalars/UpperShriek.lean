/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek

/-!
# Derived scalar extension and `Rf^!`

Let `R → S` be a map of finite commutative rings and write `Ψ = - ⊗ᴸ_R S` for the derived
extension of scalars of pro-étale sheaves. For `f : X ⟶ Y` admitting a compactification, the
comparison `b : Ψ (Rf_! M) ⟶ Rf_! (Ψ M)`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekExtendScalarsMap`) is an isomorphism on
`Dᵇctf(X, R)`. The comparison for the exceptional inverse image,

`c_{R,S}(K) : Ψ (Rf^! K) ⟶ Rf^! (Ψ K)`,

is defined as the transpose, for the exceptional adjunction `Rf_! ⊣ Rf^!` with `S`-coefficients,
of `Ψ(ε_R(K)) ∘ b(Rf^! K)⁻¹` (blueprint `lemma-sp-reduction`, equation (9.16)).

## Main definitions and results

- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekExtendScalarsMap`: the comparison
  `c_{R,S}(K)` (blueprint `lemma-sp-reduction--2`).
- `rightDerivedLowerShriek_map_rightDerivedUpperShriekExtendScalarsMap_comp_counit`: the
  counit equation (9.16), and
  `AlgebraicGeometry.ProEtale.eq_rightDerivedUpperShriekExtendScalarsMap_iff`: it determines
  `c_{R,S}(K)` (blueprint `lemma-sp-reduction--3`).
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedUpperShriekExtendScalarsMap`: `c_{R,S}(K)` is an
  isomorphism on `Dᵇctf(Y, R)` (blueprint `lemma-sp-reduction--2`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [Finite R] [Finite S]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

/-- Blueprint `lemma-sp-reduction--2`: the **comparison for the exceptional inverse image**
`c_{R,S}(K) : Ψ (Rf^! K) ⟶ Rf^! (Ψ K)`, for `Ψ = - ⊗ᴸ_R S`. It is the transpose for the
exceptional adjunction `Rf_! ⊣ Rf^!` with `S`-coefficients of

`Rf_! Ψ (Rf^! K) ≅ Ψ (Rf_! Rf^! K) ⟶ Ψ K`,

the inverse of the comparison `b(Rf^! K)` for `Rf_!`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekExtendScalarsMap`, an isomorphism as
`Rf^! K` is bounded constructible of finite Tor amplitude, `hfK`) followed by `Ψ` of the counit
`ε_R(K)`. The remaining hypotheses are those under which the exceptional adjunction applies. -/
noncomputable def rightDerivedUpperShriekExtendScalarsMap
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (hK : DerivedCategory.TStructure.t.plus K)
    (hfK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X ((R(f)^![R]).obj K))
    (hΨfK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K)))
    (hΨK : DerivedCategory.TStructure.t.plus
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj K)) :
    (L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K) ⟶
      (R(f)^![S]).obj ((L(sheafExtendScalars (algebraMap R S) Y)).obj K) :=
  haveI := isIso_rightDerivedLowerShriekExtendScalarsMap_app R S f hfK
  rightDerivedUpperShriekHomEquiv f hΨfK hΨK
    (inv ((rightDerivedLowerShriekExtendScalarsMap R S f).app ((R(f)^![R]).obj K)) ≫
      (L(sheafExtendScalars (algebraMap R S) Y)).map (rightDerivedUpperShriekCounit f K hK))

variable {R S f}

/-- Blueprint `lemma-sp-reduction--3`: the **counit equation** (9.16),
`ε_S(Ψ K) ∘ Rf_!(c_{R,S}(K)) = Ψ(ε_R(K)) ∘ b(Rf^! K)⁻¹`. -/
theorem rightDerivedLowerShriek_map_rightDerivedUpperShriekExtendScalarsMap_comp_counit
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (hK : DerivedCategory.TStructure.t.plus K)
    (hfK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X ((R(f)^![R]).obj K))
    (hΨfK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K)))
    (hΨK : DerivedCategory.TStructure.t.plus
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj K)) :
    haveI := isIso_rightDerivedLowerShriekExtendScalarsMap_app R S f hfK
    (R(f)_![ModuleCat.{u + 1} S]).map
        (rightDerivedUpperShriekExtendScalarsMap R S f K hK hfK hΨfK hΨK) ≫
      rightDerivedUpperShriekCounit f _ hΨK =
    inv ((rightDerivedLowerShriekExtendScalarsMap R S f).app ((R(f)^![R]).obj K)) ≫
      (L(sheafExtendScalars (algebraMap R S) Y)).map (rightDerivedUpperShriekCounit f K hK) :=
  (rightDerivedUpperShriekHomEquiv f hΨfK hΨK).symm_apply_apply _

/-- Blueprint `lemma-sp-reduction--3`: the counit equation (9.16) **determines** the comparison
`c_{R,S}(K)`: a morphism `c : Ψ (Rf^! K) ⟶ Rf^! (Ψ K)` is `c_{R,S}(K)` if and only if
`ε_S(Ψ K) ∘ Rf_!(c) = Ψ(ε_R(K)) ∘ b(Rf^! K)⁻¹`. -/
theorem eq_rightDerivedUpperShriekExtendScalarsMap_iff
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (hK : DerivedCategory.TStructure.t.plus K)
    (hfK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X ((R(f)^![R]).obj K))
    (hΨfK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K)))
    (hΨK : DerivedCategory.TStructure.t.plus
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj K))
    (c : (L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K) ⟶
      (R(f)^![S]).obj ((L(sheafExtendScalars (algebraMap R S) Y)).obj K)) :
    haveI := isIso_rightDerivedLowerShriekExtendScalarsMap_app R S f hfK
    c = rightDerivedUpperShriekExtendScalarsMap R S f K hK hfK hΨfK hΨK ↔
      (R(f)_![ModuleCat.{u + 1} S]).map c ≫ rightDerivedUpperShriekCounit f _ hΨK =
        inv ((rightDerivedLowerShriekExtendScalarsMap R S f).app ((R(f)^![R]).obj K)) ≫
          (L(sheafExtendScalars (algebraMap R S) Y)).map
            (rightDerivedUpperShriekCounit f K hK) := by
  rw [← rightDerivedLowerShriek_map_rightDerivedUpperShriekExtendScalarsMap_comp_counit K hK hfK
    hΨfK hΨK]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact (rightDerivedUpperShriekHomEquiv f hΨfK hΨK).symm.injective h

/-- Blueprint `lemma-sp-reduction--2`: for `K ∈ Dᵇctf(Y, R)`, `f` separated of finite type
between schemes of finite type over a field `k` in which the exponents of `R` and `S` are
invertible, the comparison `c_{R,S}(K) : Ψ (Rf^! K) ⟶ Rf^! (Ψ K)` is an **isomorphism**.

TODO: the blueprint proof restricts to smooth charts `f|_U = p_d ∘ e`, where the counit is built
from the trace of the projective line, which commutes with extension of scalars. -/
theorem isIso_rightDerivedUpperShriekExtendScalarsMap {k : Type u} [Field k]
    [HasInvertibleExponent R (Spec (.of k))] [HasInvertibleExponent S (Spec (.of k))]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (hK₀ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) Y K)
    (hK : DerivedCategory.TStructure.t.plus K)
    (hfK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X ((R(f)^![R]).obj K))
    (hΨfK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K)))
    (hΨK : DerivedCategory.TStructure.t.plus
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj K)) :
    IsIso (rightDerivedUpperShriekExtendScalarsMap R S f K hK hfK hΨfK hΨK) := by
  sorry

end AlgebraicGeometry.ProEtale
