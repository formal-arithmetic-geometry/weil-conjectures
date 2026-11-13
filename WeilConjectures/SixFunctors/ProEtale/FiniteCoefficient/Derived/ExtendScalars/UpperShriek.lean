/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness

/-!
# Derived scalar extension and `Rf^!`

Let `R → S` be a map of finite commutative rings and write `Ψ = - ⊗ᴸ_R S` for the derived
extension of scalars of pro-étale sheaves. For `f : X ⟶ Y` admitting a compactification, the
comparison `b : Ψ (Rf_! M) ⟶ Rf_! (Ψ M)`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekExtendScalarsMap`) is an isomorphism on
`Dᵇctf(X, R)`. The comparison for the exceptional inverse image,

`c_{R,S}(K) : Ψ (Rf^! K) ⟶ Rf^! (Ψ K)`,

is defined as the transpose, for the exceptional adjunction `Rf_! ⊣ Rf^!` with `S`-coefficients,
of `Ψ(ε_R(K)) ∘ b(Rf^! K)⁻¹`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekExtendScalarsMap`: the comparison
  `c_{R,S}(K)`.
- `rightDerivedLowerShriek_map_rightDerivedUpperShriekExtendScalarsMap_comp_counit`: the
  counit equation characterising `c_{R,S}(K)`, and
  `AlgebraicGeometry.ProEtale.eq_rightDerivedUpperShriekExtendScalarsMap_iff`: it determines
  `c_{R,S}(K)`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedUpperShriekExtendScalarsMap`: `c_{R,S}(K)` is an
  isomorphism on `Dᵇctf(Y, R)`.

## Implementation details

The isomorphism property of `c_{R,S}(K)` is still open. Restricted back to `R`, `c_{R,S}(K)` should
be the tensor map `Rf^! K ⊗ᴸ S_X ⟶ Rf^!(K ⊗ᴸ S_Y)` for the constant sheaf `S_Y`, whose étale
counterpart is an isomorphism by the exceptional Künneth formula
(`AlgebraicGeometry.Etale.isExceptionalKunneth`). This needs the commutation of restriction of
scalars with the pro-étale `Rf^!`, the identification of `b` restricted to `R` with the projection
map, and the comparison of both with their étale counterparts.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [Finite R] [Finite S]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

/-- The **comparison for the exceptional inverse image**
`c_{R,S}(K) : Ψ (Rf^! K) ⟶ Rf^! (Ψ K)`, for `Ψ = - ⊗ᴸ_R S`: the transpose for the exceptional
adjunction `Rf_! ⊣ Rf^!` with `S`-coefficients of

`Rf_! Ψ (Rf^! K) ≅ Ψ (Rf_! Rf^! K) ⟶ Ψ K`,

the inverse of the comparison `b(Rf^! K)` for `Rf_!`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekExtendScalarsMap`, invertible since `Rf^! K`
is in `Dᵇctf(X, R)`) followed by `Ψ` of the counit `ε_R(K)`. -/
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

/-- The **counit equation** characterising `c_{R,S}(K)`:
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

/-- The counit equation **determines** the comparison `c_{R,S}(K)`: a morphism
`c : Ψ (Rf^! K) ⟶ Rf^! (Ψ K)` is `c_{R,S}(K)` if and only if
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

section Constructible

variable {k : Type u} [Field k] [HasInvertibleExponent R (Spec (.of k))]
  (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [LocallyOfFiniteType f]
  [QuasiCompact f] {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R))}
  (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) Y K)

include aY hK

omit [CompactSpace Y] [LocallyOfFiniteType f] in
/-- For `K ∈ Dᵇctf(Y, R)`, the exceptional inverse image `Rf^! K` is in `Dᵇctf(X, R)`. -/
lemma constructibleFiniteTor_rightDerivedUpperShriek_obj_of_field :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X ((R(f)^![R]).obj K) :=
  haveI : HasInvertibleExponent R Y := .of_hom aY
  constructibleFiniteTor_rightDerivedUpperShriek R aY f hK

omit [CompactSpace Y] in
/-- For `K ∈ Dᵇctf(Y, R)`, the scalar extension `Ψ (Rf^! K)` is in `Dᵇctf(X, S)`. -/
lemma constructibleFiniteTor_leftDerivedSheafExtendScalars_rightDerivedUpperShriek_obj :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K)) :=
  haveI : HasInvertibleExponent R X := .of_hom (f ≫ aY)
  constructibleFiniteTor_leftDerivedSheafExtendScalars (f ≫ aY)
    (constructibleFiniteTor_rightDerivedUpperShriek_obj_of_field aY hK)

omit [CompactSpace Y] in
/-- For `K ∈ Dᵇctf(Y, R)`, the scalar extension `Ψ K` is in `Dᵇctf(Y, S)`. -/
lemma constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) Y
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj K) :=
  haveI : HasInvertibleExponent R Y := .of_hom aY
  constructibleFiniteTor_leftDerivedSheafExtendScalars aY hK

/-- For `K ∈ Dᵇctf(Y, R)`, `f` separated of finite type between schemes of finite type over a
field `k` in which the exponents of `R` and `S` are invertible, the comparison
`c_{R,S}(K) : Ψ (Rf^! K) ⟶ Rf^! (Ψ K)` is an **isomorphism**. -/
theorem isIso_rightDerivedUpperShriekExtendScalarsMap
    [HasInvertibleExponent S (Spec (.of k))] [IsSeparated aY] [IsSeparated f] :
    IsIso (rightDerivedUpperShriekExtendScalarsMap R S f K hK.plus
      (constructibleFiniteTor_rightDerivedUpperShriek_obj_of_field aY hK)
      (constructibleFiniteTor_leftDerivedSheafExtendScalars_rightDerivedUpperShriek_obj aY
        hK).plusEtaleOrigin
      (constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field (S := S) aY hK).plus) := by
  sorry

end Constructible

end AlgebraicGeometry.ProEtale
