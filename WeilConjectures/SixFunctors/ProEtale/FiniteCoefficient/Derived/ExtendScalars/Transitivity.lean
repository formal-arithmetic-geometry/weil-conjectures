/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriekTransitivity
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.UpperShriek

/-!
# Transitivity of the scalar extension comparisons for `Rf_!` and `Rf^!`

Let `R → S → T` be maps of finite commutative rings and write `Ψ_{R,S} = - ⊗ᴸ_R S` for the
derived extension of scalars of pro-étale sheaves. The comparison
`τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`
(`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompMap`) is induced, through the
universal property of the left derived functor `Ψ_{R,T}`, by the isomorphism
`T ⊗_S (S ⊗_R -) ≅ T ⊗_R -` of the underived extensions of scalars
(`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompIso`).

The comparisons `b` for `Rf_!` and `c` for `Rf^!` of blueprint `lemma-sp-reduction` are
transitive along `τ`:

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekExtendScalarsMap_trans`: the comparison `b`
  for `R → T` is the composite of those for `R → S` and `S → T` (`lemma-sp-reduction--4`);
- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekExtendScalarsMap_trans`: the same for the
  comparison `c` (`lemma-sp-reduction--5`), deduced from the transitivity of `b` and the counit
  equation (9.16) characterising `c`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S T : Type (u + 1)} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Finite R] [Finite S] [Finite T] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [CompactSpace Y]

/-- Blueprint `lemma-sp-reduction--5`: **transitivity of the comparison for `Rf^!`**. For
`R → S → T` and `K` such that the comparisons `c_{R,S}(K)`, `c_{R,T}(K)` and `c_{S,T}(Ψ_{R,S} K)`
are defined, the comparison `c_{R,T}(K)` is the composite of `c_{R,S}` and `c_{S,T}`, along
`τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`:

`c_{R,T}(K) ∘ τ(Rf^! K) = Rf^!(τ(K)) ∘ c_{S,T}(Ψ_{R,S} K) ∘ Ψ_{S,T}(c_{R,S}(K))`.

The two sides are transposes for the exceptional adjunction, and their transposes agree by the
counit equations (9.16) (`lemma-sp-reduction--3`) and the transitivity of the comparison for
`Rf_!` (`lemma-sp-reduction--4`). -/
theorem rightDerivedUpperShriekExtendScalarsMap_trans
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (hK : DerivedCategory.TStructure.t.plus K)
    (hfK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X ((R(f)^![R]).obj K))
    (hΨfK₁ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K)))
    (hΨK₁ : DerivedCategory.TStructure.t.plus
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj K))
    (hΨfK₂ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} T) X
      ((L(sheafExtendScalars (algebraMap R T) X)).obj ((R(f)^![R]).obj K)))
    (hΨK₂ : DerivedCategory.TStructure.t.plus
      ((L(sheafExtendScalars (algebraMap R T) Y)).obj K))
    (hfK₃ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X
      ((R(f)^![S]).obj ((L(sheafExtendScalars (algebraMap R S) Y)).obj K)))
    (hΨfK₃ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} T) X
      ((L(sheafExtendScalars (algebraMap S T) X)).obj
        ((R(f)^![S]).obj ((L(sheafExtendScalars (algebraMap R S) Y)).obj K))))
    (hΨK₃ : DerivedCategory.TStructure.t.plus
      ((L(sheafExtendScalars (algebraMap S T) Y)).obj
        ((L(sheafExtendScalars (algebraMap R S) Y)).obj K)))
    (hΨfK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K)))
    (hΨΨfK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} T) X
      ((L(sheafExtendScalars (algebraMap S T) X)).obj
        ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K)))) :
    (leftDerivedSheafExtendScalarsCompMap R S T X).app ((R(f)^![R]).obj K) ≫
        rightDerivedUpperShriekExtendScalarsMap R T f K hK hfK hΨfK₂ hΨK₂ =
      (L(sheafExtendScalars (algebraMap S T) X)).map
          (rightDerivedUpperShriekExtendScalarsMap R S f K hK hfK hΨfK₁ hΨK₁) ≫
        rightDerivedUpperShriekExtendScalarsMap S T f _ hΨK₁ hfK₃ hΨfK₃ hΨK₃ ≫
        (R(f)^![T]).map ((leftDerivedSheafExtendScalarsCompMap R S T Y).app K) := by
  have := isIso_rightDerivedLowerShriekExtendScalarsMap_app R S f hfK
  have := isIso_rightDerivedLowerShriekExtendScalarsMap_app R T f hfK
  have := isIso_rightDerivedLowerShriekExtendScalarsMap_app S T f hfK₃
  have := isIso_rightDerivedLowerShriekExtendScalarsMap_app S T f hΨfK
  apply (rightDerivedUpperShriekHomEquiv f hΨΨfK hΨK₂).symm.injective
  simp only [rightDerivedUpperShriekHomEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [rightDerivedLowerShriek_map_rightDerivedUpperShriekExtendScalarsMap_comp_counit,
    rightDerivedUpperShriekCounit_naturality f hΨK₃ hΨK₂,
    reassoc_of% rightDerivedLowerShriek_map_rightDerivedUpperShriekExtendScalarsMap_comp_counit]
  -- move `b_{S,T}⁻¹` across `Rf_!(Ψ_{S,T} c_{R,S})`
  have hb := (rightDerivedLowerShriekExtendScalarsMap S T f).naturality
    (rightDerivedUpperShriekExtendScalarsMap R S f K hK hfK hΨfK₁ hΨK₁)
  simp only [Functor.comp_obj, Functor.comp_map] at hb
  rw [← cancel_epi ((rightDerivedLowerShriekExtendScalarsMap S T f).app
      ((L(sheafExtendScalars (algebraMap R S) X)).obj ((R(f)^![R]).obj K))),
    ← reassoc_of% hb, IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    rightDerivedLowerShriek_map_rightDerivedUpperShriekExtendScalarsMap_comp_counit,
    Functor.map_comp_assoc]
  have hτ := (leftDerivedSheafExtendScalarsCompMap R S T Y).naturality
    (rightDerivedUpperShriekCounit f K hK)
  simp only [Functor.comp_obj, Functor.comp_map] at hτ
  rw [hτ]
  -- transitivity of `b` at `M = Rf^! K`
  have htr :=
    rightDerivedLowerShriekExtendScalarsMap_trans (R := R) (S := S) (T := T) f ((R(f)^![R]).obj K)
  rw [← cancel_epi ((L(sheafExtendScalars (algebraMap S T) Y)).map
      ((rightDerivedLowerShriekExtendScalarsMap R S f).app ((R(f)^![R]).obj K)))]
  simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← reassoc_of% htr, IsIso.hom_inv_id_assoc]

section Constructible

variable {k : Type u} [Field k] [HasInvertibleExponent R (Spec (.of k))]
  [HasInvertibleExponent S (Spec (.of k))] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
  [QuasiCompact aY] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Blueprint `lemma-sp-reduction--5` for `K ∈ Dᵇctf(Y, R)`, over a scheme `Y` of finite type over
a field in which the exponents of `R` and `S` are invertible: the hypotheses of
`rightDerivedUpperShriekExtendScalarsMap_trans` follow from `K ∈ Dᵇctf(Y, R)`. -/
theorem rightDerivedUpperShriekExtendScalarsMap_trans_of_constructibleFiniteTor
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) Y K) :
    (leftDerivedSheafExtendScalarsCompMap R S T X).app ((R(f)^![R]).obj K) ≫
        rightDerivedUpperShriekExtendScalarsMap R T f K hK.plus
          (constructibleFiniteTor_rightDerivedUpperShriek_obj_of_field aY hK)
          (constructibleFiniteTor_leftDerivedSheafExtendScalars_rightDerivedUpperShriek_obj aY
            hK).plusEtaleOrigin
          (constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field (S := T) aY hK).plus =
      (L(sheafExtendScalars (algebraMap S T) X)).map
          (rightDerivedUpperShriekExtendScalarsMap R S f K hK.plus
            (constructibleFiniteTor_rightDerivedUpperShriek_obj_of_field aY hK)
            (constructibleFiniteTor_leftDerivedSheafExtendScalars_rightDerivedUpperShriek_obj aY
              hK).plusEtaleOrigin
            (constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field (S := S) aY
              hK).plus) ≫
        rightDerivedUpperShriekExtendScalarsMap S T f _
          (constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field (S := S) aY hK).plus
          (constructibleFiniteTor_rightDerivedUpperShriek_obj_of_field aY
            (constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field aY hK))
          (constructibleFiniteTor_leftDerivedSheafExtendScalars_rightDerivedUpperShriek_obj aY
            (constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field aY
              hK)).plusEtaleOrigin
          (constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field (S := T) aY
            (constructibleFiniteTor_leftDerivedSheafExtendScalars_obj_of_field aY hK)).plus ≫
        (R(f)^![T]).map ((leftDerivedSheafExtendScalarsCompMap R S T Y).app K) :=
  haveI : HasInvertibleExponent S X := .of_hom (f ≫ aY)
  have hΨfK :=
    constructibleFiniteTor_leftDerivedSheafExtendScalars_rightDerivedUpperShriek_obj (S := S) aY hK
  rightDerivedUpperShriekExtendScalarsMap_trans f K _ _ _ _ _ _ _ _ _ hΨfK
    (constructibleFiniteTor_leftDerivedSheafExtendScalars (S := T) (f ≫ aY) hΨfK).plusEtaleOrigin

end Constructible

end AlgebraicGeometry.ProEtale
