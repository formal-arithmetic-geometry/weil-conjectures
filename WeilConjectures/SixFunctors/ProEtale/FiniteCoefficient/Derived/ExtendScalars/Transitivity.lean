/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

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

section Comp

variable {R S T : Type (u + 1)} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
  (ψ : S →+* T) (χ : R →+* T) (h : χ = ψ.comp φ) (X : Scheme.{u})

/-- Restriction of scalars of pro-étale sheaves along `χ = ψ ∘ φ` is restriction along `ψ` followed
by restriction along `φ`. -/
noncomputable def sheafRestrictScalarsCompIso :
    sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} ψ) ⋙
        sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ) ≅
      sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} χ) where
  hom := sheafCompose_map (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalarsComp'.{u + 1} φ ψ χ h).inv
  inv := sheafCompose_map (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalarsComp'.{u + 1} φ ψ χ h).hom
  hom_inv_id := by
    rw [← sheafCompose_comp, Iso.inv_hom_id, sheafCompose_id]
    rfl
  inv_hom_id := by
    rw [← sheafCompose_comp, Iso.hom_inv_id, sheafCompose_id]

/-- Extension of scalars of pro-étale sheaves along `ψ ∘ φ` is extension along `φ` followed by
extension along `ψ`: the conjugate of `sheafRestrictScalarsCompIso`. -/
noncomputable def sheafExtendScalarsCompIso :
    sheafExtendScalars χ X ≅ sheafExtendScalars φ X ⋙ sheafExtendScalars ψ X :=
  (conjugateIsoEquiv ((sheafExtendScalarsAdjunction φ X).comp (sheafExtendScalarsAdjunction ψ X))
    (sheafExtendScalarsAdjunction χ X)).symm (sheafRestrictScalarsCompIso φ ψ χ h X)

end Comp

variable {R S T : Type (u + 1)} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable (R S T) in
/-- The comparison `τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}` of the derived extensions of scalars of
pro-étale sheaves along `R → S → T`: the morphism into the left derived functor `Ψ_{R,T}` induced
by the composite of the counits of `Ψ_{R,S}` and `Ψ_{S,T}` and the isomorphism
`T ⊗_S (S ⊗_R -) ≅ T ⊗_R -` (`sheafExtendScalarsCompIso`). -/
noncomputable def leftDerivedSheafExtendScalarsCompMap (X : Scheme.{u}) :
    L(sheafExtendScalars (algebraMap R S) X) ⋙ L(sheafExtendScalars (algebraMap S T) X) ⟶
      L(sheafExtendScalars (algebraMap R T) X) :=
  (L(sheafExtendScalars (algebraMap R T) X)).leftDerivedLift
    (sheafExtendScalars (algebraMap R T) X).leftDerivedFunctorCounit
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (L(sheafExtendScalars (algebraMap R S) X) ⋙ L(sheafExtendScalars (algebraMap S T) X))
    (Functor.whiskerRight (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorCounit
        L(sheafExtendScalars (algebraMap S T) X) ≫
      Functor.whiskerLeft
        ((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (ComplexShape.up ℤ))
        (sheafExtendScalars (algebraMap S T) X).leftDerivedFunctorCounit ≫
      Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
        (sheafExtendScalarsCompIso (algebraMap R S) (algebraMap S T) (algebraMap R T)
          (IsScalarTower.algebraMap_eq R S T) X).symm (ComplexShape.up ℤ)).hom
        DerivedCategory.Qh)

variable [Finite R] [Finite S] [Finite T] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `lemma-sp-reduction--4`: **transitivity of the comparison for `Rf_!`**. For
`R → S → T` and `M ∈ Dᵇctf(X, R)`, the comparison `b_{R,T}(M)` is the composite of `b_{R,S}`
and `b_{S,T}`, along `τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`:

`b_{R,T}(M) ∘ τ(Rf_! M) = Rf_!(τ(M)) ∘ b_{S,T}(Ψ_{R,S} M) ∘ Ψ_{S,T}(b_{R,S}(M))`.

TODO: both comparisons are built through the compactification from the base change maps of the
extensions of scalars along `Rg_*` and from their commutation with `i_!`; associativity of the
tensor product identifies the direct comparison with the successive ones. -/
theorem rightDerivedLowerShriekExtendScalarsMap_trans
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X M) :
    (leftDerivedSheafExtendScalarsCompMap R S T Y).app ((R(f)_![ModuleCat.{u + 1} R]).obj M) ≫
        (rightDerivedLowerShriekExtendScalarsMap R T f).app M =
      (L(sheafExtendScalars (algebraMap S T) Y)).map
          ((rightDerivedLowerShriekExtendScalarsMap R S f).app M) ≫
        (rightDerivedLowerShriekExtendScalarsMap S T f).app
          ((L(sheafExtendScalars (algebraMap R S) X)).obj M) ≫
        (R(f)_![ModuleCat.{u + 1} T]).map
          ((leftDerivedSheafExtendScalarsCompMap R S T X).app M) := by
  sorry

variable [CompactSpace Y]

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
  have htr := rightDerivedLowerShriekExtendScalarsMap_trans (R := R) (S := S) (T := T) f _ hfK
  rw [← cancel_epi ((L(sheafExtendScalars (algebraMap S T) Y)).map
      ((rightDerivedLowerShriekExtendScalarsMap R S f).app ((R(f)^![R]).obj K)))]
  simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← reassoc_of% htr, IsIso.hom_inv_id_assoc]

end AlgebraicGeometry.ProEtale
