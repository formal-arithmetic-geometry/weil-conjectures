/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Étale sheaves of modules on the spectrum of an algebraically closed field

This is the étale counterpart of `WeilConjectures.SixFunctors.ProEtale.Derived.AlgClosedField`.
Let `X` be a scheme isomorphic to `Spec K` for an algebraically closed field `K`, and let `Λ`
be a commutative ring. Every étale cover of `X` has a section, so every covering sieve of the
terminal object of `X_ét` is the maximal sieve. Hence taking sections over `X` is exact on
étale sheaves of `Λ`-modules, the constant sheaf `Λ_X`, the monoidal unit, is projective, and
there are no nonzero morphisms `Λ_X ⟶ Λ_X[1]` in the derived category, that is,
`H¹(X_ét, Λ) = 0`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.id_mem_of_mem_smallEtaleTopology_of_iso`: a covering sieve of
  the terminal object of `X_ét` contains the identity.
- `AlgebraicGeometry.Etale.surjective_app_of_epi_of_iso`: an epimorphism of étale sheaves of
  `Λ`-modules on `X` is surjective on sections over `X`.
- `AlgebraicGeometry.Etale.projective_unit_of_iso`: the unit `Λ_X` is projective.
- `AlgebraicGeometry.Etale.DerivedCategory.unit_hom_shift_one_eq_zero_of_iso`: every morphism
  `Λ_X ⟶ Λ_X[1]` in `D(X_ét, Λ)` is zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}

/-- A covering sieve of the terminal object of the small étale site of a scheme `X` isomorphic
to the spectrum of an algebraically closed field `K` contains the identity: a member
`f : V ⟶ X` of an étale covering family with `V` nonempty has a section. -/
lemma Scheme.Etale.id_mem_of_mem_smallEtaleTopology_of_iso (e : X ≅ Spec (.of K))
    {S : Sieve (Scheme.Etale.mk (𝟙 X))} (hS : S ∈ X.smallEtaleTopology _) : S (𝟙 _) := by
  obtain ⟨V, g, hg, x, -⟩ :=
    (mem_smallEtaleTopology_iff S).1 hS (e.inv.base (IsLocalRing.closedPoint K))
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (V.hom ≫ e.hom) x
  have hσ' : σ ≫ V.hom = e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, hσ, e.inv_hom_id]
  have hσ'' : (e.hom ≫ σ) ≫ V.hom = (Scheme.Etale.mk (𝟙 X)).hom := by
    rw [Category.assoc, hσ', e.hom_inv_id]
    rfl
  have : S (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (𝟙 X)) (e.hom ≫ σ) hσ'' ≫ g) :=
    S.downward_closed hg _
  convert this
  exact (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X).hom_ext _ _

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {Λ} in
/-- An epimorphism of étale sheaves of `Λ`-modules on a scheme `X` isomorphic to the spectrum
of an algebraically closed field is surjective on sections over `X`: it is locally surjective,
and every covering sieve of `X` is the maximal sieve. -/
lemma surjective_app_of_epi_of_iso (e : X ≅ Spec (.of K))
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Scheme.Etale.mk (𝟙 X)))) := by
  have := (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := Scheme.Etale.id_mem_of_mem_smallEtaleTopology_of_iso e
    (Presheaf.imageSieve_mem X.smallEtaleTopology φ.hom s)
  exact ⟨t, by simpa using ht⟩

/-- Taking sections over `X` preserves epimorphisms of étale sheaves of `Λ`-modules on a scheme
`X` isomorphic to the spectrum of an algebraically closed field. -/
lemma preservesEpimorphisms_sheafSections_of_iso (e : X ≅ Spec (.of K)) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (op (Scheme.Etale.mk (𝟙 X)))).PreservesEpimorphisms where
  preserves φ _ := (ModuleCat.epi_iff_surjective _).2 (surjective_app_of_epi_of_iso e φ)

/-- The monoidal unit `Λ_X` of étale sheaves of `Λ`-modules on a scheme `X` isomorphic to the
spectrum of an algebraically closed field is projective: it is the constant sheaf on the
projective module `Λ`, and the constant sheaf functor is left adjoint to taking sections over
the terminal object `X`, which preserves epimorphisms. -/
lemma projective_unit_of_iso (e : X ≅ Spec (.of K)) :
    Projective (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) := by
  have := preservesEpimorphisms_sheafSections_of_iso Λ e
  have hP : Projective ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (𝟙_ (ModuleCat.{u + 1} Λ))) :=
    (constantSheafAdj _ _
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).map_projective _
      (ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of Λ Λ))
  exact Projective.of_iso
    (Functor.Monoidal.εIso (presheafToSheaf X.smallEtaleTopology _)).symm hP

/-- On a scheme `X` isomorphic to the spectrum of an algebraically closed field, every morphism
`Λ_X ⟶ Λ_X[1]` in the derived category of étale sheaves of `Λ`-modules is zero, the unit `Λ_X`
being projective (`AlgebraicGeometry.Etale.projective_unit_of_iso`): this is the vanishing of
`H¹(X_ét, Λ)`. -/
lemma DerivedCategory.unit_hom_shift_one_eq_zero_of_iso (e : X ≅ Spec (.of K))
    (φ : 𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ⟶
      (𝟙_ _)⟦(1 : ℤ)⟧) : φ = 0 := by
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have := projective_unit_of_iso Λ e
  let e₁ : 𝟙_ (_root_.DerivedCategory C) ≅
      _root_.DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj (𝟙_ C)) :=
    (_root_.DerivedCategory.singleFunctorObjUnitIso C).symm ≪≫
      (_root_.DerivedCategory.singleFunctorIsoCompQ C 0).app _
  let e₂ : (𝟙_ (_root_.DerivedCategory C))⟦(1 : ℤ)⟧ ≅
      _root_.DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-1)).obj (𝟙_ C)) :=
    (shiftFunctor _ (1 : ℤ)).mapIso (_root_.DerivedCategory.singleFunctorObjUnitIso C).symm ≪≫
      ((_root_.DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0 (by norm_num)).app _ ≪≫
      (_root_.DerivedCategory.singleFunctorIsoCompQ C (-1)).app _
  have h : e₁.inv ≫ φ ≫ e₂.hom = 0 :=
    _root_.DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective _ (-1) (by norm_num)
  rw [← cancel_epi e₁.inv, ← cancel_mono e₂.hom, Limits.comp_zero, Limits.zero_comp,
    Category.assoc, h]

end Etale

end AlgebraicGeometry
