/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveUnit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSections

/-!
# Pro-étale sheaves on the spectrum of an algebraically closed field

Let `X` be a scheme isomorphic to `Spec K` for an algebraically closed field `K`. Every
pro-étale cover of `X` has a section (`AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale`), so
every covering sieve of the terminal object of `X_proét` is the maximal sieve. Hence taking
sections over `X` is exact on pro-étale sheaves with values in a concrete category, such as
`Λ`-modules or `ℓ`-adic coefficients. For a commutative ring `Λ`, the constant sheaf `Λ_X`, the
monoidal unit, is then a projective object: it corepresents sections over `X`. As a consequence
there are no nonzero morphisms `Λ_X ⟶ Λ_X[1]` in the derived category, that is,
`H¹(X_proét, Λ) = 0`.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.id_mem_of_mem_topology_of_iso`: a covering sieve of the
  terminal object of `X_proét` contains the identity.
- `AlgebraicGeometry.ProEtale.surjective_app_of_epi_of_iso`: an epimorphism of pro-étale sheaves
  on `X` with values in a concrete category is surjective on sections over `X`.
- `AlgebraicGeometry.ProEtale.projective_unit_of_iso`: the unit `Λ_X` is projective.
- `AlgebraicGeometry.ProEtale.DerivedCategory.unit_hom_shift_one_eq_zero_of_iso`: every
  morphism `Λ_X ⟶ Λ_X[1]` in `D(X_proét, Λ)` is zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}

/-- A covering sieve of the terminal object of the small pro-étale site of a scheme `X`
isomorphic to the spectrum of an algebraically closed field `K` contains the identity: a member
`f : V ⟶ X` of a pro-étale covering family with `V` nonempty has a section. -/
lemma Scheme.ProEt.id_mem_of_mem_topology_of_iso (e : X ≅ Spec (.of K))
    {S : Sieve (Scheme.ProEt.mk (𝟙 X))} (hS : S ∈ Scheme.ProEt.topology X _) : S (𝟙 _) := by
  obtain ⟨R, hR, hRS⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  have hR' := (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from
    inf_le_right) _ hR
  obtain ⟨Y, g, hg, x, -⟩ := hR'.1 (e.inv.base (IsLocalRing.closedPoint K))
  obtain ⟨hg⟩ := hg
  obtain @⟨V, f, hf⟩ := hg
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (V.hom ≫ e.hom) x
  have hσ' : σ ≫ V.hom = e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, hσ, e.inv_hom_id]
  have hσ'' : (e.hom ≫ σ) ≫ V.hom = (Scheme.ProEt.mk (𝟙 X)).hom := by
    rw [Category.assoc, hσ', e.hom_inv_id]
    rfl
  have : S (MorphismProperty.Over.homMk (A := Scheme.ProEt.mk (𝟙 X)) (e.hom ≫ σ) hσ'' ≫ f) :=
    S.downward_closed (hRS _ _ hf) _
  convert this
  exact (Scheme.ProEt.isTerminalMkId _).hom_ext _ _

namespace ProEtale

section Concrete

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]

/-- An epimorphism of pro-étale sheaves with values in a concrete category `A` on a scheme `X`
isomorphic to the spectrum of an algebraically closed field is surjective on sections over `X`:
it is locally surjective, and every covering sieve of `X` is the maximal sieve. -/
lemma surjective_app_of_epi_of_iso (e : X ≅ Spec (.of K))
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective A]
    [HasSheafify (Scheme.ProEt.topology X) A]
    [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf (Scheme.ProEt.topology X) A)]
    {F G : Sheaf (Scheme.ProEt.topology X) A} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) := by
  have := (Sheaf.isLocallySurjective_iff_epi' A φ).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := Scheme.ProEt.id_mem_of_mem_topology_of_iso e
    (Presheaf.imageSieve_mem (Scheme.ProEt.topology _) φ.hom s)
  exact ⟨t, by simpa using ht⟩

/-- Taking sections over `X` preserves epimorphisms of pro-étale sheaves with values in a
concrete category on a scheme `X` isomorphic to the spectrum of an algebraically closed
field. -/
lemma preservesEpimorphisms_sheafSections_of_iso (e : X ≅ Spec (.of K))
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective A]
    [HasSheafify (Scheme.ProEt.topology X) A]
    [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf (Scheme.ProEt.topology X) A)] :
    ((sheafSections (Scheme.ProEt.topology X) A).obj
      (op (Scheme.ProEt.mk (𝟙 X)))).PreservesEpimorphisms where
  preserves φ _ := (CategoryTheory.forget A).epi_of_epi_map
    ((epi_iff_surjective _).2 (surjective_app_of_epi_of_iso e φ))

end Concrete

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The monoidal unit `Λ_X` of pro-étale sheaves of `Λ`-modules on a scheme `X` isomorphic to
the spectrum of an algebraically closed field is projective: it is the constant sheaf on the
projective module `Λ`, and the constant sheaf functor is left adjoint to taking sections over
the terminal object `X`, which preserves epimorphisms. -/
lemma projective_unit_of_iso (e : X ≅ Spec (.of K)) :
    Projective (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) := by
  have := preservesEpimorphisms_sheafSections_of_iso (A := ModuleCat.{u + 1} Λ) e
  have hP : Projective ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
      (𝟙_ (ModuleCat.{u + 1} Λ))) :=
    (constantSheafAdj _ _ (Scheme.ProEt.isTerminalMkId X)).map_projective _
      (ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of Λ Λ))
  exact Projective.of_iso
    (Functor.Monoidal.εIso (presheafToSheaf (Scheme.ProEt.topology X) _)).symm hP

/-- On a scheme `X` isomorphic to the spectrum of an algebraically closed field, every morphism
`Λ_X ⟶ Λ_X[1]` in the derived category of pro-étale sheaves of `Λ`-modules is zero, the unit
`Λ_X` being projective (`AlgebraicGeometry.ProEtale.projective_unit_of_iso`): this is the
vanishing of `H¹(X_proét, Λ)`. -/
lemma DerivedCategory.unit_hom_shift_one_eq_zero_of_iso (e : X ≅ Spec (.of K))
    (φ : 𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) ⟶
      (𝟙_ _)⟦(1 : ℤ)⟧) : φ = 0 :=
  have := projective_unit_of_iso Λ e
  _root_.DerivedCategory.unit_hom_shift_eq_zero_of_projective 1 one_pos φ

end ProEtale

end AlgebraicGeometry
