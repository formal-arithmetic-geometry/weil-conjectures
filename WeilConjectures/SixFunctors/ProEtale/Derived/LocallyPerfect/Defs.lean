/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Derived.Locally

/-!
# Complexes with a strictly perfect top part

Let `Y` be a scheme and `Λ` a commutative ring. The proof that a dualizable object `K` of
`D(Y_proét, Λ)` is locally perfect (Stacks, Tag 0FPV) represents `K`, locally on `Y_proét`, by
complexes `M` whose terms in degrees `≥ m` form a bounded complex of finite free constant
sheaves, for smaller and smaller `m`. This file sets up this notion and shows that it is stable
under derived pullback along weakly étale morphisms.

## Main definitions

- `AlgebraicGeometry.ProEtale.HasPerfectTop K m`: `K ≅ Q(M)` for a complex `M` containing the
  constant complex `c(E₀)` attached to a bounded complex `E₀` of finite free `Λ`-modules
  vanishing in degrees `< m`, as a subcomplex which is equal to `M` in degrees `≥ m`.

## Main results

- `AlgebraicGeometry.ProEtale.HasPerfectTop.upperStar`: stability under derived pullback along a
  weakly étale morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The isomorphism `Lg^*(Q M) ≅ Q(g^* M)` for a complex `M` of pro-étale sheaves: the derived
pullback of an exact functor is computed termwise. -/
noncomputable def leftDerivedUpperStarQObjIso {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (M : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ) :
    L((g)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex _).obj M) :=
  (leftDerivedUpperStarIsoMapDerivedCategory _ g).app _ ≪≫
    (g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryFactors.app M

/-- The pullback of the constant complex attached to a complex of `Λ`-modules is the constant
complex. -/
noncomputable def upperStarConstantComplexIso {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (E₀ : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) :
    ((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex _).obj
        (((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          _).obj E₀) ≅
      ((constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          _).obj E₀ :=
  (Functor.mapHomologicalComplexCompIso (upperStarConstantSheafIso g) _).app E₀

/-- `K ∈ D(Y_proét, Λ)` *has a perfect top part in degrees `≥ m`* if `K ≅ Q(M)` for a complex
`M` with a degreewise monomorphism `j : c(E₀) ⟶ M` from the constant complex attached to a
bounded complex `E₀` of finite free `Λ`-modules vanishing in degrees `< m`, which is an
isomorphism in degrees `≥ m`. -/
def HasPerfectTop {Y : Scheme.{u}}
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) (m : ℤ) :
    Prop :=
  ∃ (M : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ)
    (E₀ : CochainComplex (ModuleCat.{u + 1} Λ) ℤ)
    (j : ((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
      _).obj E₀ ⟶ M) (b : ℤ),
    Nonempty (K ≅ DerivedCategory.Q.obj M) ∧ (∀ i, Mono (j.f i)) ∧
      (∀ i, m ≤ i → IsIso (j.f i)) ∧ E₀.IsStrictlyGE m ∧ E₀.IsStrictlyLE b ∧
        ∀ i, Module.Free Λ (E₀.X i) ∧ Module.Finite Λ (E₀.X i)

lemma HasPerfectTop.of_iso {Y : Scheme.{u}}
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') {m : ℤ} (h : HasPerfectTop K m) : HasPerfectTop K' m := by
  obtain ⟨M, E₀, j, b, ⟨e'⟩, h⟩ := h
  exact ⟨M, E₀, j, b, ⟨e.symm ≪≫ e'⟩, h⟩

/-- Having a perfect top part is stable under derived pullback along a weakly étale morphism. -/
lemma HasPerfectTop.upperStar {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))} {m : ℤ}
    (h : HasPerfectTop K m) : HasPerfectTop (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) m := by
  obtain ⟨M, E₀, j, b, ⟨e⟩, hj, hj', hE, hE', hfree⟩ := h
  let G := (g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)
  refine ⟨G.obj M, E₀, (upperStarConstantComplexIso g E₀).inv ≫ G.map j, b,
    ⟨L((g)^*[ModuleCat.{u + 1} Λ]).mapIso e ≪≫ leftDerivedUpperStarQObjIso g M⟩,
    fun i ↦ ?_, fun i hi ↦ ?_, hE, hE', hfree⟩
  · have := hj i
    simp only [G, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    infer_instance
  · have := hj' i hi
    simp only [G, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    infer_instance

end AlgebraicGeometry.ProEtale
