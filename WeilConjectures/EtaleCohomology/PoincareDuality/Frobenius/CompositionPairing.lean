/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit

/-!
# The composition pairing at the point over a field

Let `Λ` be a finite field. In the derived category `D(Λ)`, with unit `U = Λ[0]`, the composition
pairing
`Hom(U, E) × Hom(E, U) ⟶ End(U) = Λ`
is nondegenerate on both sides as soon as `H^0(E)` is finite-dimensional: over a field `E` is
split, `E ≅ ⊕ H^n(E)[-n]`, and both sides are computed by the degree-zero summand. Through the
equivalence `RΓ(Spec k, -) : D(Spec k_ét, Λ) ≌ D(Λ)` for `k` separably closed, the same holds
in the point category, with `U` the unit `Λ_s`.

This is the input from linear algebra for the degreewise perfectness of the Poincaré pairings
over a field (`WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Perfectness`).

## Main statements

- `LinearMap.isPerfPair_of_comp`: a bilinear pairing which is a composition pairing
  `⟨x, y⟩ = ℓ(x ≫ g(y))` with `g` bijective and both sides nondegenerate is perfect.
- `DerivedCategory.nondegenerate_comp_singleFunctor_of_isField`: the composition pairing with
  `Λ[0]` in `D(Λ)` is nondegenerate.
- `AlgebraicGeometry.Etale.nondegenerate_comp_unit_of_isSepClosed`: the composition pairing with
  the unit `Λ_s` of the point category is nondegenerate.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
  [F.Full] [F.Faithful] [F.PreservesZeroMorphisms] {U E : C} {U' E' : D}

/-- Nondegeneracy of the composition pairing `Hom(U, E) × Hom(E, U) ⟶ End(U)` on the left is
reflected by a fully faithful functor `F`, with `F(U) ≅ U'` and `F(E) ≅ E'`. -/
lemma exists_comp_ne_zero_of_fullyFaithful (eU : F.obj U ≅ U') (eE : F.obj E ≅ E')
    (h : ∀ x : U' ⟶ E', x ≠ 0 → ∃ f : E' ⟶ U', x ≫ f ≠ 0) (x : U ⟶ E) (hx : x ≠ 0) :
    ∃ f : E ⟶ U, x ≫ f ≠ 0 := by
  obtain ⟨f', hf'⟩ := h (eU.inv ≫ F.map x ≫ eE.hom) fun h0 ↦ hx <| by
    rw [← F.map_eq_zero_iff]
    simpa using congrArg (fun z ↦ eU.hom ≫ z ≫ eE.inv) h0
  refine ⟨F.preimage (eE.hom ≫ f' ≫ eU.inv), fun h0 ↦ hf' ?_⟩
  have := congrArg (fun z ↦ eU.inv ≫ F.map z ≫ eU.hom) h0
  simpa using this

/-- Nondegeneracy of the composition pairing `Hom(U, E) × Hom(E, U) ⟶ End(U)` on the right is
reflected by a fully faithful functor `F`, with `F(U) ≅ U'` and `F(E) ≅ E'`. -/
lemma exists_comp_ne_zero_of_fullyFaithful' (eU : F.obj U ≅ U') (eE : F.obj E ≅ E')
    (h : ∀ f : E' ⟶ U', f ≠ 0 → ∃ x : U' ⟶ E', x ≫ f ≠ 0) (f : E ⟶ U) (hf : f ≠ 0) :
    ∃ x : U ⟶ E, x ≫ f ≠ 0 := by
  obtain ⟨x', hx'⟩ := h (eE.inv ≫ F.map f ≫ eU.hom) fun h0 ↦ hf <| by
    rw [← F.map_eq_zero_iff]
    simpa using congrArg (fun z ↦ eE.hom ≫ z ≫ eU.inv) h0
  refine ⟨F.preimage (eU.hom ≫ x' ≫ eE.inv), fun h0 ↦ hx' ?_⟩
  have := congrArg (fun z ↦ eU.inv ≫ F.map z ≫ eU.hom) h0
  simpa using this

omit [Preadditive C] [Preadditive D] [F.PreservesZeroMorphisms] in
/-- Finiteness of `Hom(U, E)` is reflected by a fully faithful functor. -/
lemma finite_hom_of_fullyFaithful (eU : F.obj U ≅ U') (eE : F.obj E ≅ E')
    [Finite (U' ⟶ E')] : Finite (U ⟶ E) :=
  Finite.of_equiv _ ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
    (eU.homCongr eE)).symm

end CategoryTheory.Functor

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

instance : Projective (ModuleCat.of R R) :=
  ModuleCat.projective_of_free (Module.Basis.singleton Unit R)

/-- For a module `M` over `R`, morphisms `R[0] ⟶ E` in `D(R)` are the elements of `H^0(E)`. -/
noncomputable def homSingleRingEquiv (E : DerivedCategory (ModuleCat.{u} R)) :
    ((singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E) ≃
      (homologyFunctor (ModuleCat.{u} R) 0).obj E :=
  (homSingleEquivOfProjective (ModuleCat.of R R) 0 E).trans
    (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toEquiv)

end DerivedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

variable (Λ k) in
/-- Over a separably closed field `k`, the derived global sections of the unit `Λ_s` of the point
category are `Λ[0]`. -/
noncomputable def rightDerivedGlobalSectionsUnitIso :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of Λ Λ) :=
  (rightDerivedGlobalSections _ _).mapIso (unitIsoSingleFunctorConstantSheaf Λ _) ≪≫
    (rightDerivedGlobalSectionsIsoMapDerivedCategoryInv _ _).app _ ≪≫
      ((constantSheaf (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).inv.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((constantSheaf (Spec (.of k)).smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).asEquivalence.unitIso.app _).symm

end AlgebraicGeometry.Etale
