/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally
import WeilConjectures.AlgebraicGeometry.TangentBundle
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# First Fitting singular subscheme

Source: Stacks Project, Divisors, Tags 0C3I, 0C3J, 0C3K, and Morphisms Tag 01UM;
More on Algebra Tags 07Z6, 07Z8, 07ZA (blueprint: def-trf-first-fitting-singular-subscheme).

## Main definitions

* `isFirstFittingIdealSheaf`: the affine-local first Fitting condition.
* `firstFittingIdealSheaf`: the glued ideal sheaf of relative differentials.
* `firstFittingSingularSubscheme`: the resulting closed subscheme inclusion.

## Main statements

* `existsUnique_firstFittingIdealSheaf`: existence and uniqueness of the glued ideal sheaf.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Affine-local characterization of the first Fitting ideal sheaf of the relative
Kähler differentials.  The finite free presentation is allowed to vary with the affine
open; presentation independence and localization are supplied by
`LinearMap.presentationFittingIdeal_independence_baseChange`. (blueprint:
def-trf-first-fitting-singular-subscheme) -/
def isFirstFittingIdealSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (J : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens,
    ∃ (n : ℕ)
      (π : (Fin n → Γ(X, U.1)) →ₗ[Γ(X, U.1)] Γ(f.relativeDifferentials, U.1)),
      Function.Surjective π ∧ J.ideal U = π.presentationFittingIdeal 1

/-- Relative differentials are finite type for a locally finite type morphism.
Source: Stacks Project, Morphisms, lemma-finite-type-differentials. On an affine-pair
cover use `relativeDifferentialsRestrictFromSpecIso` and `KaehlerDifferential.finite`;
the affine finite-type criterion then descends finite generation.
(blueprint: def-trf-first-fitting-singular-subscheme) -/
private theorem relativeDifferentials_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] : f.relativeDifferentials.IsFiniteType := by
  choose U hU V hV hxV hVU using f.exists_isAffineOpen_le_preimage
  have hcover : (⨆ x, V x) = ⊤ := eq_top_iff.2 fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  have hcriterion := ((Modules.quasicoherent_finite_type_affine X).2
    f.relativeDifferentials inferInstance).2.1
  refine (hcriterion X V hcover hV ?_).1
  intro x
  let φ := f.appLE (U x) (V x) (hVU x)
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType Γ(S, U x) Γ(X, V x) := f.finiteType_appLE (hU x) (hV x) _
  have : Module.Finite Γ(X, V x) (CommRingCat.KaehlerDifferential φ) := by
    dsimp [CommRingCat.KaehlerDifferential]
    infer_instance
  let e := (moduleSpecΓFunctor.mapIso
    (f.relativeDifferentialsRestrictFromSpecIso (hU x) (hV x) (hVU x))).toLinearEquiv
  have : Module.Finite Γ(X, V x)
      (moduleSpecΓFunctor.obj (f.relativeDifferentials.restrict (hV x).fromSpec)) :=
    Module.Finite.equiv ((tilde.isoTop (CommRingCat.KaehlerDifferential φ)).toLinearEquiv
      ≪≫ₗ e.symm)
  exact Module.Finite.equiv (Modules.sectionsRestrictFromSpecLinearEquiv _ (hV x))

/-- The affine-local first Fitting ideals glue uniquely to an ideal sheaf.  The proof
uses finite generation of relative differentials on affine charts, independence of the
finite presentation, and compatibility with localization. (blueprint:
def-trf-first-fitting-singular-subscheme)

Proof: relative differentials are quasi-coherent, and finite type by the affine-pair
comparison and finite generation of algebraic Kähler differentials (Stacks Project,
Morphisms, lemma-finite-type-differentials). Use the general `fittingIdealSheaf` at
index one. The affine characterization in `fitting_ideal_generate_locally` identifies
its ideals with every finite generating surjection. Such a surjection exists on every
affine open by `finite_sections_of_finiteType` and `Module.Finite.exists_fin'`.
For any other ideal sheaf satisfying the condition, compare its witnessing surjection
with this same characterization on each affine open, then use `IdealSheafData.ext`. -/
theorem existsUnique_firstFittingIdealSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    ∃! J : X.IdealSheafData, isFirstFittingIdealSheaf f J := by
  have := relativeDifferentials_finiteType f
  let J := Modules.fittingIdealSheaf f.relativeDifferentials 1
  have hJ := (Modules.fitting_ideal_generate_locally X f.relativeDifferentials 1).1
  refine ⟨J, ?_, ?_⟩
  · intro U
    have := Modules.finite_sections_of_finiteType f.relativeDifferentials U.2
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Γ(X, U.1) Γ(f.relativeDifferentials, U.1)
    exact ⟨n, π, hπ, hJ U n π hπ⟩
  · intro K hK
    apply IdealSheafData.ext
    funext U
    obtain ⟨n, π, hπ, hKπ⟩ := hK U
    exact hKπ.trans (hJ U n π hπ).symm

/-- The glued ideal sheaf whose affine sections are the first Fitting ideals of
`Ω¹_{X/S}`.  Its data is determined uniquely by the affine-local condition above.
(blueprint: def-trf-first-fitting-singular-subscheme) -/
noncomputable def firstFittingIdealSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] : X.IdealSheafData :=
  Classical.choose (existsUnique_firstFittingIdealSheaf f)

/-- The first-Fitting singular subscheme of `f`, as the closed subscheme cut out by
`firstFittingIdealSheaf f`.  (blueprint: def-trf-first-fitting-singular-subscheme) -/
noncomputable def firstFittingSingularSubscheme {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    (firstFittingIdealSheaf f).subscheme ⟶ X :=
  (firstFittingIdealSheaf f).subschemeι

/-- The first-Fitting singular subscheme inclusion is a closed immersion, as the closed
subscheme of an ideal sheaf.  Source: Stacks Project, Divisors, Section 0C3C; Schemes
Lemma 01IN. (blueprint: def-trf-first-fitting-singular-subscheme) -/
instance firstFittingSingularSubscheme_isClosedImmersion {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    IsClosedImmersion (firstFittingSingularSubscheme f) := by
  dsimp [firstFittingSingularSubscheme]
  infer_instance

end AlgebraicGeometry.Scheme
