/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.SmoothPurity.TraceBaseChange
public import WeilConjectures.TraceFormula.DualizableShift
public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.TateTwist.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeDualizable

/-!

# The orientation of a morphism smooth of pure relative dimension

Let `f : X ⟶ Y` be smooth of pure relative dimension `d`. The trace isomorphism
`ℚ̄_ℓ(d)[2d] ≅ Rf^! ℚ̄_ℓ` (`ProEtale.CondensedRing.isIso_smoothPurityMap`, built from the smooth
trace `ProEtale.CondensedRing.smoothTrace` of `WeilConjectures.SmoothPurity.Defs`) gives the two
properties of the relative dualizing complex `ω_f = Rf^! ℚ̄_ℓ` used by the proof of smooth purity
for `ℚ̄_ℓ`-coefficients:

- `ProEtale.CondensedRing.isDualizable_upperShriek_unit_of_smoothOfRelativeDimension`: `ω_f` is
  dualizable, the Tate twists being invertible;
- `ProEtale.CondensedRing.isIso_upperShriekBaseChange_unit_of_smoothOfRelativeDimension`: the
  formation of `ω_f` commutes with base change, the smooth trace being compatible with base change.

## Inputs

- `ProEtale.CondensedRing.isDualizable_boundedConstructibleTateTwist`: the Tate twist
  `ℚ̄_ℓ,X(d)` is invertible (blueprint `det-def-sp-tate-twist-locally-free` (3), subsection
  `sk-prop-an`).
- `ProEtale.CondensedRing.exists_iso_smoothTrace_baseChange`: the compatibility of the smooth
  trace with base change (SGA 4, Exposé XVIII, Théorème 2.9 (Var 4); blueprint
  `sk-prop-sp-purity-bc`), a property of the sorried definition `smoothTrace`, required from the
  smooth purity section. Its adjoint form is
  `ProEtale.CondensedRing.exists_iso_map_smoothPurityMap_comp_upperShriekBaseChange`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

variable (X) in
/-- **The Tate twists are invertible** (blueprint `det-def-sp-tate-twist-locally-free` (3),
subsection `sk-prop-an`: "for `Λ ∈ {A, 𝒪_E, E, ℚ̄_ℓ}` the sheaf `Λ_X(1)` is an invertible
`Λ_X`-module [...] hence so are `Λ_X(d)` and `Λ_X(-d)`"): the Tate twist `ℚ̄_ℓ,X(d)`, placed in
degree `0`, is a dualizable bounded constructible complex. -/
theorem isDualizable_boundedConstructibleTateTwist (d : ℤ) :
    IsDualizable (boundedConstructibleTateTwist ℓ X d 0) := by
  have : NeZero (ℓ : k) := ⟨fun h ↦ (Fact.out : ringChar k ≠ ℓ)
    (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k ℓ).1 h)).resolve_left
      (CharP.ringChar_ne_one))⟩
  refine (isDualizable_singleFunctor_of_isLocallyFree ℓ X (tateTwist X.left ℓ d)
    (isLocallyFree_tateTwist ℓ X.hom d)).of_iso
    ((boundedConstructible _).fullyFaithfulι.preimageIso ?_)
  exact ((shiftFunctorZero _ ℤ).app (tateTwistDerived X.left ℓ d)).symm

variable (X) in
/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]` is the shift of `ℚ̄_ℓ,X(d)` in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def boundedConstructibleTateTwistShiftIso (d n : ℤ) :
    boundedConstructibleTateTwist ℓ X d n ≅
      (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) n).obj
        (boundedConstructibleTateTwist ℓ X d 0) :=
  (boundedConstructible _).fullyFaithfulι.preimageIso
    ((shiftFunctor _ n).mapIso ((shiftFunctorZero _ ℤ).app _).symm ≪≫
      (((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
        |>.commShiftIso n).app (boundedConstructibleTateTwist ℓ X d 0)).symm)

/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]` is dualizable. -/
theorem isDualizable_boundedConstructibleTateTwist_shift (d n : ℤ) :
    IsDualizable (boundedConstructibleTateTwist ℓ X d n) :=
  (IsDualizable.shift ℓ (isDualizable_boundedConstructibleTateTwist ℓ X d) n).of_iso
    (boundedConstructibleTateTwistShiftIso ℓ X d n).symm

/-- **The relative dualizing complex of a morphism smooth of pure relative dimension is
dualizable**: `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` by the trace (`isIso_smoothPurityMap`), and the Tate twists
are invertible. -/
theorem isDualizable_upperShriek_unit_of_smoothOfRelativeDimension (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    IsDualizable ((boundedConstructibleUpperShriek ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :=
  (isDualizable_boundedConstructibleTateTwist_shift ℓ d (2 * d)).of_iso
    (asIso (smoothPurityMap ℓ f d))

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback of the purity map of `f` followed by the exceptional base change map at the unit
is the adjoint, for `Rf'_! ⊣ Rf'^!`, of the pullback of the trace of `f` read through
compact-support base change `Rf'_! Lg'^* ≅ Lg^* Rf_!`. -/
lemma homEquiv_symm_map_smoothPurityMap_comp_upperShriekBaseChange (sq : IsPullback g' f' f g)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
    ((boundedConstructibleUpperShriekAdjunction ℓ f').homEquiv _ _).symm
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (smoothPurityMap ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _)) =
      inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
          (boundedConstructibleTateTwist ℓ X d (2 * d))) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          (smoothTrace ℓ f d) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  -- naturality of compact-support base change at the purity map of `f`
  have hβ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).naturality
    (smoothPurityMap ℓ f d)
  rw [Functor.comp_map, Functor.comp_map, ← IsIso.eq_comp_inv, Category.assoc,
    ← IsIso.inv_comp_eq] at hβ
  have hf := (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv_counit
    (g := smoothPurityMap ℓ f d)
  rw [Adjunction.homEquiv_naturality_left_symm, upperShriekBaseChange, Equiv.symm_apply_apply,
    ← Category.assoc, ← hβ, Category.assoc, ← Functor.map_comp, ← hf, smoothPurityMap,
    Equiv.symm_apply_apply]

/-- Compatibility required from the smooth purity section: **the smooth trace is compatible with
base change** (SGA 4, Exposé XVIII, Théorème 2.9 (Var 4); blueprint `sk-prop-sp-purity-bc` at the
unit, `det-sp-purity-bc-factors` (1)): for a cartesian square with `f` (hence `f'`) smooth of pure
relative dimension `d`, the pullback of the purity map `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ` (the adjoint of
the trace), followed by the exceptional base change map at the unit, is the purity map of `f'` up
to an isomorphism of the Tate twists. This is the adjoint form of the compatibility of the smooth
trace with base change, `exists_iso_smoothTrace_baseChange`. -/
theorem exists_iso_map_smoothPurityMap_comp_upperShriekBaseChange (sq : IsPullback g' f' f g)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    ∃ τ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ≅
          boundedConstructibleTateTwist ℓ X' d (2 * d),
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (smoothPurityMap ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
          (boundedConstructibleUpperShriek ℓ f').map
            (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)) =
        τ.hom ≫ smoothPurityMap ℓ f' d := by
  obtain ⟨τ, hτ⟩ := exists_iso_smoothTrace_baseChange ℓ sq d
  refine ⟨τ, ((boundedConstructibleUpperShriekAdjunction ℓ f').homEquiv _ _).symm.injective ?_⟩
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_map_smoothPurityMap_comp_upperShriekBaseChange,
    Adjunction.homEquiv_naturality_left_symm, smoothPurityMap, Equiv.symm_apply_apply,
    Category.assoc, hτ]

/-- **The formation of the relative dualizing complex of a morphism smooth of pure relative
dimension commutes with base change**: the exceptional base change map at the unit is an
isomorphism, since, through the trace isomorphisms, it is an isomorphism of Tate twists
(`exists_iso_map_smoothPurityMap_comp_upperShriekBaseChange`). -/
theorem isIso_upperShriekBaseChange_unit_of_smoothOfRelativeDimension (sq : IsPullback g' f' f g)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    IsIso (upperShriekBaseChange ℓ sq (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  obtain ⟨τ, hτ⟩ := exists_iso_map_smoothPurityMap_comp_upperShriekBaseChange ℓ sq d
  have h : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
      (smoothPurityMap ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
        (boundedConstructibleUpperShriek ℓ f').map
          (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g))) := by
    rw [hτ]
    infer_instance
  have h' := IsIso.of_isIso_comp_left ((boundedConstructibleUpperStar
    (Profinite.padicAlgClRingObj ℓ) ℓ g').map (smoothPurityMap ℓ f d))
    (upperShriekBaseChange ℓ sq (𝟙_ _) ≫
      (boundedConstructibleUpperShriek ℓ f').map
        (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)))
  exact IsIso.of_isIso_comp_right _ ((boundedConstructibleUpperShriek
    ℓ f').map
      (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)))

end AlgebraicGeometry.ProEtale.CondensedRing
