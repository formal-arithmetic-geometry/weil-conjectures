/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeFrobenius
public import WeilConjectures.TraceFormula.BaseChange.WeilObject
public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.RelativeFrobenius

/-!

# The base change of the Weil lower shriek from a finite field to its algebraic closure

Let `k = 𝔽_q` be a finite field, `Ω ⊇ k` a field, `f : X ⟶ Y` a morphism of separated schemes of
finite type over `Spec k` and `e_X`, `e_Y` automorphisms over `Spec k` with `e_X ≫ f = f ≫ e_Y`.
For `N : ℕ` the base changes `X̄ = X ×_k Ω`, `Ȳ = Y ×_k Ω` carry the model Frobenii
`Φ_X = (e_X ≫ F_X^N) ×_k Ω` and `Φ_Y = (e_Y ≫ F_Y^N) ×_k Ω` (`baseChangeModelFrobenius`), which
are finite universal homeomorphisms (`isFinite_baseChangeModelFrobenius_left`,
`isUniversalHomeomorphism_baseChangeModelFrobenius_left`), and `f̄ = f ×_k Ω` commutes with them.
Its relative Frobenius `r : X̄ ⟶ X̄' = Ȳ ×_{Φ_Y, Ȳ, f̄} X̄` is therefore a finite universal
homeomorphism, and `f̄` has a lower shriek of Weil objects for the model Frobenii
(`ProEtale.CondensedRing.weilLowerShriekOfFrobenius`), the model-Frobenius setting of the
Lefschetz–Verdier formula.

The *geometric base change of the Weil lower shriek*
(`ProEtale.CondensedRing.nonempty_weilGeometricBaseChange_weilLowerShriek_iso`) identifies the
base change `Lπ_Y^* Rf_!^Weil K` of the twisted Weil lower shriek of a Weil object `K` for `e_X`
with the model Weil lower shriek `Rf̄_! Lπ_X^* K` of its base change: the compactly supported base
change `Lπ_Y^* Rf_! ≅ Rf̄_! Lπ_X^*` along `π_Y : Ȳ ⟶ Y` intertwines the two Frobenius structures.

## Main definitions

- `AlgebraicGeometry.geometricBaseChangeRelativeFrobenius`: the relative Frobenius of `f̄` for
  the model Frobenii.

## Main statements

- `AlgebraicGeometry.isPullback_geometricBaseChange_map_left`: `f̄` is the base change of `f`.
- `ProEtale.CondensedRing.nonempty_weilGeometricBaseChange_weilLowerShriek_iso`: the geometric
  base change of the Weil lower shriek.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme ProEtale.CondensedRing

variable {k : Type u} [Field k] {Ω : Type u} [Field Ω] [Algebra k Ω]

omit [Algebra k Ω] in
/-- The base change `f̄ : X̄ ⟶ Ȳ` of a morphism `f` of schemes over `Spec k` is the base change
of `f` along the projection `π_Y : Ȳ ⟶ Y`. -/
lemma isPullback_geometricBaseChange_map_left [Algebra k Ω] {X Y : Over (Spec (.of k))}
    (f : X ⟶ Y) :
    IsPullback ((geometricBaseChange k Ω).map f).left (geometricBaseChangeProj X)
      (geometricBaseChangeProj Y) f.left := by
  refine (IsPullback.of_bot ?_ (geometricBaseChange_map_left_comp_proj f).symm
    (isPullback_geometricBaseChangeProj Y)).flip
  have hw : ((geometricBaseChange k Ω).map f).left ≫ ((geometricBaseChange k Ω).obj Y).hom =
      ((geometricBaseChange k Ω).obj X).hom :=
    Over.w ((geometricBaseChange k Ω).map f)
  rw [hw, Over.w f]
  exact isPullback_geometricBaseChangeProj X

variable [Finite k]

omit [Finite k] in
/-- The base change of an isomorphism is an isomorphism. -/
instance isIso_geometricBaseChange_map_left {X : Over (Spec (.of k))} (e : X ≅ X) :
    IsIso ((geometricBaseChange k Ω).map e.hom).left :=
  inferInstanceAs (IsIso ((Over.forget _).map ((geometricBaseChange k Ω).mapIso e).hom))

/-- The model Frobenius `(g ≫ F_X^N) ×_k Ω` for an isomorphism `g` is the composite of the base
change of `g` and of the model Frobenius `F_X^N ×_k Ω`. -/
lemma baseChangeModelFrobenius_eq_comp (X : Over (Spec (.of k))) (N : ℕ) (g : X ⟶ X) :
    baseChangeModelFrobenius Ω X N g =
      (geometricBaseChange k Ω).map g ≫ baseChangeModelFrobenius Ω X N (𝟙 X) := by
  rw [baseChangeModelFrobenius, baseChangeModelFrobenius, Category.id_comp, Functor.map_comp]

/-- The model Frobenius `(e ≫ F_X^N) ×_k Ω` of an automorphism `e` is finite. -/
instance isFinite_baseChangeModelFrobenius_left {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] (N : ℕ) (e : X ≅ X) :
    IsFinite (baseChangeModelFrobenius Ω X N e.hom).left := by
  have h := (isModelFrobenius_modelFrobenius_one (Ω := Ω) X).isFinite N
  rw [← modelFrobenius_id] at h
  rw [baseChangeModelFrobenius_eq_comp, Over.comp_left]
  infer_instance

/-- The model Frobenius `(e ≫ F_X^N) ×_k Ω` of an automorphism `e` is a universal
homeomorphism. -/
instance isUniversalHomeomorphism_baseChangeModelFrobenius_left {X : Over (Spec (.of k))} (N : ℕ)
    (e : X ≅ X) : IsUniversalHomeomorphism (baseChangeModelFrobenius Ω X N e.hom).left := by
  have h := (isModelFrobenius_modelFrobenius_one (Ω := Ω) X).isUniversalHomeomorphism N
  rw [← modelFrobenius_id] at h
  rw [baseChangeModelFrobenius_eq_comp, Over.comp_left]
  infer_instance

/-- The base change `f̄` commutes with the model Frobenii `(g_X ≫ F_X^N) ×_k Ω` and
`(g_Y ≫ F_Y^N) ×_k Ω` if `g_X ≫ f = f ≫ g_Y`. -/
lemma baseChangeModelFrobenius_comp_map {X Y : Over (Spec (.of k))} (N : ℕ) {gX : X ⟶ X}
    {gY : Y ⟶ Y} {f : X ⟶ Y} (hf : gX ≫ f = f ≫ gY) :
    baseChangeModelFrobenius Ω X N gX ≫ (geometricBaseChange k Ω).map f =
      (geometricBaseChange k Ω).map f ≫ baseChangeModelFrobenius Ω Y N gY := by
  simp only [baseChangeModelFrobenius, ← Functor.map_comp, Category.assoc,
    frobeniusIterate_comp_of_comp (comp_overFrobenius f).symm N, reassoc_of% hf]

/-- The relative Frobenius `r = (f̄, Φ_X) : X̄ ⟶ Ȳ ×_{Φ_Y, Ȳ, f̄} X̄` of the base change `f̄` of
`f` for the model Frobenii `Φ_X = (g_X ≫ F_X^N) ×_k Ω` and `Φ_Y = (g_Y ≫ F_Y^N) ×_k Ω`. -/
noncomputable abbrev geometricBaseChangeRelativeFrobenius {X Y : Over (Spec (.of k))} (N : ℕ)
    {gX : X ⟶ X} {gY : Y ⟶ Y} {f : X ⟶ Y} (hf : gX ≫ f = f ≫ gY) :
    (geometricBaseChange k Ω).obj X ⟶
      pullback (baseChangeModelFrobenius Ω Y N gY) ((geometricBaseChange k Ω).map f) :=
  relativeFrobenius _ _ _ (baseChangeModelFrobenius_comp_map N hf)

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] (Ω : Type u) [Field Ω]
  [Algebra k Ω] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom) (N : ℕ)

/-- **The geometric base change of the Weil lower shriek** (Unfinished input): for a proper
morphism `f : X ⟶ Y` of separated schemes of finite type over `k = 𝔽_q` with `e_X ≫ f = f ≫ e_Y` and a
Weil object `K` for `e_X`, the base change to `Ω` of the twisted Weil lower shriek is the model
Weil lower shriek of the base change,
```
Lπ_Y^* Rf_!^Weil K ≅ Rf̄_! Lπ_X^* K
```
as Weil objects for the model Frobenius `Φ_Y = (e_Y ≫ F_Y^N) ×_k Ω`, the right side with the
Frobenius comparison of the relative Frobenius `r = (f̄, Φ_X)` of `f̄`
(`weilLowerShriekOfFrobenius`, blueprint `def-trf-weil-shriek-pushforward`). The underlying
isomorphism is the proper base change `Lπ_Y^* Rf_* ≅ Rf̄_* Lπ_X^*` along the projection
`π_Y : Ȳ ⟶ Y` (blueprint `sk-thm-sfb-proper-base-change`, for an arbitrary base change), read
through `Rf_! ≅ Rf_*`, and its compatibility with the Frobenius structures is the pasting of
`Ex_!` along the cube formed by the base change squares of `e_X`, `e_Y` and of the Frobenii,
with the trivializations `κ : (F^N)^* ≅ 𝟭` of the absolute Frobenius (blueprint
`sk-i-relative-frob` (1), `lem-trf-absolute-frobenius-site`, `fix-lem-exchanges`).

The base change runs along `Spec Ω ⟶ Spec k`, which is not of finite type, so it is outside the
compactly supported base change theorem of the project
(`isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl`), which is stated for squares of
separated schemes of finite type over one field. -/
theorem nonempty_weilGeometricBaseChange_weilLowerShriek_iso [IsProper f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) :
    Nonempty ((weilGeometricBaseChange Ω ℓ Y N eY.hom).obj ((weilLowerShriek ℓ eX eY hf).obj K) ≅
      (weilLowerShriekOfFrobenius ℓ (baseChangeModelFrobenius Ω X N eX.hom)
        (baseChangeModelFrobenius Ω Y N eY.hom) ((geometricBaseChange k Ω).map f)
        (IsPullback.of_hasPullback (baseChangeModelFrobenius Ω Y N eY.hom)
          ((geometricBaseChange k Ω).map f)).flip
        (geometricBaseChangeRelativeFrobenius N hf) (relativeFrobenius_snd _ _ _ _)
        (relativeFrobenius_fst _ _ _ _)).obj
        ((weilGeometricBaseChange Ω ℓ X N eX.hom).obj K)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
