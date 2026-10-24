/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeFrobenius
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightCube
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraExchangeCube
public import WeilConjectures.TraceFormula.BaseChange.CubeCoherence
public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.RelativeFrobeniusProper
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

open scoped CategoryTheory.Functor CategoryTheory.Obj

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
  refine (IsPullback.of_bot ?_ (geometricBaseChange_map_left_comp_proj (Ω := Ω) f).symm
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

/-! ### Proper base change along the base change `π` -/

section ProperBaseChange

variable {Ω} (f) in
/-- The transport `L(f̄ ≫ π_Y)^* ≅ L(π_X ≫ f)^*` along the square `f̄ ≫ π_Y = π_X ≫ f`. -/
noncomputable def leftDerivedUpperStarGeometricBaseChangeCongr :
    L((Over.Hom.left ((geometricBaseChange k Ω).map f) ≫
        geometricBaseChangeProj (Ω := Ω) Y)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((geometricBaseChangeProj (Ω := Ω) X ≫ f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  pullbackCongrIso (D := fun S ↦ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S)
    Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)))
    (fun t ↦ L((t)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (geometricBaseChange_map_left_comp_proj (Ω := Ω) f)

variable {Ω} (f) in
/-- The comparison `Lπ_Y^* ⋙ Lf̄^* ≅ Lf^* ⋙ Lπ_X^*` of the derived pullbacks along the square
`f̄ ≫ π_Y = π_X ≫ f` of the base change, on the ambient derived categories: the composite
`L(f̄ ≫ π_Y)^* = L(π_X ≫ f)^*` of the composition isomorphisms. -/
noncomputable def leftDerivedUpperStarGeometricBaseChangeComparison :
    L((geometricBaseChangeProj (Ω := Ω) Y)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((Over.Hom.left ((geometricBaseChange k Ω).map f))^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((geometricBaseChangeProj (Ω := Ω) X)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ)
      ((geometricBaseChange k Ω).map f).left (geometricBaseChangeProj (Ω := Ω) Y)).symm ≪≫
    leftDerivedUpperStarGeometricBaseChangeCongr ℓ f ≪≫
    leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ)
      (geometricBaseChangeProj (Ω := Ω) X) f.left

variable {Ω} (f) in
/-- The components of `leftDerivedUpperStarGeometricBaseChangeComparison`. -/
lemma leftDerivedUpperStarGeometricBaseChangeComparison_hom_app
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))) :
    (leftDerivedUpperStarGeometricBaseChangeComparison ℓ (Ω := Ω) f).hom.app M =
      (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ)
          ((geometricBaseChange k Ω).map f).left (geometricBaseChangeProj (Ω := Ω) Y)).inv.app M ≫
        (leftDerivedUpperStarGeometricBaseChangeCongr ℓ f).hom.app M ≫
        (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ)
          (geometricBaseChangeProj (Ω := Ω) X) f.left).hom.app M := by
  simp only [leftDerivedUpperStarGeometricBaseChangeComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]

variable (f) in
/-- The comparison `θ_π : Lπ_Y^* ⋙ Lf̄^* ≅ Lf^* ⋙ Lπ_X^*` of the derived pullbacks along the
square `f̄ ≫ π_Y = π_X ≫ f` of the base change, on bounded constructible complexes. -/
noncomputable def geometricBaseChangePullbackComparison :
    geometricBaseChangeUpperStar Ω ℓ Y ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          ((geometricBaseChange k Ω).map f) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        geometricBaseChangeUpperStar Ω ℓ X :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((leftDerivedUpperStarGeometricBaseChangeComparison ℓ (Ω := Ω) f).app K.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((leftDerivedUpperStarGeometricBaseChangeComparison ℓ (Ω := Ω) f).hom.naturality φ.hom))

variable (f) in
/-- On the ambient derived categories, `θ_π` is
`leftDerivedUpperStarGeometricBaseChangeComparison`. -/
lemma geometricBaseChangePullbackComparison_hom_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((geometricBaseChangePullbackComparison ℓ Ω f).hom.app K).hom =
      (leftDerivedUpperStarGeometricBaseChangeComparison ℓ (Ω := Ω) f).hom.app K.obj :=
  (congrArg InducedCategory.Hom.hom (NatIso.ofComponents_hom_app _ _ K)).trans
    ((congrArg InducedCategory.Hom.hom (ObjectProperty.isoMk_hom _ _)).trans
      ((ObjectProperty.homMk_hom _).trans (Iso.app_hom _ _)))

variable (f) in
/-- The *base change morphism along the base change* `Ex_π : Lπ_Y^* Rf_* ⟶ Rf̄_* Lπ_X^*` of the
square `f̄ ≫ π_Y = π_X ≫ f`: the exchange morphism of `θ_π` under the adjunctions
`Lf^* ⊣ Rf_*` and `Lf̄^* ⊣ Rf̄_*`. -/
noncomputable abbrev geometricBaseChangeLowerStarBaseChange :
    boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        geometricBaseChangeUpperStar Ω ℓ Y ⟶
      geometricBaseChangeUpperStar Ω ℓ X ⋙
        boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
          ((geometricBaseChange k Ω).map f) :=
  Adjunction.exchangeRight
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      ((geometricBaseChange k Ω).map f))
    (geometricBaseChangePullbackComparison ℓ Ω f)

variable (f) in
/-- **Proper base change along the base change to `Ω`** (blueprint
`sk-thm-sfb-proper-base-change`, for the cartesian square `f̄ ≫ π_Y = π_X ≫ f`,
`isPullback_geometricBaseChange_map_left`): for a proper morphism `f` of separated schemes of
finite type over `k`, the base change morphism `Ex_π : Lπ_Y^* Rf_* ⟶ Rf̄_* Lπ_X^*` along the
projection `π_Y : Ȳ ⟶ Y` is an isomorphism on bounded constructible complexes. The blueprint
statement is for an arbitrary cartesian square; the project's version
(`isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`) only covers squares of schemes of
finite type over one field, and `π_Y` is the base change of `Spec Ω ⟶ Spec k`, which is not of
finite type. -/
theorem isIso_geometricBaseChangeLowerStarBaseChange [IsProper f.left] :
    IsIso (geometricBaseChangeLowerStarBaseChange ℓ Ω f) :=
  sorry

omit [Finite k] in
/-- The base change `f̄` of a proper morphism is proper. -/
instance isProper_geometricBaseChange_map_left [IsProper f.left] :
    IsProper ((geometricBaseChange k Ω).map f).left :=
  MorphismProperty.of_isPullback (isPullback_geometricBaseChange_map_left f).flip ‹_›

end ProperBaseChange

/-! ### The Frobenius structures -/

section Frobenius

variable [IsProper f.left]

omit [IsProper f.left] in
include hf in
/-- The square `Φ_X ≫ f̄ = f̄ ≫ Φ_Y` of the model Frobenii, as a commutative square. -/
lemma commSq_baseChangeModelFrobenius :
    CommSq (baseChangeModelFrobenius Ω X N eX.hom) ((geometricBaseChange k Ω).map f)
      ((geometricBaseChange k Ω).map f) (baseChangeModelFrobenius Ω Y N eY.hom) :=
  ⟨baseChangeModelFrobenius_comp_map N hf⟩

/-- **The pullback cube**: on bounded constructible complexes, the comparisons of the derived
pullbacks along the squares of `e`, of the base change `π` and of the model Frobenii `Φ`
commute with the Frobenius comparisons of the base change
(`weilGeometricBaseChangeComparison`). -/
lemma geometricBaseChangePullbackComparison_cube (We : CommSq eX.hom f f eY.hom)
    (WΦ : CommSq (baseChangeModelFrobenius Ω X N eX.hom) ((geometricBaseChange k Ω).map f)
      ((geometricBaseChange k Ω).map f) (baseChangeModelFrobenius Ω Y N eY.hom)) :
    Adjunction.CubeCondition
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        We)
      (geometricBaseChangePullbackComparison ℓ Ω f)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        WΦ)
      (weilGeometricBaseChangeComparison Ω ℓ X N eX.hom)
      (weilGeometricBaseChangeComparison Ω ℓ Y N eY.hom) := by
  intro M
  sorry

/-- Under `Rf_! ≅ Rf_*`, the Frobenius comparison `b_! : Rf_! ⋙ Le_Y^* ≅ Le_X^* ⋙ Rf_!` of the
twisted Weil lower shriek is the direct-image exchange morphism `Ex_e` of the square of `e`
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper`). -/
lemma weilLowerShriekComparison_exchangeCompatible :
    Adjunction.ExchangeCompatible
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (weilFrobeniusSquare eX eY hf).toCommSq)
      (weilLowerShriekComparison ℓ eX eY hf)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f) := by
  intro K
  have h := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper ℓ
    (weilFrobeniusSquare eX eY hf) K
  rw [boundedConstructibleBaseChange_eq_exchangeRight] at h
  rw [weilLowerShriekComparison_hom]
  exact h

/-- Under `Rf̄_! ≅ Rf̄_*`, the Frobenius comparison `θ_f̄` of the model Weil lower shriek is the
direct-image exchange morphism `Ex_Φ` of the square of the model Frobenii
(`weilLowerShriekFrobeniusComparison_hom_app_comp_isoLowerStar_of_commSq`). -/
lemma weilLowerShriekFrobeniusComparison_exchangeCompatible :
    Adjunction.ExchangeCompatible
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        ((geometricBaseChange k Ω).map f))
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (commSq_baseChangeModelFrobenius Ω eX eY hf N))
      (weilLowerShriekFrobeniusComparison ℓ (baseChangeModelFrobenius Ω X N eX.hom)
        (baseChangeModelFrobenius Ω Y N eY.hom) ((geometricBaseChange k Ω).map f)
        (IsPullback.of_hasPullback (baseChangeModelFrobenius Ω Y N eY.hom)
          ((geometricBaseChange k Ω).map f)).flip
        (geometricBaseChangeRelativeFrobenius N hf) (relativeFrobenius_snd _ _ _ _)
        (relativeFrobenius_fst _ _ _ _))
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
        ((geometricBaseChange k Ω).map f)) := by
  intro K
  have h := weilLowerShriekFrobeniusComparison_hom_app_comp_isoLowerStar_of_commSq ℓ
    (baseChangeModelFrobenius Ω X N eX.hom) (baseChangeModelFrobenius Ω Y N eY.hom)
    ((geometricBaseChange k Ω).map f)
    (IsPullback.of_hasPullback (baseChangeModelFrobenius Ω Y N eY.hom)
      ((geometricBaseChange k Ω).map f)).flip
    (geometricBaseChangeRelativeFrobenius N hf) (relativeFrobenius_snd _ _ _ _)
    (relativeFrobenius_fst _ _ _ _) (commSq_baseChangeModelFrobenius Ω eX eY hf N) K
  rw [boundedConstructibleBaseChange_eq_exchangeRight] at h
  exact h

end Frobenius

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
        ((weilGeometricBaseChange Ω ℓ X N eX.hom).obj K)) := by
  haveI := isIso_geometricBaseChangeLowerStarBaseChange ℓ Ω f
  have hc := Adjunction.nonempty_mapOfNatIso_obj_iso_of_cubeCondition
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      ((geometricBaseChange k Ω).map f))
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      (weilFrobeniusSquare eX eY hf).toCommSq)
    (geometricBaseChangePullbackComparison ℓ Ω f)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      (commSq_baseChangeModelFrobenius Ω eX eY hf N))
    (weilGeometricBaseChangeComparison Ω ℓ X N eX.hom)
    (weilGeometricBaseChangeComparison Ω ℓ Y N eY.hom)
    (geometricBaseChangePullbackComparison_cube ℓ Ω eX eY N _ _)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ((geometricBaseChange k Ω).map f))
    _ _ (weilLowerShriekComparison_exchangeCompatible ℓ eX eY hf)
    (weilLowerShriekFrobeniusComparison_exchangeCompatible ℓ Ω eX eY hf N) K
  unfold weilGeometricBaseChange weilLowerShriek weilLowerShriekOfFrobenius
  convert hc using 3

end AlgebraicGeometry.ProEtale.CondensedRing
