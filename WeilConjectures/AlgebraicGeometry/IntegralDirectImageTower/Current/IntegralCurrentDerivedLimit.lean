/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Cochain.CochainHomotopyComparison
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # The normalized derived limit for current reduction data

The ordinary and derived proofs are reused from the existing limit modules,
specialized to the construction-only current interface.
Source: integral direct-image proof (2), total inverse limit after restriction.
(blueprint: lem-sp-current-derived-limit-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev scalar (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :=
  (s.towers T).scalar (spIntegralReductionScalar l E T (s.reduction T).coefficient n)

private abbrev restrictionIso (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :
    spCompletedEllRestriction l E T n ⋙ completedRestriction l E s T ≅
      restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (spIntegralReductionScalar l E T (s.reduction T).coefficient n)) :=
  systemScalarRestrictionComposition.{u + 1, u, u + 1}
    (s.reduction T).coefficient.hom (spCompletedEllCommProjection l E T n)
    (spIntegralReductionScalar l E T (s.reduction T).coefficient n) rfl

private theorem restrictedTower_succ (s : Coefficients l E) (T : Scheme.{u})
    (C : spCoefficientTowers l E T) (n : ℕ) :
    ((restrictedTower l E s T).obj C).map (homOfLE (Nat.le_succ n)).op =
      (completedRestriction l E s T).map
        ((spCompletedTransition l E T (s.towers T) n).app C) := by
  change ((Functor.ofOpSequence
    (X := fun n : ℕ ↦ spCompletedEvaluation l E T (s.towers T) n ⋙
      completedRestriction l E s T)
    (fun n ↦ Functor.whiskerRight (spCompletedTransition l E T (s.towers T) n)
      (completedRestriction l E s T))).map (homOfLE (Nat.le_succ n)).op).app C = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private theorem restrictedTower_map (s : Coefficients l E) (T : Scheme.{u})
    (C : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (x : (((restrictedTower l E s T).obj C).obj (op n)).val.obj U) :
    (((restrictedTower l E s T).obj C).map (homOfLE h).op).val.app U x =
      (((s.towers T).equivalence.functor.obj C).transition h).val.app U x := by
  induction n, h using Nat.le_induction with
  | base =>
      simpa using (((s.towers T).equivalence.functor.obj C).identity m U x).symm
  | succ n h ih =>
      rw [← homOfLE_comp h (Nat.le_succ n), op_comp, Functor.map_comp]
      rw [restrictedTower_succ]
      change (((restrictedTower l E s T).obj C).map (homOfLE h).op).val.app U
        (((spCompletedTransition l E T (s.towers T) n).app C).val.app U x) = _
      have ht := (spCompletedTransition_existsUnique l E T (s.towers T) n).exists.choose_spec C U x
      exact (congrArg
        (fun y ↦ (((restrictedTower l E s T).obj C).map (homOfLE h).op).val.app U y)
        ht).trans ((ih _).trans
          (((s.towers T).equivalence.functor.obj C).compose h (Nat.le_succ n) U x).symm)

private def family (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : (s.reduction T).ordinary.obj P ⟶ C) (n : ℕ) :
    P ⟶ ((restrictedTower l E s T).obj C).obj (op n) :=
  (scalar l E s T n).ordinaryAdj.homEquiv _ _
    (((s.reduction T).level n).inv.app P ≫
      ((s.towers T).equivalence.functor.map f).app n) ≫
    (restrictionIso l E s T n).inv.app _

private theorem family_apply (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : (s.reduction T).ordinary.obj P ⟶ C) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : P.val.obj U) :
    (family l E s T f n).val.app U x =
      (((s.towers T).equivalence.functor.map f).app n).val.app U
        (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
          (s.reduction T).ordinary (s.reduction T).level P n U 1 x) := by
  rw [family, Adjunction.homEquiv_unit]
  change (((s.towers T).equivalence.functor.map f).app n).val.app U
    ((((s.reduction T).level n).inv.app P).val.app U
      (((scalar l E s T n).ordinaryAdj.unit.app P).val.app U x)) = _
  rw [(scalar l E s T n).unit_normalized]
  rfl

private theorem family_compatible (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : (s.reduction T).ordinary.obj P ⟶ C) (n : ℕ) :
    family l E s T f (n + 1) ≫
      ((restrictedTower l E s T).obj C).map (homOfLE (Nat.le_succ n)).op =
      family l E s T f n := by
  rw [restrictedTower_succ]
  ext U x
  change (((spCompletedTransition l E T (s.towers T) n).app C).val.app U)
    ((family l E s T f (n + 1)).val.app U x) = _
  refine ((spCompletedTransition_existsUnique l E T (s.towers T) n).exists.choose_spec C U
    ((family l E s T f (n + 1)).val.app U x)).trans ?_
  rw [family_apply, family_apply]
  have h := congrArg (fun a ↦ a.val.app U
    (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
      (s.reduction T).ordinary (s.reduction T).level P (n + 1) U 1 x))
    (((s.towers T).equivalence.functor.map f).comm (Nat.le_succ n))
  change (((s.towers T).equivalence.functor.obj C).transition (Nat.le_succ n)).val.app U
      ((((s.towers T).equivalence.functor.map f).app (n + 1)).val.app U
        (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
          (s.reduction T).ordinary (s.reduction T).level P (n + 1) U 1 x)) =
    ((((s.towers T).equivalence.functor.map f).app n).val.app U)
      (spStrictTransitionSection T (spCoefficientCommRings l E T)
        ((s.towers T).equivalence.functor.obj ((s.reduction T).ordinary.obj P))
        (Nat.le_succ n) U
        (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
          (s.reduction T).ordinary (s.reduction T).level P (n + 1) U 1 x)) at h
  rw [(s.reduction T).transition, map_one] at h
  exact h

private def familyCone (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : (s.reduction T).ordinary.obj P ⟶ C) : Cone ((restrictedTower l E s T).obj C) where
  pt := P
  π := NatTrans.ofOpSequence (family l E s T f) (by
    intro n
    simpa using (family_compatible l E s T f n).symm)

private def transpose (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : (s.reduction T).ordinary.obj P ⟶ C) : P ⟶ (ordinaryLimit l E s T).obj C :=
  limit.lift _ (familyCone l E s T f)

private theorem transpose_projection (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : (s.reduction T).ordinary.obj P ⟶ C) (n : ℕ) :
    transpose l E s T f ≫ ordinaryProjection l E s T C n = family l E s T f n :=
  limit.lift_π _ _

private def untransposeLevel (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (h : P ⟶ (ordinaryLimit l E s T).obj C) (n : ℕ) :
    ((s.towers T).equivalence.functor.obj ((s.reduction T).ordinary.obj P)).level n ⟶
      ((s.towers T).equivalence.functor.obj C).level n :=
  ((s.reduction T).level n).hom.app P ≫
    ((scalar l E s T n).ordinaryAdj.homEquiv _ _).symm
      (h ≫ ordinaryProjection l E s T C n ≫ (restrictionIso l E s T n).hom.app _)

private theorem untransposeLevel_generator (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (h : P ⟶ (ordinaryLimit l E s T).obj C) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : P.val.obj U) :
    (untransposeLevel l E s T h n).val.app U
      (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level P n U 1 x) =
      (ordinaryProjection l E s T C n).val.app U (h.val.app U x) := by
  have hi := congrArg (fun a ↦ a.val.app U
    (systemModelTmul (scalar l E s T n).model P U 1 x))
    (((s.reduction T).level n).inv_hom_id_app P)
  dsimp only [spReductionGenerator, untransposeLevel]
  change (((scalar l E s T n).ordinaryAdj.homEquiv _ _).symm _).val.app U
    ((((s.reduction T).level n).hom.app P).val.app U
      ((((s.reduction T).level n).inv.app P).val.app U _)) = _
  change (((((s.reduction T).level n).hom.app P).val.app U)
    ((((s.reduction T).level n).inv.app P).val.app U
      (systemModelTmul (scalar l E s T n).model P U 1 x))) =
        systemModelTmul (scalar l E s T n).model P U 1 x at hi
  rw [hi, systemScalarModel_transpose_tmul (scalar l E s T n),
    Equiv.apply_symm_apply, one_smul]
  rfl

private def untransposeStrict (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (h : P ⟶ (ordinaryLimit l E s T).obj C) :
    (s.towers T).equivalence.functor.obj ((s.reduction T).ordinary.obj P) ⟶
      (s.towers T).equivalence.functor.obj C where
  app := untransposeLevel l E s T h
  comm {m n} k := by
    apply (cancel_epi (((s.reduction T).level n).inv.app P)).1
    apply systemScalarModel_hom_ext (scalar l E s T n)
    intro U x
    change (((s.towers T).equivalence.functor.obj C).transition k).val.app U
      ((untransposeLevel l E s T h n).val.app U
        (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
          (s.reduction T).ordinary (s.reduction T).level P n U 1 x)) =
      (untransposeLevel l E s T h m).val.app U
        (spStrictTransitionSection T (spCoefficientCommRings l E T)
          ((s.towers T).equivalence.functor.obj ((s.reduction T).ordinary.obj P)) k U
          (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
            (s.reduction T).ordinary (s.reduction T).level P n U 1 x))
    rw [(s.reduction T).transition, map_one,
      untransposeLevel_generator, untransposeLevel_generator]
    have hw := congrArg (fun a ↦ a.val.app U (h.val.app U x))
      (limit.w ((restrictedTower l E s T).obj C) (homOfLE k).op)
    change (ordinaryProjection l E s T C n ≫
      ((restrictedTower l E s T).obj C).map (homOfLE k).op).val.app U
      (h.val.app U x) = _ at hw
    change (((restrictedTower l E s T).obj C).map (homOfLE k).op).val.app U
      ((ordinaryProjection l E s T C n).val.app U (h.val.app U x)) = _ at hw
    rw [restrictedTower_map] at hw
    exact hw

private def untranspose (s : Coefficients l E) (T : Scheme.{u})
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (h : P ⟶ (ordinaryLimit l E s T).obj C) : (s.reduction T).ordinary.obj P ⟶ C :=
  (s.towers T).equivalence.functor.preimage (untransposeStrict l E s T h)

private def ordinaryHomEquiv (s : Coefficients l E) (T : Scheme.{u})
    (P : spIntegralSectionModules l E T) (C : spCoefficientTowers l E T) :
    ((s.reduction T).ordinary.obj P ⟶ C) ≃ (P ⟶ (ordinaryLimit l E s T).obj C) where
  toFun := transpose l E s T
  invFun := untranspose l E s T
  left_inv f := by
    apply (s.towers T).equivalence.functor.map_injective
    rw [untranspose, Functor.map_preimage]
    apply strict_ext l E T
    intro n
    apply (cancel_epi (((s.reduction T).level n).inv.app P)).1
    apply systemScalarModel_hom_ext (scalar l E s T n)
    intro U x
    change (untransposeLevel l E s T (transpose l E s T f) n).val.app U
      (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level P n U 1 x) = _
    rw [untransposeLevel_generator]
    have ht := congrArg (fun a ↦ a.val.app U x) (transpose_projection l E s T f n)
    change (ordinaryProjection l E s T C n).val.app U
      ((transpose l E s T f).val.app U x) = _ at ht
    rw [family_apply] at ht
    exact ht
  right_inv h := by
    apply limit.hom_ext (F := (restrictedTower l E s T).obj C)
    intro n
    change transpose l E s T (untranspose l E s T h) ≫
      ordinaryProjection l E s T C n.unop = h ≫ ordinaryProjection l E s T C n.unop
    rw [transpose_projection]
    ext U x
    rw [family_apply]
    dsimp only [untranspose]
    rw [Functor.map_preimage]
    change (untransposeLevel l E s T h n.unop).val.app U
      (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level P n.unop U 1 x) = _
    exact untransposeLevel_generator l E s T h n.unop U x

private theorem reduction_map_generator (s : Coefficients l E) (T : Scheme.{u})
    {P Q : spIntegralSectionModules l E T} (f : P ⟶ Q) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : P.val.obj U) :
    ((((s.towers T).equivalence.functor.map ((s.reduction T).ordinary.map f)).app n).val.app U)
      (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level P n U 1 x) =
      spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level Q n U 1 (f.val.app U x) := by
  have hn := congrArg (fun a ↦ a.val.app U
    (systemModelTmul (scalar l E s T n).model P U 1 x))
    (((s.reduction T).level n).inv.naturality f)
  change (((s.reduction T).level n).inv.app Q).val.app U
    (((scalar l E s T n).model.E.map f).val.app U
      (systemModelTmul (scalar l E s T n).model P U 1 x)) = _ at hn
  rw [systemScalarModel_map_tmul (scalar l E s T n)] at hn
  exact hn.symm

private def ordinaryAdjunction (s : Coefficients l E) (T : Scheme.{u}) :
    (s.reduction T).ordinary ⊣ ordinaryLimit l E s T :=
  Adjunction.mkOfHomEquiv {
    homEquiv := ordinaryHomEquiv l E s T
    homEquiv_naturality_left_symm := by
      intro P Q C f h
      change untranspose l E s T (f ≫ h) =
        (s.reduction T).ordinary.map f ≫ untranspose l E s T h
      apply (s.towers T).equivalence.functor.map_injective
      rw [untranspose, Functor.map_preimage, Functor.map_comp, untranspose,
        Functor.map_preimage]
      apply strict_ext l E T
      intro n
      apply (cancel_epi (((s.reduction T).level n).inv.app P)).1
      apply systemScalarModel_hom_ext (scalar l E s T n)
      intro U x
      change (untransposeLevel l E s T (f ≫ h) n).val.app U
        (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
          (s.reduction T).ordinary (s.reduction T).level P n U 1 x) =
        (untransposeLevel l E s T h n).val.app U
          (((((s.towers T).equivalence.functor.map
            ((s.reduction T).ordinary.map f)).app n).val.app U)
            (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
              (s.reduction T).ordinary (s.reduction T).level P n U 1 x))
      rw [reduction_map_generator, untransposeLevel_generator, untransposeLevel_generator]
      rfl
    homEquiv_naturality_right := by
      intro P C D f g
      apply limit.hom_ext (F := (restrictedTower l E s T).obj D)
      intro n
      change transpose l E s T (f ≫ g) ≫ ordinaryProjection l E s T D n.unop =
        (transpose l E s T f ≫ (ordinaryLimit l E s T).map g) ≫
          ordinaryProjection l E s T D n.unop
      have hn : (ordinaryLimit l E s T).map g ≫
          ordinaryProjection l E s T D n.unop =
          ordinaryProjection l E s T C n.unop ≫
            (((restrictedTower l E s T).map g).app n) :=
        limMap_π _ n
      rw [transpose_projection, Category.assoc, hn, ← Category.assoc,
        transpose_projection]
      ext U x
      change (family l E s T (f ≫ g) n.unop).val.app U x =
        (((s.towers T).equivalence.functor.map g).app n.unop).val.app U
          ((family l E s T f n.unop).val.app U x)
      rw [family_apply, family_apply, (s.towers T).equivalence.functor.map_comp]
      rfl }

/-- Ordinary strict reduction is left adjoint to the inverse limit after restriction
of each quotient's scalar action, with unit given by one tensor the section.
Source: Stacks 03D7 and 0940; blueprint integral direct-image proof paragraph (2).
Proof: use the recorded level isomorphisms and normalized scalar adjunctions to
transpose every level of a strict tower map. The quotient-generator transition
formula makes these transposes a cone. The limit universal property gives a map
to the restricted limit. Conversely, transpose each limit projection and transport
back through the level isomorphisms. Tensor generation and compatibility of the
limit projections show that these maps form a strict tower morphism. The scalar
Hom equivalences and limit extensionality prove the two inverse identities and
naturality. At the identity tower map the transpose is the adjunction unit, and
its projections evaluate the scalar unit, giving exactly the stated normalization.
(blueprint: lem-sp-current-derived-limit-existence). -/
theorem ordinary_limit_adjunction (s : Coefficients l E) (T : Scheme.{u}) :
    ∃ adj : (s.reduction T).ordinary ⊣ ordinaryLimit l E s T,
      IsOrdinaryAdjunctionNormalized l E s T adj := by
  refine ⟨ordinaryAdjunction l E s T, ?_⟩
  intro P n U x
  change (ordinaryProjection l E s T ((s.reduction T).ordinary.obj P) n).val.app U
    ((transpose l E s T (𝟙 ((s.reduction T).ordinary.obj P))).val.app U x) = _
  have ht := congrArg (fun a ↦ a.val.app U x)
    (transpose_projection l E s T (𝟙 ((s.reduction T).ordinary.obj P)) n)
  change (ordinaryProjection l E s T ((s.reduction T).ordinary.obj P) n).val.app U
    ((transpose l E s T (𝟙 ((s.reduction T).ordinary.obj P))).val.app U x) = _ at ht
  rw [family_apply] at ht
  rw [(s.towers T).equivalence.functor.map_id] at ht
  change (ordinaryProjection l E s T ((s.reduction T).ordinary.obj P) n).val.app U
    ((transpose l E s T (𝟙 ((s.reduction T).ordinary.obj P))).val.app U x) =
      spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level P n U 1 x at ht
  exact ht


/-- Derive a normalized ordinary reduction/limit adjunction using K-flat and K-injective
resolutions. Source: Stacks 09T5, 06YS and 07A6.
Proof: K-flat resolutions form a left resolving class. The fixed reduction counit is
invertible on this class, so its naturality proves that ordinary reduction inverts
quasi-isomorphisms between its objects. K-injective resolutions of the Grothendieck
category of strict towers construct the right derived limit. The resolving-class
adjunction theorem then gives the derived adjunction and its formula on every chain
map, with precisely the fixed counit. Ordinary normalization is retained unchanged.
(blueprint: lem-sp-current-derived-limit-existence). -/
theorem limit_of_normalized_ordinary_adjunction (s : Coefficients l E) (T : Scheme.{u})
    (adj : (s.reduction T).ordinary ⊣ ordinaryLimit l E s T)
    (hnorm : IsOrdinaryAdjunctionNormalized l E s T adj) :
    Nonempty (DerivedLimit l E s T) := by
  letI := (s.towers T).hasDerived
  letI := (s.towers T).grothendieck
  letI : Abelian.HasKInjectiveResolutions (spCoefficientTowers l E T) := inferInstance
  letI : (ordinaryLimit l E s T).Additive := adj.right_adjoint_additive
  let G := (s.reduction T).ordinary
  let q := HomotopyCategory.quotient (spIntegralSectionModules l E T) (.up ℤ)
  let P : Set (HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ)) :=
    fun X ↦ ∃ K : CochainComplex (spIntegralSectionModules l E T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) K ∧
        q.obj K = X
  have hres : ∀ X : HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ),
      ∃ (X' : HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ)) (f : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso (spIntegralSectionModules l E T) (.up ℤ) f := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := spIntegralSectionRing l E T) K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  obtain ⟨εh, hεh, hεapp⟩ := exists_homotopy_leftDerived_comparison G
    (s.reduction T).red (s.reduction T).counit (s.reduction T).universal
  have hinv : ∀ X Y (f : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso (spIntegralSectionModules l E T) (.up ℤ) f →
      IsIso ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map f) := by
    rintro X Y f ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hf
    obtain ⟨f, rfl⟩ := q.map_surjective f
    have : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hf
    have : IsIso (εh.app (q.obj K)) := by
      rw [hεapp]
      exact (s.reduction T).computes K hK
    have : IsIso (εh.app (q.obj L)) := by
      rw [hεapp]
      exact (s.reduction T).computes L hL
    have : IsIso ((DerivedCategory.Qh ⋙ (s.reduction T).red).map (q.map f)) := by
      change IsIso ((s.reduction T).red.map (DerivedCategory.Q.map f))
      infer_instance
    exact IsIso.of_isIso_fac_left (εh.naturality (q.map f)).symm
  obtain ⟨R, η, hR, hη⟩ := CategoryTheory.exists_derived (ordinaryLimit l E s T)
  obtain ⟨d, hd⟩ := derivedAdjunctionOfResolvingClass G (ordinaryLimit l E s T) adj
    P hres hinv (s.reduction T).red εh hεh R η hR
  refine ⟨{
    ordinaryAdjunction := adj
    ordinary_normalization := hnorm
    derived := R
    unit := η
    universal := hR
    computes := hη
    adjunction := d
    normalization := ?_ }⟩
  intro K I f
  rw [← hεapp K]
  exact hd K I f


/-- The specified total derived restricted limit exists for each current construction.
Proof: first construct its ordinary tensor/limit adjunction using compatible quotient
transposes, and then derive that same adjunction on K-flat and K-injective resolutions.
The ordinary generator and derived representative normalizations are retained.
Source: blueprint integral direct-image proof (2).
(blueprint: lem-sp-current-derived-limit-existence). -/
theorem derived_limit_exists (s : Coefficients l E) (T : Scheme.{u}) :
    Nonempty (DerivedLimit l E s T) := by
  obtain ⟨adj, hnorm⟩ := ordinary_limit_adjunction l E s T
  exact limit_of_normalized_ordinary_adjunction l E s T adj hnorm

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
