/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.Paper.IntegralOperationsScalarExtension
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus

import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.CompactSupportRoosCofinality
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.DerivedCompleteKoszulReconstruction
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.IntegralScalarExtensionUniverses
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.WeilCompletedTensorReflector
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized

/-! # Normalized integral scalar comparisons

Source: blueprint sec-smooth-purity/sk-def-sf-operations, integral/common-stage paragraph;
Stacks Tags 07A4, 08J9, 099N
(blueprint: lem-pur-integral-operations-scalar-extension).

The representative maps below fix the comparisons before any common-stage descent.
They use arbitrary finite extensions between the small coefficient models, independently
of the universe containing the algebraic closure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

/-- The boundary of the actual Roos cocone, for use in both coordinate formulas.
Source: Stacks 08TC (blueprint: lem-pur-integral-operations-scalar-extension). -/
abbrev scalarRoosBoundary {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
    (integralOperationsTowerStep C)

section ScalarRoos

open CochainComplex CochainComplex.HomComplex

private theorem scalarCocone_relation
    {A : Type a} [Category.{b} A] [Abelian A]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    δ (-1) 0 (mappingCocone.snd φ) + Cochain.ofHom (mappingCocone.fst φ ≫ φ) = 0 := by
  simp only [mappingCocone.snd, Cochain.δ_leftShift (mappingCone.snd φ) (-1) (-1) 0 rfl 1 rfl,
    mappingCone.δ_snd]
  simp [mappingCocone.fst, Cochain.leftShift_neg,
    Cochain.leftShift_comp_zero_cochain, Cochain.ofHom_comp]


private def scalarAdditiveCoconeMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {B : Type a'} [Category.{b'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (mappingCocone φ) ⟶
      mappingCocone ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  refine mappingCocone.lift (G.map φ) (G.map (mappingCocone.fst φ))
    ((mappingCocone.snd φ).map F) ?_
  have h := congrArg (fun z ↦ z.map F) (scalarCocone_relation φ)
  simpa only [Cochain.map_add, Cochain.map_zero, Cochain.map_ofHom, ← δ_map,
    Functor.map_comp] using h


private def scalarCoconeSquareMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {K L K' L' : CochainComplex A ℤ} (φ : K ⟶ L) (ψ : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (w : φ ≫ b = a ≫ ψ) :
    mappingCocone φ ⟶ mappingCocone ψ := by
  refine mappingCocone.lift ψ (mappingCocone.fst φ ≫ a)
    ((mappingCocone.snd φ).comp (Cochain.ofHom b) (add_zero _)) ?_
  have hδ : δ (-1) 0 (mappingCocone.snd φ) =
      -Cochain.ofHom (mappingCocone.fst φ ≫ φ) := eq_neg_of_add_eq_zero_left
        (scalarCocone_relation φ)
  rw [δ_comp_ofHom, hδ]
  simp only [Cochain.neg_comp, ← Cochain.ofHom_comp]
  rw [Category.assoc, w, ← Category.assoc, neg_add_cancel]

/-- An additive functor maps the Roos cocone to the Roos cocone of its tower.
Both coordinates, including the shifted coordinate, are prescribed, so no cone
completion is chosen. Source: Stacks 08TC
(blueprint: lem-pur-integral-operations-scalar-extension).
Proof: apply the functor to the two cone coordinates. The universal property of each
product gives the specified maps to the target products. Additivity preserves 1-s and
the signed cocone differential, so these coordinates define a chain map. The cocone's
biproduct coordinates and joint monicity of the product projections give uniqueness. -/
theorem scalarRoosMap_existsUnique
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    ∃! α : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)),
      (∀ n : ℕ, α ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
          Pi.π (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.obj (op n))) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
            Pi.π (fun n ↦ C.obj (op n)) n)) ∧
      (∀ (i j : ℤ) (h : i + -1 = j) (n : ℕ), α.f i ≫
          (CochainComplex.mappingCocone.snd
            (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)))).v i j h ≫
          (Pi.π (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (C.obj (op n))) n).f j =
        F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i j h ≫
          (Pi.π (fun n ↦ C.obj (op n)) n).f j)) := by
  dsimp only [integralOperationsRoos]
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let pc : G.obj (∏ᶜ (fun n ↦ C.obj (op n))) ⟶
      ∏ᶜ (fun n ↦ G.obj (C.obj (op n))) :=
    Pi.lift (fun n ↦ G.map (Pi.π (fun n ↦ C.obj (op n)) n))
  have w : G.map (scalarRoosBoundary C) ≫ pc =
      pc ≫ scalarRoosBoundary (C ⋙ G) := by
    apply Pi.hom_ext
    intro n
    have hC := (towerTransitionEndomorphism_eq_iff
      (integralOperationsTowerStep C) (scalarRoosBoundary C)).mp rfl n
    have hG := (towerTransitionEndomorphism_eq_iff
      (integralOperationsTowerStep (C ⋙ G)) (scalarRoosBoundary (C ⋙ G))).mp rfl n
    simp only [Category.assoc]
    rw [show pc ≫ Pi.π _ n = G.map (Pi.π _ n) from Pi.lift_π _ n,
      ← G.map_comp, hC, G.map_sub, G.map_comp]
    dsimp only [Functor.comp_obj] at hG
    erw [hG]
    simp only [Preadditive.comp_sub, ← Category.assoc, pc, Pi.lift_π]
    rfl
  let α := scalarAdditiveCoconeMap F (scalarRoosBoundary C) ≫
    scalarCoconeSquareMap (G.map (scalarRoosBoundary C)) (scalarRoosBoundary (C ⋙ G)) pc pc w
  have hα : (∀ n : ℕ, α ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
          Pi.π (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.obj (op n))) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
            Pi.π (fun n ↦ C.obj (op n)) n)) ∧
      (∀ (i j : ℤ) (h : i + -1 = j) (n : ℕ), α.f i ≫
          (CochainComplex.mappingCocone.snd
            (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)))).v i j h ≫
          (Pi.π (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (C.obj (op n))) n).f j =
        F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i j h ≫
          (Pi.π (fun n ↦ C.obj (op n)) n).f j)) := by
    constructor
    · intro n
      dsimp only [α, scalarAdditiveCoconeMap, scalarCoconeSquareMap, G]
      simp only [Category.assoc, mappingCocone.lift_fst_assoc]
      change _ ≫ pc ≫ Pi.π _ n = _
      rw [show pc ≫ Pi.π _ n = G.map (Pi.π _ n) from Pi.lift_π _ n]
      exact (G.map_comp _ _).symm
    · intro i j h n
      dsimp only [α, scalarAdditiveCoconeMap, scalarCoconeSquareMap, G]
      simp only [HomologicalComplex.comp_f, Category.assoc,
        mappingCocone.lift_f_snd_v_assoc]
      rw [Cochain.comp_v _ _ (add_zero (-1)) i j j h (add_zero j)]
      simp only [Cochain.ofHom_v, Category.assoc]
      rw [mappingCocone.lift_f_snd_v_assoc]
      simp only [Cochain.map_v]
      have hpc := congrArg (fun z ↦ z.f j)
        (show pc ≫ Pi.π _ n = G.map (Pi.π _ n) from Pi.lift_π _ n)
      change pc.f j ≫ (Pi.π (fun n ↦ G.obj (C.obj (op n))) n).f j =
          F.map ((Pi.π (fun n ↦ C.obj (op n)) n).f j) at hpc
      rw [hpc, ← F.map_comp]
  refine ⟨α, hα, ?_⟩
  intro β hβ
  have hf : β ≫ mappingCocone.fst (scalarRoosBoundary (C ⋙ G)) =
      α ≫ mappingCocone.fst (scalarRoosBoundary (C ⋙ G)) := by
    apply Pi.hom_ext
    intro n
    simpa only [Category.assoc] using! (hβ.1 n).trans (hα.1 n).symm
  have hs (i j : ℤ) (h : i + -1 = j) :
      β.f i ≫ (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i j h =
        α.f i ≫ (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i j h := by
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval B (ComplexShape.up ℤ) j)
      (fun n ↦ G.obj (C.obj (op n)))).hom_ext
    rintro ⟨n⟩
    simpa only [Category.assoc] using! (hβ.2 i j h n).trans (hα.2 i j h n).symm
  ext i
  have hfi := congrArg (fun z ↦ z.f i) hf
  change β.f i ≫ _ = α.f i ≫ _ at hfi
  have hid := mappingCocone.id_X (scalarRoosBoundary (C ⋙ G)) i (i - 1) (by omega)
  have hβid := congrArg (fun z ↦ β.f i ≫ z) hid
  have hαid := congrArg (fun z ↦ α.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc, Category.comp_id] at hβid hαid
  rw [hfi, hs i (i - 1) (by omega)] at hβid
  exact (Category.comp_id (β.f i)).symm.trans (hβid.symm.trans hαid)

end ScalarRoos


/-- The Roos map with its two prescribed coordinates.
Source: Stacks 08TC (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarRoosMap
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  (scalarRoosMap_existsUnique F C).exists.choose

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Scalar extension of a finite pullback level, before taking the Roos complex.
Source: Stacks 07A4, 099N (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: on the displayed generators send 1 tensor f-star(1 tensor x) to
f-star(1 tensor (1 tensor x)). Extend by the target completed-ring action. The
canonical constant-section ring map makes this balanced. Kan extension and
sheafification give a unique sheaf map. It commutes with the differential and is
natural in P since the generator formula commutes with every chain map. -/
theorem scalarPullbackLevel_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! α : integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
        (x : (P.X i).val.obj (op V)),
        ((α.app P).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X
            (((integralOperationsPullbackLevel l E f n).obj P).X i)
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator l E f n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator l L f n
          (((unrestrictedIntegralFiniteComplex l L Y n).obj
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i) V
          (unrestrictedIntegralTensorSection l L Y n
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x)) := by
  sorry

/-- The generator-normalized finite-level scalar pullback map.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarPullbackLevel {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose

/-- The level maps form the strict tower map; the component equations retain all
reduction maps, rather than choosing a map between unrelated limits.
Source: Stacks 07A4, 08TC (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the two composites with each consecutive reduction have the same generator
formula. Uniqueness of the level maps proves the consecutive squares, and induction
proves all tower squares. Naturality in P is componentwise. This constructs the tower
transformation, and the component equations give uniqueness. -/
theorem scalarPullbackTower_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralOperationsPullbackTowerFunctor l E f ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackTowerFunctor l L f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ),
        (α.app P).app (op n) = (scalarPullbackLevel l E L ι f n).app P := by
  sorry

/-- The strict scalar pullback tower map.
Source: Stacks 08TC (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarPullbackTower {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :=
  (scalarPullbackTower_existsUnique l E L ι f).exists.choose

/-- The chain comparison is the diagonal Roos map of the prescribed tower map.
Source: Stacks 07A4, 08TC (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarPullbackChain {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((integralOperationsPullbackComplexFunctor l E f).obj P) ⟶
      (integralOperationsPullbackComplexFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  scalarRoosMap (integralOrdinaryScalar l E L ι X)
      ((integralOperationsPullbackTowerFunctor l E f).obj P) ≫
    integralOperationsRoosMap ((scalarPullbackTower l E L ι f).app P)


/-- Scalar extension of each finite tensor level is fixed on total tensor generators.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: send 1 tensor ((1 tensor x) tensor (1 tensor y)) to
(1 tensor (1 tensor x)) tensor (1 tensor (1 tensor y)), and extend by the target
completed scalar action. Balance follows from the coefficient quotient map. This
commutes with restrictions and both signed differentials, so extends uniquely
through sheafification and the direct-sum totalization. -/
theorem scalarTensorLevel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    ∃! α : integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U 1
            (integralOperationsTotalTensorSection l E W n P Q p q U
              (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
              (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
        integralOperationsTotalTensorSection l L W n
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q U
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (P.X p)) U 1
            (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x))
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (Q.X q)) U 1
            (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)) := by
  sorry

/-- The normalized finite tensor level map.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorLevel (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :=
  (scalarTensorLevel_existsUnique l E L ι W n).exists.choose

/-- The tensor level maps respect the specified strict reductions.
Source: Stacks 08TC (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: both consecutive composites send a total tensor generator to the reduction
of its two entries. The uniqueness of scalarTensorLevel identifies those composites.
Iterate consecutive squares for every tower arrow; naturality is componentwise.
The component equations determine the transformation uniquely. -/
theorem scalarTensorTower_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralOperationsTensorTowerFunctor l E W ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorTowerFunctor l L W,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ),
        (α.app (P, Q)).app (op n) = (scalarTensorLevel l E L ι W n).app (P, Q) := by
  sorry

/-- The strict scalar tensor tower map.
Source: Stacks 08TC (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorTower (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarTensorTower_existsUnique l E L ι W).exists.choose

/-- The tensor chain map is the diagonal Roos map of that strict tower map.
Source: Stacks 07A4, 08TC (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorChain (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((integralOperationsTensorComplexFunctor l E W).obj (P, Q)) ⟶
      (integralOperationsTensorComplexFunctor l L W).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)) :=
  scalarRoosMap (integralOrdinaryScalar l E L ι W)
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) ≫
    integralOperationsRoosMap ((scalarTensorTower l E L ι W).app (P, Q))

/-- Finite free ordinary coefficient extension preserves the good representatives.
Source: Stacks 06YU, 07A4 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the object and morphism formulas of integralOrdinaryScalarWitness give
an isomorphism with the concrete changeOfRingsComplex. Convert flatness on the site
to exactness of tensorRight and apply changeOfRings_isKFlat_of_flat_terms. Tensoring
the comparison isomorphism transports K-flatness; its degree components transport
flatness. This general change-of-rings argument needs no finite-free basis and
imposes no equality of site object and arrow sizes. -/
theorem scalarGood (W : AlgebraicGeometry.Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    integralOperationsGoodComplex l L W
      (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P.obj) := by
  let : EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0} _
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  let S := completedIntegralCommRingSheafUnrestricted.{u, u} l L W
  let φ := integralCompletedScalarMap l E L ι W
  let F := integralOrdinaryScalar l E L ι W
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u+1, u, u+1} R
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u+1, u, u+1} S
  let : MonoidalCategory (integralTowerModules l E W) :=
    SheafOfModules.monoidalCategory.{u, u+1, u+1} R
  let : MonoidalCategory (integralTowerModules l L W) :=
    SheafOfModules.monoidalCategory.{u, u+1, u+1} S
  have ho := (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
  let e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.obj ≅
      SheafOfModules.changeOfRingsComplex.{u+1, u} φ P.obj :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (ho (P.obj.X i))) (by
      intro i j hij
      symm
      change F.map (P.obj.d i j) ≫ eqToHom (ho (P.obj.X j)) =
        eqToHom (ho (P.obj.X i)) ≫
          SheafOfModules.changeOfRingsHom φ (P.obj.X i) (P.obj.d i j)
      erw [(integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose
        (P.obj.d i j)]
      simp
      rfl)
  have hflat (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory.{u, u+1, u+1} R) (P.obj.X i)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u+1, u, u+1} R (P.obj.X i))
      (P.property.2 i)
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms.{u+1, u}
    φ P.obj P.property.1 hflat
  constructor
  · let : (MonoidalCategory.curriedTensor
        (integralTowerModules l L W)).PreservesZeroMorphisms :=
      SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
    let : ∀ M : integralTowerModules l L W,
        ((MonoidalCategory.curriedTensor _).obj M).PreservesZeroMorphisms :=
      SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
    intro A hA i
    let T := ((MonoidalCategory.curriedTensor
      (integralTowerModules l L W)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)).obj A
    exact (h.1 A hA i).of_iso (T.mapIso e).symm
  · intro i
    let ei := (HomologicalComplex.eval _ _ i).mapIso e
    have hi := (exactFunctor _ _).prop_of_iso
      ((MonoidalCategory.curriedTensor (integralTowerModules l L W)).flip.mapIso ei).symm
      (h.2 i)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u+1, u, u+1} S
        (((F.mapHomologicalComplex (.up ℤ)).obj P.obj).X i)).symm hi

/-- The ordinary scalar/pullback comparison is the localization of scalarPullbackChain.
Source: Stacks 07A4, 099N (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the prescribed level generator maps are natural and commute with strict
reductions. The two Roos coordinates therefore give scalarPullbackChain. Finite
freeness commutes with countable products; cofinality of uniformizer filtrations
makes this chain map a quasi-isomorphism on good representatives. Localize the
map, conjugating by the two displayed representative comparisons. Good K-flat
resolutions compute all objects and roofs, giving naturality and invertibility.
The same localization property gives uniqueness with this normalization. -/
theorem scalarPullbackOrdinary_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι X).map
            ((integralDerivedPullbackComparison l E f).hom.app P) ≫
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
            ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
          DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (integralDerivedPullback l L f).map
            ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
          (integralDerivedPullbackComparison l L f).hom.app
            ⟨_, scalarGood l E L ι Y P⟩ := by
  sorry

/-- The canonical localized scalar/pullback comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarPullbackOrdinary {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :=
  (scalarPullbackOrdinary_existsUnique l E L ι f).exists.choose

/-- The ordinary scalar/completed-tensor comparison has its full Roos normalization.
Source: Stacks 07A4, 099N (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the finite tensor generator maps respect the signed total differential and
strict reductions. Their diagonal Roos map is scalarTensorChain. Finite freeness
commutes with its products, and the two uniformizer filtrations are cofinal. Thus
this map is a quasi-isomorphism on good pairs. Localize in both variables and
conjugate by the displayed comparisons. Roofs prove naturality and independence;
the universal property of the localization gives uniqueness. -/
theorem scalarTensorOrdinary_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W,
      ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l L W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l L W).hom.app
            (⟨_, scalarGood l E L ι W P⟩, ⟨_, scalarGood l E L ι W Q⟩) := by
  sorry

/-- The canonical localized scalar/completed-tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorOrdinary (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarTensorOrdinary_existsUnique l E L ι W).exists.choose

/-- The ordinary-to-completed scalar map is fixed on every good complex.
Source: Bhatt--Scholze 3.5.1 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the already prescribed integralScalarCompletionChain has the quotient tensor
projection as its unshifted coordinate and zero shifted coordinate. Localize that
chain map using the scalar representative comparisons. Good resolutions compute
all objects and roofs, so the localization gives exactly one natural transformation.
The finite free basis commutes with the Roos products; on a complete input the
completion unit is invertible, which proves the second assertion. -/
theorem scalarCompletion_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W,
      (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι W).hom.app P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj)) ∧
      (∀ K, IsSfDerivedComplete l E W K → IsIso (χ.app K)) := by
  sorry

/-- The normalized scalar completion map, including on nonconstructible complete Homs.
Source: Bhatt--Scholze 3.5.1 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarCompletion (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarCompletion_existsUnique l E L ι W).exists.choose


/-- The intrinsic ordinary closed structure, retaining the recorded ambient Hom.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarIntegralClosed (W : AlgebraicGeometry.Scheme.{u}) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralClosed

/-- The normalized total tensor models for the same closed structure.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarIntegralModels (W : AlgebraicGeometry.Scheme.{u}) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralTensorModel

/-- Ordinary total tensor base change, fixed on sheafified pure tensors.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: send s tensor (x tensor y) to (s tensor x) tensor (1 tensor y).
Balance gives the inverse (s tensor x) tensor (t tensor y) to st tensor (x tensor y).
Sheafify, and sum over bidegrees. The formulas respect both signed differential
summands and chain maps. These generators determine the natural isomorphism. -/
theorem scalarOrdinaryTensorChain_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W),
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.hom.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)) U 1
            (coefficientTensorGenerator.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)) =
        coefficientTensorGenerator.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l L W)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y) := by
  sorry

/-- The pure-tensor-normalized ordinary total comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarOrdinaryTensorChain (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarOrdinaryTensorChain_existsUnique l E L ι W).exists.choose

/-- The ordinary derived scalar tensor comparison is fixed on all good pairs.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: scalarGood supplies good target representatives. Localize the ordinary
pure-tensor chain isomorphism, using the two normalized closed tensor models.
Exact ordinary extension identifies its derived value with its termwise value.
The displayed square is that conjugation. Naturality on roofs and simultaneous
localization give a natural isomorphism and uniqueness with this square. -/
theorem scalarClosedTensor_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : (scalarIntegralClosed l E W).tensor ⋙
        integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ (scalarIntegralClosed l L W).tensor,
      ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
          (((scalarIntegralModels l E W).iso _ _ _ _ _ P.property.1 Q.property.1).hom) ≫
          α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (scalarIntegralClosed l L W).tensor.map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) =
        (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L ι W).hom.app (P.obj, Q.obj)) ≫
          ((scalarIntegralModels l L W).iso _ _ _ _ _
            (scalarGood l E L ι W P).1 (scalarGood l E L ι W Q).1).hom := by
  sorry

/-- The canonical closed scalar tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarClosedTensor (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarClosedTensor_existsUnique l E L ι W).exists.choose

/-- Ordinary scalar/internal-Hom comparison: transpose of scalar-extended evaluation.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarHomOrdinary (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W)) :=
  coefficientBaseChangeHom (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
    (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W) M N

/-- Finite free scalar extension commutes with internal Hom, including unbounded inputs.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: resolve the second input by a K-injective complex. After restriction, finite
free extension is a finite direct sum. Internal Hom into a finite direct sum is
the corresponding finite sum of internal Homs; restriction is exact, so the derived
adjunction gives the same conclusion. Under the closed tensor model, the resulting
map is exactly the transpose of extended evaluation, namely scalarHomOrdinary.
The inverse is the finite-free tensor-Hom identity; its basis calculation is
independent of the basis. Thus this specified map is invertible. -/
theorem scalarHomOrdinary_isIso (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W)) :
    IsIso (scalarHomOrdinary l E L ι W M N) := by
  sorry


/-- The completion isomorphism on an actually derived-complete object.
Source: Bhatt--Scholze 3.5.1 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarCompletionIso (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules l E W)) (hK : IsSfDerivedComplete l E W K) :
    (integralOrdinaryDerivedScalar l E L ι W).obj K ≅
      (integralScalarExtension l E L ι W).obj K := by
  letI : IsIso ((scalarCompletion l E L ι W).app K) :=
    (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.2 K hK
  exact asIso ((scalarCompletion l E L ι W).app K)

/-- Completed pullback/scalar comparison, conjugated by the normalized completion maps.
Source: Stacks 099N (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarPullbackCompleted {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : IsSfDerivedComplete l E Y K)
    (hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj K)) :
    (integralScalarExtension l E L ι X).obj ((integralDerivedPullback l E f).obj K) ≅
      (integralDerivedPullback l L f).obj ((integralScalarExtension l E L ι Y).obj K) :=
  (scalarCompletionIso l E L ι X _ hF).symm ≪≫
    (scalarPullbackOrdinary l E L ι f).app K ≪≫
    (integralDerivedPullback l L f).mapIso (scalarCompletionIso l E L ι Y K hK)

/-- Completed tensor/scalar comparison, with the prescribed ordinary and Roos maps.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorCompleted (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : IsSfDerivedComplete l E W M) (hN : IsSfDerivedComplete l E W N)
    (hT : IsSfDerivedComplete l E W ((integralCompletedTensor l E W).obj (M, N))) :
    (integralScalarExtension l E L ι W).obj ((integralCompletedTensor l E W).obj (M, N)) ≅
      (integralCompletedTensor l L W).obj
        ((integralScalarExtension l E L ι W).obj M,
          (integralScalarExtension l E L ι W).obj N) :=
  (scalarCompletionIso l E L ι W _ hT).symm ≪≫
    (scalarTensorOrdinary l E L ι W).app (M, N) ≪≫
    (integralCompletedTensor l L W).mapIso
      (Iso.prod (scalarCompletionIso l E L ι W M hM) (scalarCompletionIso l E L ι W N hN))

/-- The completed Hom comparison uses the inverse first-variable comparison.
It is defined whenever its three completion inverses exist; in particular this
includes every permitted constructible-Hom pair in the owning definition.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarHomCompleted (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : IsSfDerivedComplete l E W M) (hN : IsSfDerivedComplete l E W N)
    (hH : IsSfDerivedComplete l E W ((integralDerivedInternalHom l E W).obj (op M, N))) :
    (integralScalarExtension l E L ι W).obj
        ((integralDerivedInternalHom l E W).obj (op M, N)) ≅
      (integralDerivedInternalHom l L W).obj
        (op ((integralScalarExtension l E L ι W).obj M),
          (integralScalarExtension l E L ι W).obj N) := by
  letI := scalarHomOrdinary_isIso l E L ι W M N
  exact (scalarCompletionIso l E L ι W _ hH).symm ≪≫
    asIso (scalarHomOrdinary l E L ι W M N) ≪≫
    (integralDerivedInternalHom l L W).mapIso
      (Iso.prod (scalarCompletionIso l E L ι W M hM).symm.op
        (scalarCompletionIso l E L ι W N hN))


/-- Ambient internal Hom into a complete object is complete; constructibility of the
Hom is not assumed. Source: Bhatt--Scholze 3.4.11; Stacks 08JB, 099B
(blueprint: lem-pur-integral-operations-scalar-extension).
Proof: restrict to every slice. Tensor-Hom currying identifies Hom from R[1/t]
into Hom(M,N) with Hom from M into Hom(R[1/t],N), which vanishes by completeness
of N. The local Koszul completion reflector identifies this vanishing with
invertibility of the canonical completion unit. Its Roos triangle is the specified
strict reduction-tower triangle, giving precisely IsSfDerivedComplete. -/
theorem scalarInternalHom_complete (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hN : IsSfDerivedComplete l E W N) :
    IsSfDerivedComplete l E W ((integralDerivedInternalHom l E W).obj (op M, N)) := by
  sorry

/-- The canonical completed Hom comparison on all complete input pairs, including
those whose Hom is not constructible.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarHomCompleteInputs (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : IsSfDerivedComplete l E W M) (hN : IsSfDerivedComplete l E W N) :=
  scalarHomCompleted l E L ι W M N hM hN (scalarInternalHom_complete l E W M N hN)


private theorem scalarEvaluation_naturality
    {D : Type a} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _

private theorem scalarBaseChangeHom_naturality
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P Q P' Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q') :
    F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ P' Q' =
      coefficientBaseChangeHom SA SB F μ P Q ≫
        HB.map (Prod.mkHom (F.map f).op (F.map g)) := by
  let := SB.monoidal
  have hu (T P Q : B) (h : T ⟶ HB.obj (op P, Q)) :
      (SB.transpose T P Q).symm h =
        SB.tensor.map (Prod.mkHom h (𝟙 P)) ≫ SB.evaluation P Q := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      CoefficientClosedStructure.evaluation] using! (SB.adjunction P).homEquiv_counit T Q h
  apply (SB.transpose _ (F.obj P') (F.obj Q')).symm.injective
  rw [hu, hu]
  have tc {U V Z R : B} (a : U ⟶ V) (b : V ⟶ Z) :
      SB.tensor.map (Prod.mkHom (a ≫ b) (𝟙 R)) =
        SB.tensor.map (Prod.mkHom a (𝟙 R)) ≫ SB.tensor.map (Prod.mkHom b (𝟙 R)) := by
    rw [← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  simp only [tc, Category.assoc]
  rw [scalarEvaluation_naturality SB _ _ _ _ (F.map f) (F.map g)]
  have beta (U V : A) :
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ U V) (𝟙 (F.obj U))) ≫
        SB.evaluation (F.obj U) (F.obj V) =
          μ.inv.app (HA.obj (op U, V), U) ≫ F.map (SA.evaluation U V) := by
    rw [← hu, coefficientBaseChangeHom, Equiv.symm_apply_apply]
  rw [beta]
  have hn := μ.inv.naturality (Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 P'))
  have hn' := μ.inv.naturality (Prod.mkHom (𝟙 (HA.obj (op P, Q))) f)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn hn'
  erw [F.map_id] at hn
  erw [F.map_id] at hn'
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, scalarEvaluation_naturality SA]
  rw [F.map_comp, F.map_comp]
  have ht : SB.tensor.map
      (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P'))) ≫
      SB.tensor.map (Prod.mkHom (𝟙 _) (F.map f)) =
    SB.tensor.map (Prod.mkHom (𝟙 _) (F.map f)) ≫
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P))) := by
    rw [← SB.tensor.map_comp, ← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [reassoc_of% ht, reassoc_of% beta P Q, ← reassoc_of% hn']


/-- Naturality of the evaluation-defined ordinary Hom comparison in both variables.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: uncurry both sides. Tensor-comparison naturality and evaluation naturality
identify both uncurried maps with extended evaluation after the two given arrows.
The closed transpose bijection gives the equality, including precomposition. -/
theorem scalarHomOrdinary_naturality (W : AlgebraicGeometry.Scheme.{u})
    (M N M' N' : DerivedCategory (integralTowerModules l E W))
    (a : M' ⟶ M) (b : N ⟶ N') :
    (integralOrdinaryDerivedScalar l E L ι W).map
      ((integralDerivedInternalHom l E W).map (CategoryTheory.Prod.mkHom a.op b)) ≫
        scalarHomOrdinary l E L ι W M' N' =
      scalarHomOrdinary l E L ι W M N ≫
        (integralDerivedInternalHom l L W).map (CategoryTheory.Prod.mkHom
          ((integralOrdinaryDerivedScalar l E L ι W).map a).op
          ((integralOrdinaryDerivedScalar l E L ι W).map b)) := by
  exact scalarBaseChangeHom_naturality (scalarIntegralClosed l E W)
    (scalarIntegralClosed l L W) (integralOrdinaryDerivedScalar l E L ι W)
    (scalarClosedTensor l E L ι W) M N M' N' a b

/-- The prescribed comparisons commute with coefficient towers before completion.
Conjugation by scalarCompletion gives the completed tower identities, with the
same completed scalar associators as the recorded scalar-extension composition.
Source: blueprint scalar comparison proof step 9; Stacks 07A4, 08J9
(blueprint: lem-pur-integral-operations-scalar-extension).
Proof: on finite pullback and tensor generators, both routes multiply the two
new coefficients in the same order. This gives equality of the strict tower maps
and both diagonal Roos coordinates. Their localizations give the first two
equalities. Uncurry the Hom equality: both routes evaluate h on m and multiply
those same coefficients. The normalized closed transpose gives the third
equality. The canonical completion maps commute with these diagrams by their
quotient generator normalization; cancel adjacent inverse completion maps to
obtain the completed identities. -/
theorem scalarOperationsOrdinary_tower
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{u}) :
    (∀ K : DerivedCategory (integralTowerModules l E Y),
      (integralOrdinaryDerivedScalar l L F j X).map
          ((scalarPullbackOrdinary l E L ι f).hom.app K) ≫
        (scalarPullbackOrdinary l L F j f).hom.app
          ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
        (integralDerivedPullback l F f).map
          ((integralOrdinaryDerivedScalarComp l E L ι Y F j).hom.app K) =
      (integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app
          ((integralDerivedPullback l E f).obj K) ≫
        (scalarPullbackOrdinary l E F (j.comp ι) f).hom.app K) ∧
    (∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralOrdinaryDerivedScalar l L F j W).map
          ((scalarTensorOrdinary l E L ι W).hom.app (M, N)) ≫
        (scalarTensorOrdinary l L F j W).hom.app
          ((integralOrdinaryDerivedScalar l E L ι W).obj M,
            (integralOrdinaryDerivedScalar l E L ι W).obj N) ≫
        (integralCompletedTensor l F W).map (CategoryTheory.Prod.mkHom
          ((integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app M)
          ((integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app N)) =
      (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
          ((integralCompletedTensor l E W).obj (M, N)) ≫
        (scalarTensorOrdinary l E F (j.comp ι) W).hom.app (M, N)) ∧
    (∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralOrdinaryDerivedScalar l L F j W).map
          (scalarHomOrdinary l E L ι W M N) ≫
        scalarHomOrdinary l L F j W
          ((integralOrdinaryDerivedScalar l E L ι W).obj M)
          ((integralOrdinaryDerivedScalar l E L ι W).obj N) ≫
        (integralDerivedInternalHom l F W).map (CategoryTheory.Prod.mkHom
          (((integralOrdinaryDerivedScalarComp l E L ι W F j).inv.app M).op)
          ((integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app N)) =
      (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
          ((integralDerivedInternalHom l E W).obj (op M, N)) ≫
        scalarHomOrdinary l E F (j.comp ι) W M N) := by
  sorry

/-- Identity coefficient extension has the ordinary tensor-unit normalization.
After completion this is the canonical completeness unit, rather than a literal
identity between chosen Roos representatives.
Source: blueprint scalar comparison proof step 9; Stacks 07A4, 08J9
(blueprint: lem-pur-integral-operations-scalar-extension).
Proof: specialize each pure-tensor formula to the identity coefficient map. The
ordinary unit multiplies r tensor x to rx, and its inverse sends x to 1 tensor x.
Both sides of each equation have this same action on generators. The strict Roos
maps and localization preserve these equalities. For Hom, uncurry and evaluate;
the inverse first-variable unit and the second-variable unit give the displayed
equation. Conjugating by the normalized completion maps gives the stated
canonical unit normalization on complete inputs. -/
theorem scalarOperationsOrdinary_unit {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{u}) :
    (∀ K : DerivedCategory (integralTowerModules l E Y),
      (integralOrdinaryDerivedScalarUnit l E X).inv.app
          ((integralDerivedPullback l E f).obj K) ≫
        (scalarPullbackOrdinary l E E (AlgHom.id ℚ_[l] E) f).hom.app K =
      (integralDerivedPullback l E f).map
        ((integralOrdinaryDerivedScalarUnit l E Y).inv.app K)) ∧
    (∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralOrdinaryDerivedScalarUnit l E W).inv.app
          ((integralCompletedTensor l E W).obj (M, N)) ≫
        (scalarTensorOrdinary l E E (AlgHom.id ℚ_[l] E) W).hom.app (M, N) =
      (integralCompletedTensor l E W).map (CategoryTheory.Prod.mkHom
        ((integralOrdinaryDerivedScalarUnit l E W).inv.app M)
        ((integralOrdinaryDerivedScalarUnit l E W).inv.app N))) ∧
    (∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralDerivedInternalHom l E W).map (CategoryTheory.Prod.mkHom
          (((integralOrdinaryDerivedScalarUnit l E W).inv.app M).op) (𝟙 N)) ≫
        (integralOrdinaryDerivedScalarUnit l E W).inv.app
          ((integralDerivedInternalHom l E W).obj (op M, N)) ≫
        scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) W M N =
      (integralDerivedInternalHom l E W).map (CategoryTheory.Prod.mkHom
        (𝟙 (op ((integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) W).obj M)))
        ((integralOrdinaryDerivedScalarUnit l E W).inv.app N))) := by
  sorry

end WeilConjectures
