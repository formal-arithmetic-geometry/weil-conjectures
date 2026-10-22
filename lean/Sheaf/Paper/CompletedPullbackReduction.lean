/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.Paper.CompletedConstantAlgebraFlatQuotients
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.FourCorners
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Sheaf.Paper.AdicCoefficientDatum
import all Sheaf.Paper.ReductionPullbackDerivedTower
/-! # Finite reduction of completed pullback

Source: Stacks Project, Tag 099N (5), and blueprint order 1262
(blueprint: lemma-weil-pbc-completed-pullback-reduction).

## Main definitions

- `completedPullbackReductionArrow`: adjunct of the actual limit projection.
- `completedReductionTargetNormalization`: canonical scalar normalization of finite pullback.

## Main statements

- `completedPullback_reduction`: completeness, finite reduction and every coherence clause.

All coefficients remain sheaves on the original small pro-etale sites. Positive
level n is encoded by n-1, so a natural number n denotes the quotient by I^(n+1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] CategoryTheory.Functor.mapHomotopyCategory
attribute [local irreducible] CategoryTheory.Functor.mapHomotopyCategoryFactors
open AlgebraicGeometry.ProEtale
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme
attribute [local instance] completedTowerModulePullback_additive
attribute [local instance] completedReductionModuleTowerFunctor_additive
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The functor whose object map is the published completed pullback.
Source: blueprint order 1262 (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedPullbackFunctor :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  completedReductionTower Y d ⋙ completedTowerPullback g d ⋙ completedTowerRlim d X

/-- The small-model module pushforward has its canonical pullback adjunction.
Source: Stacks 03D2 (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: the small-model site functor is continuous and cocontinuous. Compose its
module inverse image with module sheafification; Mathlib's pullback construction
is left adjoint to the specified sectionwise pushforward. -/
theorem completedReductionModelPushforward_isRightAdjoint
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    (@SheafOfModules.pushforward.{u + 1} _ _ _ _ _ _ _ _ _
      (proEtaleModelBaseChange_isContinuous g) (proEtaleModelRingUnit g R)).IsRightAdjoint := by
  infer_instance

/-- An inverse-image generator from an object V and a base-change arrow U→g*V.
It is the small-model module-adjunction unit followed by restriction along that arrow.
Source: Stacks 03D2, 00VC (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionInverseImageGenerator
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (M : pbcModules Y R)
    (V : Y.ProEt) (U : X.ProEt) (f : U ⟶ (proEtaleBaseChange g).obj V)
    (m : M.val.obj (op V)) :
    ((proEtaleModuleInverseImage g R).obj M).val.obj (op U) :=
  ((proEtaleModuleInverseImage g R).obj M).val.map f.op
    (((@SheafOfModules.pullbackPushforwardAdjunction.{u + 1} _ _ _ _ _ _ _ _ _
        (proEtaleModelBaseChange_isContinuous g) (proEtaleModelRingUnit g R)
        (completedReductionModelPushforward_isRightAdjoint g R)).unit.app
      ((proEtaleModuleToModel ((adicLisseForget Y).obj R)).obj M)).val.app
        (op (AsSmall.up.obj V)) m)

attribute [irreducible] completedReductionInverseImageGenerator

/-- The standard localization comparison for exact restriction, with its exactness
instances supplied by the existing coefficient interface.
Source: Stacks 03D3 (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionRestrictionFactors (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedRestrict φ ≅
      (pbcRestrict φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (pbcRestrict φ).mapDerivedCategoryFactors

/-- The existing tensor-formula module pullback over the finite coefficient sheaves.
Source: Stacks 099N (5) (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
abbrev completedReductionFiniteModules (n : ℕ) :=
  proEtaleRingModulePullback g (reductionCoefficient Y d n)
    (reductionCoefficient X d n) (asIso (completedFiniteCoefficientMap g d n))

/-- Exact finite-coefficient pullback, with the standard localization on both sites.
Source: Stacks 099N (5) (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
abbrev completedReductionFiniteDerived (n : ℕ) :=
  proEtaleRingDerivedPullback g (reductionCoefficient Y d n)
    (reductionCoefficient X d n) (asIso (completedFiniteCoefficientMap g d n))

/-- Finite pullback of the finite reduction, with its quotient action retained.
Source: blueprint order 1262 (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteTarget (n : ℕ) :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (reductionCoefficient X d n)) :=
  reductionDerivedChange Y (completedReductionProjection Y d n) ⋙
    completedReductionFiniteDerived g d n

/-- The actual sheafified pure tensor in the tensor-formula finite pullback.
Source: Stacks 03EK (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteTensor (n : ℕ)
    (M : pbcModules Y (reductionCoefficient Y d n))
    (U : X.ProEtᵒᵖ) (s : (reductionCoefficient X d n).obj.obj U)
    (m : ((proEtaleModuleInverseImage g
      (reductionCoefficient Y d n)).obj M).val.obj U) :
    ((completedReductionFiniteModules g d n).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((adicLisseForget X).obj (reductionCoefficient X d n)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (completedFiniteCoefficientMap g d n)
        ((proEtaleModuleInverseImage g (reductionCoefficient Y d n)).obj M))).app U
          (s ⊗ₜ[((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (reductionCoefficient Y d n)).obj.obj U,
              ((completedFiniteCoefficientMap g d n).hom.app U).hom] m)

attribute [irreducible] completedReductionFiniteTensor

/-- A pure tensor generator of the finite pullback of a reduction.
This uses the recorded scalar-extension tensor, the module inverse-image unit,
and the actual tensor-formula finite pullback, without any choice of sections.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteGenerator (n : ℕ)
    (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
    (f : U ⟶ (proEtaleBaseChange g).obj V)
    (s : (reductionCoefficient X d n).obj.obj (op U))
    (z : (reductionCoefficient Y d n).obj.obj (op V)) (m : M.val.obj (op V)) :
    ((completedReductionFiniteModules g d n).obj
      ((reductionChange Y (completedReductionProjection Y d n)).obj M)).val.obj (op U) :=
  completedReductionFiniteTensor g d n _ (op U) s
    (completedReductionInverseImageGenerator g (reductionCoefficient Y d n)
      ((reductionChange Y (completedReductionProjection Y d n)).obj M) V U f
        (pbcTensorSection (completedReductionProjection Y d n) M (op V) z m))

attribute [irreducible] completedReductionFiniteGenerator

/-- Explicitly inherit zero preservation before forming the complex comparison.
Source: Stacks 03EK (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
instance completedReductionOrdinarySource_preservesZero (n : ℕ) :
    (completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).PreservesZeroMorphisms :=
  letI := completedReductionModuleTowerFunctor_additive Y d
  letI := completedTowerModulePullback_additive g d
  Functor.preservesZeroMorphisms_of_additive _

/-- The canonical limit projection, derived from the ordinary projection.
Source: Stacks 08TC (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionLimitProjection (n : ℕ) :
    completedTowerRlim d X ⟶ pbcTowerEvaluation X (pbcAdicCompletion X d) n :=
  Functor.rightDerivedFunctorNatTrans
    (lim.π (C := pbcModules X (pbcAdicCompletion X d)) (op n)) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).rightDerivedFunctorIsoMapDerivedCategory.hom

/-- Canonical balancing across two quotient maps, using the existing scalar adjunctions.
Source: blueprint quotient cocycle (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionQuotientAssoc (T : Scheme.{u}) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c)
    (M : DerivedCategory (pbcModules T (reductionCoefficient T d c))) :=
  pbcReductionNormalization (reductionCoefficientMap T d c b hbc)
    (reductionCoefficientMap T d b a hab)
    (reductionCoefficientMap T d c a (hab.trans hbc))
    (reductionCoefficientMap_comp T d c b a hab hbc) M

/-- Canonical scalar balancing for the finite reductions of a completed-coefficient object.
Source: blueprint normalization (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedPullbackSourceNormalization (T : Scheme.{u}) (a b : ℕ) (h : a ≤ b)
    (M : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :=
  pbcReductionNormalization (completedReductionProjection T d b)
    (reductionCoefficientMap T d b a h) (completedReductionProjection T d a)
    (completedReductionProjection_comp T d b a h) M

/-- An equality of sections of a scalar-semilinear module map, stated over abstract rings.
Naming this predicate keeps concrete finite-ring constructions out of kernel conversion.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionSectionEquation (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M : pbcModules T R} {N : pbcModules T S}
    (ν : M ⟶ (pbcRestrict φ).obj N) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : Prop := ν.val.app U x = y

attribute [irreducible] completedReductionSectionEquation

/-- The representative normalization specifying the ordinary finite comparison uniquely.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def HasCompletedReductionOrdinaryComparisonNormalization (n : ℕ)
    (e : completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n))) : Prop :=
  ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
        (f : U ⟶ (proEtaleBaseChange g).obj V)
        (b : (pbcAdicCompletion X d).obj.obj (op U))
        (m : M.val.obj (op V)),
        completedReductionSectionEquation X (completedReductionProjection X d n)
          (e.hom.app M) (op U)
          (reductionTensorSection X (completedCoefficientMap g d) _ (op U) b
            (completedReductionInverseImageGenerator g (pbcAdicCompletion Y d)
              (((completedReductionModuleTowerFunctor Y d).obj M).obj (op n)) V U f
                ((((completedReductionModuleUnit d Y).app M).app (op n)).val.app (op V) m)))
          (completedReductionFiniteGenerator g d n M V U f
            ((completedReductionProjection X d n).hom.app (op U) b) 1 m)

attribute [irreducible] HasCompletedReductionOrdinaryComparisonNormalization

/-- The completed structure map is the invertible profinite coefficient comparison. -/
private theorem coefficientMap_isIso : IsIso (completedCoefficientMap g d) := by
  have he : completedCoefficientMap g d = (d.integralRingIso g).hom := by
    apply limit.hom_ext
    intro n
    change completedCoefficientMap g d ≫ d.projection X n.unop =
      (d.integralRingIso g).hom ≫ d.projection X n.unop
    rw [d.projection_comm]
    exact limit.lift_π _ n
  rw [he]
  infer_instance

/-- Identify the chosen extension functor with exact pullback over isomorphic rings. -/
private def exactPullbackIso : completedModulePullback g d ≅
    proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (@asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d)) :=
  NatIso.ofComponents (fun M ↦ eqToIso
    (reductionChange_obj_eq X (completedCoefficientMap g d)
      ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M))) (by
    intro M N f
    dsimp only [completedModulePullback, Functor.comp_map, proEtaleRingModulePullback,
      proEtaleRingModulePullbackMap]
    rw [reductionChange_map_eq]
    simp)

section OrdinaryComparison
variable (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
private def ringTensor (M : pbcModules Y R) (U : X.ProEtᵒᵖ) (s : S.obj.obj U)
    (m : ((proEtaleModuleInverseImage g R).obj M).val.obj U) :
    ((proEtaleRingModulePullback g R S c).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((adicLisseForget X).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
        ((proEtaleModuleInverseImage g R).obj M))).app U
          (s ⊗ₜ[_, (c.hom.hom.app U).hom] m)

private theorem ringTensor_smul (M : pbcModules Y R) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U)
    (m : ((proEtaleModuleInverseImage g R).obj M).val.obj U) :
    ringTensor g R S c M U s m = s • ringTensor g R S c M U 1 m := by
  let eta := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((adicLisseForget X).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
        ((proEtaleModuleInverseImage g R).obj M))).app U
  change eta (s ⊗ₜ[_, (c.hom.hom.app U).hom] m) =
    s • eta ((1 : S.obj.obj U) ⊗ₜ[_, (c.hom.hom.app U).hom] m)
  rw [← eta.hom.map_smul]
  congr 1
  change s ⊗ₜ[_, (c.hom.hom.app U).hom] m =
    (s * 1) ⊗ₜ[_, (c.hom.hom.app U).hom] m
  rw [mul_one]

private theorem ringAdjunction_generator
    (M : pbcModules Y R) (N : pbcModules X S)
    (h : (proEtaleRingModulePullback g R S c).obj M ⟶ N)
    (V : Y.ProEt) (m : M.val.obj (op V)) :
    (((proEtaleRingModuleAdjunction g R S c).homEquiv M N) h).val.app (op V) m =
      h.val.app (op ((proEtaleBaseChange g).obj V))
        (ringTensor g R S c M (op ((proEtaleBaseChange g).obj V)) 1
          (completedReductionInverseImageGenerator.{u} g R M V
            ((proEtaleBaseChange g).obj V) (𝟙 _) m)) := by
  obtain ⟨k, hk, he⟩ :=
    (Classical.choose_spec (proEtaleRingModuleAdjunction_existsUnique g R S c)).1 M N h
  unfold proEtaleRingModuleAdjunction
  rw [he, Adjunction.homEquiv_unit]
  change k.val.app (op (AsSmall.up.obj ((proEtaleBaseChange g).obj V)))
    (((@SheafOfModules.pullbackPushforwardAdjunction.{u + 1} _ _ _ _ _ _ _ _ _
      (proEtaleModelBaseChange_isContinuous g) (proEtaleModelRingUnit g R)
      (completedReductionModelPushforward_isRightAdjoint g R)).unit.app
      ((proEtaleModuleToModel ((adicLisseForget Y).obj R)).obj M)).val.app
        (op (AsSmall.up.obj V)) m) = _
  rw [hk]
  unfold ringTensor completedReductionInverseImageGenerator
  simp
  rfl

private theorem ringTensor_restrict (M : pbcModules Y R) {U V : X.ProEtᵒᵖ}
    (i : U ⟶ V) (m : ((proEtaleModuleInverseImage g R).obj M).val.obj U) :
    ((proEtaleRingModulePullback g R S c).obj M).val.map i
        (ringTensor g R S c M U 1 m) =
      ringTensor g R S c M V 1 (((proEtaleModuleInverseImage g R).obj M).val.map i m) := by
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((adicLisseForget X).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
        ((proEtaleModuleInverseImage g R).obj M))
  have hi := PresheafOfModules.naturality_apply eta i
    ((1 : S.obj.obj U) ⊗ₜ[_, (c.hom.hom.app U).hom] m)
  change eta.app V (SheafOfModules.changeOfRingsMap c.hom
    ((proEtaleModuleInverseImage g R).obj M) i
      ((1 : S.obj.obj U) ⊗ₜ[_, (c.hom.hom.app U).hom] m)) = _ at hi
  unfold SheafOfModules.changeOfRingsMap at hi
  rw [Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap c.hom
    ((proEtaleModuleInverseImage g R).obj M) i), map_one] at hi
  exact hi.symm

private theorem ringTensor_generator_restrict (M : pbcModules Y R)
    (V : Y.ProEt) (U : X.ProEt) (f : U ⟶ (proEtaleBaseChange g).obj V)
    (m : M.val.obj (op V)) :
    ((proEtaleRingModulePullback g R S c).obj M).val.map f.op
      (ringTensor g R S c M (op ((proEtaleBaseChange g).obj V)) 1
        (completedReductionInverseImageGenerator.{u} g R M V
          ((proEtaleBaseChange g).obj V) (𝟙 _) m)) =
      ringTensor g R S c M (op U) 1
        (completedReductionInverseImageGenerator.{u} g R M V U f m) := by
  rw [ringTensor_restrict]
  unfold completedReductionInverseImageGenerator
  simp

private theorem quotientUnit_hom_ext (T : Scheme.{u})
    {B D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (phi : B ⟶ D)
    (surj : ∀ U : T.ProEtᵒᵖ, Function.Surjective (phi.hom.app U))
    (M N : pbcModules T B)
    (f k : (reductionRestrict T phi).obj ((reductionChange T phi).obj M) ⟶ N)
    (he : ∀ (U : T.ProEtᵒᵖ) (m : M.val.obj U),
      f.val.app U (reductionTensorSection T phi M U 1 m) =
        k.val.app U (reductionTensorSection T phi M U 1 m)) : f = k := by
  apply level_hom_ext T phi M N f k
  intro U s m
  obtain ⟨b, hb⟩ := surj U s
  let L := (reductionRestrict T phi).obj ((reductionChange T phi).obj M)
  let x : L.val.obj U := reductionTensorSection T phi M U 1 m
  have hs : (reductionTensorSection T phi M U s m : L.val.obj U) = b • x := by
    change reductionTensorSection T phi M U s m =
      (phi.hom.app U b) • reductionTensorSection T phi M U 1 m
    rw [hb, tensorSection_smul, mul_one]
  rw [hs, map_smul, map_smul, he]

variable (R' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (aR : R ⟶ R') (aS : S ⟶ S')
  (c' : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R' ≅ S')
  (hc : c.hom ≫ aS =
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aR ≫ c'.hom)

private theorem ringRestriction_generator
    (M : pbcModules Y R') (V : Y.ProEt) (m : M.val.obj (op V)) :
    ((proEtaleRingRestrictionPullbackInv g R R' S S' aR aS c c' hc).app M).val.app
      (op ((proEtaleBaseChange g).obj V))
      (ringTensor g R S c ((proEtaleRingRestrictScalars aR).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (completedReductionInverseImageGenerator.{u} g R
          ((proEtaleRingRestrictScalars aR).obj M) V
          ((proEtaleBaseChange g).obj V) (𝟙 _) m)) =
      ringTensor g R' S' c' M (op ((proEtaleBaseChange g).obj V)) 1
        (completedReductionInverseImageGenerator.{u} g R' M V
          ((proEtaleBaseChange g).obj V) (𝟙 _) m) := by
  let adjR := proEtaleRingModuleAdjunction g R S c
  let adjS := proEtaleRingModuleAdjunction g R' S' c'
  let delta := proEtaleRingRestrictionDirectImage g R R' S S' aR aS c c' hc
  let k := (proEtaleRingRestrictionPullbackInv g R R' S S' aR aS c c' hc).app M
  have hk : k = (adjR.homEquiv _ _).symm
      ((proEtaleRingRestrictScalars aR).map (adjS.unit.app M) ≫
        delta.hom.app ((proEtaleRingModulePullback g R' S' c').obj M)) := by
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rfl
  have he := (adjR.homEquiv _ _).apply_symm_apply
    ((proEtaleRingRestrictScalars aR).map (adjS.unit.app M) ≫
      delta.hom.app ((proEtaleRingModulePullback g R' S' c').obj M))
  rw [← hk] at he
  have hev := congrArg (fun t ↦ t.val.app (op V) m) he
  have hb := ringAdjunction_generator g R S c
    ((proEtaleRingRestrictScalars aR).obj M)
    ((proEtaleRingRestrictScalars aS).obj
      ((proEtaleRingModulePullback g R' S' c').obj M)) k V m
  have hd := (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique g R R' S S' aR aS c c' hc)).1
      ((proEtaleRingModulePullback g R' S' c').obj M) (op V)
      ((adjS.unit.app M).val.app (op V) m)
  have hu := ringAdjunction_generator g R' S' c' M
    ((proEtaleRingModulePullback g R' S' c').obj M) (𝟙 _) V m
  rw [Adjunction.homEquiv_id] at hu
  exact hb.symm.trans (hev.trans (hd.trans hu))

private theorem ringRestriction_generator_local
    (M : pbcModules Y R') (V : Y.ProEt) (U : X.ProEt)
    (f : U ⟶ (proEtaleBaseChange g).obj V) (b : S.obj.obj (op U))
    (m : M.val.obj (op V)) :
    ((proEtaleRingRestrictionPullbackInv g R R' S S' aR aS c c' hc).app M).val.app
      (op U)
      (ringTensor g R S c ((proEtaleRingRestrictScalars aR).obj M) (op U) b
        (completedReductionInverseImageGenerator.{u} g R
          ((proEtaleRingRestrictScalars aR).obj M) V U f m)) =
      ringTensor g R' S' c' M (op U) (aS.hom.app (op U) b)
        (completedReductionInverseImageGenerator.{u} g R' M V U f m) := by
  let k := (proEtaleRingRestrictionPullbackInv g R R' S S' aR aS c c' hc).app M
  have hn := PresheafOfModules.naturality_apply k.val f.op
    (ringTensor g R S c ((proEtaleRingRestrictScalars aR).obj M)
      (op ((proEtaleBaseChange g).obj V)) 1
      (completedReductionInverseImageGenerator.{u} g R
        ((proEtaleRingRestrictScalars aR).obj M) V
        ((proEtaleBaseChange g).obj V) (𝟙 _) m))
  change k.val.app (op U)
    (((proEtaleRingModulePullback g R S c).obj
      ((proEtaleRingRestrictScalars aR).obj M)).val.map f.op _) = _ at hn
  rw [ringTensor_generator_restrict] at hn
  dsimp only [k] at hn
  rw [ringRestriction_generator] at hn
  change k.val.app (op U) _ =
    ((proEtaleRingModulePullback g R' S' c').obj M).val.map f.op
      (ringTensor g R' S' c' M (op ((proEtaleBaseChange g).obj V)) 1
        (completedReductionInverseImageGenerator.{u} g R' M V
          ((proEtaleBaseChange g).obj V) (𝟙 _) m)) at hn
  rw [ringTensor_generator_restrict] at hn
  have hs := (k.val.app (op U)).hom.map_smul b
    (ringTensor g R S c ((proEtaleRingRestrictScalars aR).obj M) (op U) 1
      (completedReductionInverseImageGenerator.{u} g R
        ((proEtaleRingRestrictScalars aR).obj M) V U f m))
  change k.val.app (op U) (b • _) =
    (aS.hom.app (op U) b) •
      (show ((proEtaleRingModulePullback g R' S' c').obj M).val.obj (op U)
        from k.val.app (op U) _) at hs
  rw [← ringTensor_smul] at hs
  exact hs.trans ((congrArg (fun x :
    ((proEtaleRingModulePullback g R' S' c').obj M).val.obj (op U) ↦
      (aS.hom.app (op U) b) • x) hn).trans (ringTensor_smul g R' S' c' _ _ _ _).symm)

private theorem projection_surjective {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{u}) (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective ((completedReductionProjection T d n).hom.app U) := by
  let := d.noetherian
  let e := pbcCompletedComparison T d
  let c := CompletedConstantReduction.base T d.ideal ≫ e.hom
  have hc (m : ℕ) : c ≫ e.inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op m) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (m + 1)))) := by
    dsimp only [c]
    rw [Category.assoc, e.hom_inv_id_assoc]
    exact (CompletedConstantReduction.base_exists T d.ideal).choose_spec.1 m
  have hp : completedReductionProjection T d n =
      e.inv ≫ limit.π (adicLisseRingSystem T d.ideal) (op n) ≫
        (pbcLevelConstantComparison T d n).hom := by
    dsimp only [e, pbcCompletedComparison]
    rw [HasLimit.isoOfNatIso_inv_π_assoc]
    simp [pbcConstantSystemComparison, completedReductionProjection]
    rfl
  exact (CompletedConstantAlgebra.projection_surjective_and_kernel T d.ideal e c hc n
    (pbcLevelConstantComparison T d n) (completedReductionProjection T d n) hp U).1

private theorem exactPullbackIso_tensor (M : pbcModules Y (pbcAdicCompletion Y d))
    (U : X.ProEtᵒᵖ) (b : (pbcAdicCompletion X d).obj.obj U)
    (m : ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M).val.obj U) :
    ((exactPullbackIso g d).hom.app M).val.app U
      (reductionTensorSection X (completedCoefficientMap g d) _ U b m) =
    ringTensor g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (@asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d)) M U b m := by
  let h := reductionChange_obj_eq X (completedCoefficientMap g d)
    ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)
  have he : eqToHom h.symm ≫ eqToHom h = 𝟙 _ := by simp
  have ht := congrArg (fun t ↦ t.val.app U
    (ringTensor g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (@asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d)) M U b m)) he
  with_unfolding_all exact ht

private theorem exactPullbackIso_inv_tensor (M : pbcModules Y (pbcAdicCompletion Y d))
    (U : X.ProEtᵒᵖ) (b : (pbcAdicCompletion X d).obj.obj U)
    (m : ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M).val.obj U) :
    ((exactPullbackIso g d).inv.app M).val.app U
      (ringTensor g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (@asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d)) M U b m) =
      reductionTensorSection X (completedCoefficientMap g d) _ U b m := by
  rw [← exactPullbackIso_tensor]
  have he := congrArg (fun t ↦ t.val.app U
    (reductionTensorSection X (completedCoefficientMap g d) _ U b m))
    ((exactPullbackIso g d).hom_inv_id_app M)
  exact he

private def ordinaryIsoCandidate (n : ℕ) :
    completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
    reductionChange Y (completedReductionProjection Y d n) ⋙
      completedReductionFiniteModules g d n ⋙
        SheafOfModules.restrictScalars.{u + 1}
          ((adicLisseForget X).map (completedReductionProjection X d n)) := by
  let cB := @asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d)
  have hc : cB.hom ≫ completedReductionProjection X d n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (completedReductionProjection Y d n) ≫
          (asIso (completedFiniteCoefficientMap g d n)).hom := by
    exact limit.lift_π _ (op n)
  let k := proEtaleRingRestrictionPullbackInv g (pbcAdicCompletion Y d)
    (reductionCoefficient Y d n) (pbcAdicCompletion X d) (reductionCoefficient X d n)
    (completedReductionProjection Y d n) (completedReductionProjection X d n)
    cB (asIso (completedFiniteCoefficientMap g d n)) hc
  have : IsIso k := proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _
  let j : completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        proEtaleRingRestrictScalars (completedReductionProjection Y d n) ⋙
          proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d) cB :=
    NatIso.ofComponents (fun M ↦ (exactPullbackIso g d).app
      ((completedReductionLevel Y d n).obj M)) (by
        intro M N f
        exact (exactPullbackIso g d).hom.naturality ((completedReductionLevel Y d n).map f))
  exact j ≪≫ Functor.isoWhiskerLeft
    (reductionChange Y (completedReductionProjection Y d n)) (asIso k)
attribute [irreducible] ordinaryIsoCandidate

private theorem ordinaryIsoCandidate_tensor (n : ℕ)
    (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
    (f : U ⟶ (proEtaleBaseChange g).obj V) (b : (pbcAdicCompletion X d).obj.obj (op U))
    (m : ((reductionChange Y (completedReductionProjection Y d n)).obj M).val.obj (op V)) :
    ((ordinaryIsoCandidate g d n).hom.app M).val.app (op U)
      (reductionTensorSection X (completedCoefficientMap g d) _ (op U) b
        (completedReductionInverseImageGenerator.{u} g (pbcAdicCompletion Y d)
          ((completedReductionLevel Y d n).obj M) V U f m)) =
    completedReductionFiniteTensor g d n _ (op U)
      ((completedReductionProjection X d n).hom.app (op U) b)
      (completedReductionInverseImageGenerator.{u} g (reductionCoefficient Y d n)
        ((reductionChange Y (completedReductionProjection Y d n)).obj M) V U f m) := by
  unfold ordinaryIsoCandidate
  dsimp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Iso.app_hom,
    asIso_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [exactPullbackIso_tensor]
  unfold completedReductionFiniteTensor
  exact ringRestriction_generator_local g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (@asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d))
    (reductionCoefficient Y d n) (reductionCoefficient X d n)
    (completedReductionProjection Y d n) (completedReductionProjection X d n)
    (asIso (completedFiniteCoefficientMap g d n)) (limit.lift_π _ (op n))
    ((reductionChange Y (completedReductionProjection Y d n)).obj M) V U f b m

private theorem ordinaryIsoCandidate_normalized (n : ℕ) :
    HasCompletedReductionOrdinaryComparisonNormalization g d n
      (ordinaryIsoCandidate g d n) := by
  unfold HasCompletedReductionOrdinaryComparisonNormalization
  intro M V U f b m
  unfold completedReductionSectionEquation
  have hu : (((completedReductionModuleUnit d Y).app M).app (op n)).val.app (op V) m =
      reductionTensorSection Y (completedReductionProjection Y d n) M (op V) 1 m :=
    (completedReductionModuleUnit_exists d Y).exists.choose_spec M n (op V) m
  rw [hu]
  unfold completedReductionFiniteGenerator
  with_unfolding_all exact ordinaryIsoCandidate_tensor g d n M V U f b _

private theorem ordinaryIsoCandidate_unique (n : ℕ)
    (e : completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n)))
    (he : HasCompletedReductionOrdinaryComparisonNormalization g d n e) :
    e = ordinaryIsoCandidate g d n := by
  have hcan := ordinaryIsoCandidate_normalized g d n
  unfold HasCompletedReductionOrdinaryComparisonNormalization
    completedReductionSectionEquation at he hcan
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let L := (completedReductionLevel Y d n).obj M
  let cB := @asIso _ _ _ _ (completedCoefficientMap g d) (coefficientMap_isIso g d)
  apply (cancel_epi ((exactPullbackIso g d).inv.app L)).mp
  apply ((proEtaleRingModuleAdjunction g (pbcAdicCompletion Y d)
    (pbcAdicCompletion X d) cB).homEquiv _ _).injective
  apply quotientUnit_hom_ext Y (completedReductionProjection Y d n)
    (fun U ↦ projection_surjective d Y n U) M
  intro W m
  cases W with
  | op V =>
    let N := (reductionChange Y (completedReductionProjection Y d n) ⋙
      completedReductionFiniteModules g d n ⋙
        SheafOfModules.restrictScalars.{u + 1}
          ((adicLisseForget X).map (completedReductionProjection X d n))).obj M
    have h₁ := ringAdjunction_generator g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      cB L N ((exactPullbackIso g d).inv.app L ≫ e.hom.app M) V
      (reductionTensorSection Y (completedReductionProjection Y d n) M (op V) 1 m)
    have h₂ := ringAdjunction_generator g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      cB L N ((exactPullbackIso g d).inv.app L ≫ (ordinaryIsoCandidate g d n).hom.app M) V
      (reductionTensorSection Y (completedReductionProjection Y d n) M (op V) 1 m)
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    let W := op ((proEtaleBaseChange g).obj V)
    let x := completedReductionInverseImageGenerator.{u} g (pbcAdicCompletion Y d)
      L V ((proEtaleBaseChange g).obj V) (𝟙 _)
      (reductionTensorSection Y (completedReductionProjection Y d n) M (op V) 1 m)
    change (e.hom.app M).val.app W
        (((exactPullbackIso g d).inv.app L).val.app W (ringTensor g _ _ cB L W 1 x)) =
      ((ordinaryIsoCandidate g d n).hom.app M).val.app W
        (((exactPullbackIso g d).inv.app L).val.app W (ringTensor g _ _ cB L W 1 x))
    have hx := exactPullbackIso_inv_tensor g d L W 1 x
    have hn₁ := he M V ((proEtaleBaseChange g).obj V) (𝟙 _) 1 m
    have hn₂ := hcan M V ((proEtaleBaseChange g).obj V) (𝟙 _) 1 m
    have hu : (((completedReductionModuleUnit d Y).app M).app (op n)).val.app (op V) m =
        reductionTensorSection Y (completedReductionProjection Y d n) M (op V) 1 m :=
      (completedReductionModuleUnit_exists d Y).exists.choose_spec M n (op V) m
    erw [hu] at hn₁ hn₂
    exact (congrArg ((e.hom.app M).val.app W) hx).trans
      ((hn₁.trans hn₂.symm).trans
        (congrArg (((ordinaryIsoCandidate g d n).hom.app M).val.app W) hx).symm)

end OrdinaryComparison

/-- The ordinary finite comparison is fixed on inverse images of the quotient unit.
Source: blueprint finite evaluation (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: send b tensor the inverse image of (m tensor z) to pi(b) times the pullback
of z tensor the inverse image of (1 tensor m). The coefficient-map projection
identity makes this balanced. The inverse inserts 1 in the completed scalar factor.
The quotient unit sends m to m tensor 1. Balancing determines the map from its
values on these generators, and both maps respect restrictions. Sheafification
extends them uniquely. The same formula commutes with maps of M and with quotients. -/
theorem completedReductionOrdinaryComparison_exists (n : ℕ) :
    ∃! e : completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n)),
      HasCompletedReductionOrdinaryComparisonNormalization g d n e := by
  refine ⟨ordinaryIsoCandidate g d n, ordinaryIsoCandidate_normalized g d n, ?_⟩
  exact fun e he ↦ ordinaryIsoCandidate_unique g d n e he

/-- The finite comparison with its unique local generator normalization.
Source: blueprint finite evaluation (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionOrdinaryComparison (n : ℕ) :
    completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n)) :=
  (completedReductionOrdinaryComparison_exists g d n).exists.choose

/-- Compose two universal complex computations and one exact localization comparison.
The specified components allow the model map and its naturality proof to share data.
Source: transport of universal derived counits
(blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionCompositeCounitNat
    {B C D E : Type*} [Category* B] [Category* C] [Category* D] [Category* E]
    [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E]
    (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (LF : DerivedCategory B ⥤ DerivedCategory C)
    (LG : DerivedCategory C ⥤ DerivedCategory D)
    (εF : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ (LF ⋙ LG ⋙ H.mapDerivedCategory) ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⋙
        H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := H.mapDerivedCategory.map
    (LG.map (Functor.leftDerivedCounitOnComplex F LF εF P) ≫
      Functor.leftDerivedCounitOnComplex G LG εG
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    H.mapDerivedCategoryFactors.hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
  naturality P P' f := by
    let qF := HomotopyCategory.quotient B (.up ℤ)
    let qG := HomotopyCategory.quotient C (.up ℤ)
    let jF : qF ⋙ (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso C)
    let jG : qG ⋙ (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
        G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
    let cF : DerivedCategory.Q ⋙ LF ⟶
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso B).inv LF ≫
        (Functor.associator qF DerivedCategory.Qh LF).hom ≫
          Functor.whiskerLeft qF εF ≫ jF.hom
    let cG : DerivedCategory.Q ⋙ LG ⟶
        G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv LG ≫
        (Functor.associator qG DerivedCategory.Qh LG).hom ≫
          Functor.whiskerLeft qG εG ≫ jG.hom
    have hF (V : CochainComplex B ℤ) :
        cF.app V = Functor.leftDerivedCounitOnComplex F LF εF V := by
      simp [cF, jF, qF, Functor.leftDerivedCounitOnComplex]
    have hG (V : CochainComplex C ℤ) :
        cG.app V = Functor.leftDerivedCounitOnComplex G LG εG V := by
      simp [cG, jG, qG, Functor.leftDerivedCounitOnComplex]
    let ρ := Functor.whiskerRight
      (Functor.whiskerRight cF LG ≫
        Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) cG) H.mapDerivedCategory ≫
      Functor.whiskerLeft
        (F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ))
        H.mapDerivedCategoryFactors.hom
    have hn := ρ.naturality f
    dsimp only [Functor.comp_map, Functor.comp_obj]
    simp only [Functor.map_comp, Category.assoc]
    simpa only [ρ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      hF, hG, Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc] using hn

/-- The universal comparison from the pulled derived reduction tower to its ordinary
computation on a complex. This retains the actual strict tower counits.
Source: blueprint finite projections (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionPulledModelMap (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj
      ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj
        (DerivedCategory.Q.obj P))) ⟶
    DerivedCategory.Q.obj
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj
          (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
            (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex
              (.up ℤ)).obj P))) := by
  letI := completedReductionModuleTowerFunctor_additive Y d
  letI := completedTowerModulePullback_additive g d
  exact (completedReductionCompositeCounitNat (completedReductionModuleTowerFunctor Y d)
    (completedTowerModulePullback g d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
    (completedReductionTower Y d) (completedTowerPullback g d)
    (completedReductionTowerCounit d Y) (completedTowerPullbackCounit g d)).app P

/-- The finite target's canonical comparison with a K-flat computation.
Source: blueprint finite coefficients (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteModelMap (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :=
  (completedReductionFiniteDerived g d n).map
    (pbcComplexCounit (completedReductionProjection Y d n) P) ≫
      (completedReductionFiniteModules g d n).mapDerivedCategoryFactors.hom.app
        (((reductionChange Y (completedReductionProjection Y d n)).mapHomologicalComplex
          (.up ℤ)).obj P)

/-- The representative normalization specifying the derived finite evaluation comparison uniquely.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def HasCompletedReductionFiniteEvaluationNormalization (n : ℕ)
    (e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n)) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
        completedReductionPulledModelMap g d n P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (completedReductionOrdinaryComparison g d n).hom (.up ℤ)).app P) =
          e.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict (completedReductionProjection X d n)).map
              (completedReductionFiniteModelMap g d n P) ≫
            (completedReductionRestrictionFactors X (completedReductionProjection X d n)).hom.app
                (((completedReductionFiniteModules g d n).mapHomologicalComplex (.up ℤ)).obj
                  (((reductionChange Y
                    (completedReductionProjection Y d n)).mapHomologicalComplex
                      (.up ℤ)).obj P))

attribute [irreducible] HasCompletedReductionFiniteEvaluationNormalization

section DerivedComparisons
attribute [local irreducible] completedReductionModuleTowerFunctor completedReductionTower
attribute [local irreducible] completedTowerModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh

/-- Descend an ordinary map through invertible computations on a resolving class. -/
private theorem completedReduction_descend_map
    {B D : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [Category* D]
    (good : CochainComplex B ℤ → Prop)
    (res : ∀ P, ∃ (V : CochainComplex B ℤ) (v : V ⟶ P), good V ∧ QuasiIso v)
    (H J : DerivedCategory B ⥤ D) (E F : CochainComplex B ℤ ⥤ D)
    (α : DerivedCategory.Q ⋙ H ⟶ E) (β : DerivedCategory.Q ⋙ J ⟶ F)
    (hβ : ∀ P, good P → IsIso (β.app P)) (v : E ⟶ F) :
    ∃! τ : H ⟶ J, ∀ P, good P →
      α.app P ≫ v.app P = τ.app (DerivedCategory.Q.obj P) ≫ β.app P := by
  let P : ObjectProperty (CochainComplex B ℤ) := good
  let L := P.ι ⋙ DerivedCategory.Q
  let ff := _root_.cochainRepresentativeWhiskering good res D
  let αP := Functor.whiskerLeft P.ι α
  let βP := Functor.whiskerLeft P.ι β
  have : ∀ V : P.FullSubcategory, IsIso (βP.app V) :=
    fun V ↦ hβ V.obj V.property
  have : IsIso βP := NatIso.isIso_of_isIso_app βP
  let t : L ⋙ H ⟶ L ⋙ J :=
    αP ≫ Functor.whiskerLeft P.ι v ≫ inv βP
  let τ : H ⟶ J := ff.preimage t
  have ht (V : P.FullSubcategory) : τ.app (DerivedCategory.Q.obj V.obj) = t.app V :=
    congr_app (ff.map_preimage t) V
  have hτ (V : CochainComplex B ℤ) (hV : good V) :
      α.app V ≫ v.app V = τ.app (DerivedCategory.Q.obj V) ≫ β.app V := by
    rw [ht ⟨V, hV⟩]
    change α.app V ≫ v.app V =
      (α.app V ≫ v.app V ≫ (inv βP).app ⟨V, hV⟩) ≫ β.app V
    have he := congr_app (IsIso.inv_hom_id βP) ⟨V, hV⟩
    change (inv βP).app ⟨V, hV⟩ ≫ β.app V = 𝟙 _ at he
    simp only [Category.assoc, he]
    exact congrArg (fun z ↦ α.app V ≫ z) (Category.comp_id (v.app V)).symm
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply ff.map_injective
  ext V
  have : IsIso (β.app V.obj) := hβ V.obj V.property
  apply (cancel_mono (β.app V.obj)).mp
  exact (hτ' V.obj V.property).symm.trans (hτ V.obj V.property)

/-- Descent of a termwise transition, retaining its factored component formula. -/
private theorem completedReduction_descend_composite
    {B C C' D' D : Type*}
    [Category* B] [Category* C] [Category* C'] [Category* D'] [Category* D]
    [Abelian B] [Abelian C] [Abelian C'] [Abelian D'] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D'] [HasDerivedCategory D]
    (good : CochainComplex B ℤ → Prop)
    (res : ∀ P, ∃ (V : CochainComplex B ℤ) (v : V ⟶ P), good V ∧ QuasiIso v)
    (F : B ⥤ C) (G : C ⥤ D) (F' : B ⥤ C') (G' : C' ⥤ D') (R : D' ⥤ D)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive] [R.Additive]
    (H : DerivedCategory B ⥤ DerivedCategory D)
    (J : DerivedCategory B ⥤ DerivedCategory D')
    (S : DerivedCategory D' ⥤ DerivedCategory D)
    (α : DerivedCategory.Q ⋙ H ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (γ : DerivedCategory.Q ⋙ J ⟶
      F'.mapHomologicalComplex (.up ℤ) ⋙ G'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ S ≅ R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hγ : ∀ P, good P → IsIso (γ.app P))
    (t : F ⋙ G ⟶ F' ⋙ G' ⋙ R) :
    ∃! τ : H ⟶ J ⋙ S, ∀ P, good P →
      α.app P ≫ DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app P) =
        τ.app (DerivedCategory.Q.obj P) ≫ S.map (γ.app P) ≫
          δ.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj
            ((F'.mapHomologicalComplex (.up ℤ)).obj P)) := by
  let E := F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q
  let E' := F'.mapHomologicalComplex (.up ℤ) ⋙ G'.mapHomologicalComplex (.up ℤ)
  let β : DerivedCategory.Q ⋙ (J ⋙ S) ⟶
      E' ⋙ R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight γ S ≫ Functor.whiskerLeft E' δ.hom
  have hβ P (hP : good P) : IsIso (β.app P) := by
    have := hγ P hP
    change IsIso (S.map (γ.app P) ≫ δ.hom.app _)
    infer_instance
  let v : E ⟶ E' ⋙ R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q
  exact completedReduction_descend_map good res H (J ⋙ S) E _ α β hβ v

/-- The finite computation is natural in the cochain representative. -/
private def completedReductionFiniteModelNat (n : ℕ) :
    DerivedCategory.Q ⋙ completedReductionFiniteTarget g d n ⟶
      (reductionChange Y (completedReductionProjection Y d n)).mapHomologicalComplex (.up ℤ) ⋙
        (completedReductionFiniteModules g d n).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q where
  app P := completedReductionFiniteModelMap g d n P
  naturality P P' f := by
    let ρ := Functor.whiskerRight
      (complexCounitNat (pbcExtend (completedReductionProjection Y d n))
        (pbcDerivedExtend (completedReductionProjection Y d n))
        (pbcExtensionCounit (completedReductionProjection Y d n)))
      (completedReductionFiniteDerived g d n) ≫
        Functor.whiskerLeft
          ((reductionChange Y (completedReductionProjection Y d n)).mapHomologicalComplex
            (.up ℤ))
          (completedReductionFiniteModules g d n).mapDerivedCategoryFactors.hom
    have hn := ρ.naturality f
    simp only [ρ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      complexCounitNat_app] at hn
    exact hn

/-- K-flat representatives compute the finite target. -/
private theorem completedReductionFiniteModelMap_isIso (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := pbcAdicCompletion Y d) P) :
    IsIso (completedReductionFiniteModelMap.{u} g d n P) := by
  have := pbcExtensionCounit_isIso.{u} (completedReductionProjection Y d n) P hP
  unfold completedReductionFiniteModelMap pbcComplexCounit
  infer_instance

private theorem completedReductionPullback_preservesFiniteLimits :
    PreservesFiniteLimits (completedModulePullback g d) := by
  exact preservesFiniteLimits_of_natIso (exactPullbackIso g d).symm

private theorem completedReductionPullback_preservesFiniteColimits :
    PreservesFiniteColimits (completedModulePullback g d) := by
  exact preservesFiniteColimits_of_natIso (exactPullbackIso g d).symm

private theorem completedReductionTowerPullback_preservesFiniteLimits :
    PreservesFiniteLimits (completedTowerModulePullback g d) := by
  let := completedReductionPullback_preservesFiniteLimits g d
  unfold completedTowerModulePullback
  constructor
  intro J _ _
  infer_instance

private theorem completedReductionTowerPullback_preservesFiniteColimits :
    PreservesFiniteColimits (completedTowerModulePullback g d) := by
  let := completedReductionPullback_preservesFiniteColimits g d
  unfold completedTowerModulePullback
  constructor
  intro J _ _
  infer_instance

/-- An exact functor's universal derived counit is invertible on every complex. -/
private theorem completedReduction_exactCounit_isIso
    {B D : Type*} [Category* B] [Category* D] [Abelian B] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))]
    (P : CochainComplex B ℤ) :
    IsIso (Functor.leftDerivedCounitOnComplex F L ε P) := by
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  have hi : W.IsInvertedBy (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    apply (MorphismProperty.IsInvertedBy.iff_of_iso W F.mapDerivedCategoryFactorsh).mp
    exact MorphismProperty.IsInvertedBy.of_comp _ _ (Localization.inverts _ W)
      F.mapDerivedCategory
  have : IsIso ε := Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _ hi
  unfold Functor.leftDerivedCounitOnComplex
  infer_instance

/-- Exact tower pullback is already its own derived functor on every complex. -/
private theorem completedReductionPullbackCounit_isIso
    (P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :
    IsIso (completedTowerPullbackComplexCounit g d P) := by
  let := completedReductionTowerPullback_preservesFiniteLimits g d
  let := completedReductionTowerPullback_preservesFiniteColimits g d
  have hLF : (completedTowerPullback g d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
    unfold completedTowerPullback completedTowerPullbackCounit
    exact (completedTowerPullback_exists g d).choose_spec.choose_spec.1
  let := hLF
  exact completedReduction_exactCounit_isIso (completedTowerModulePullback g d)
    (completedTowerPullback g d) (completedTowerPullbackCounit g d) P

/-- The pulled finite computation is natural in the cochain representative. -/
private def completedReductionPulledModelNat (n : ℕ) :
    DerivedCategory.Q ⋙ (completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
      pbcTowerEvaluation X (pbcAdicCompletion X d) n) ⟶
    (completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ) ⋙
      (completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ) ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
          (op n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let := completedReductionModuleTowerFunctor_additive Y d
  let := completedTowerModulePullback_additive g d
  exact completedReductionCompositeCounitNat (completedReductionModuleTowerFunctor Y d)
    (completedTowerModulePullback g d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
    (completedReductionTower Y d) (completedTowerPullback g d)
    (completedReductionTowerCounit d Y) (completedTowerPullbackCounit g d)

/-- Invertible computations remain invertible after two functors and composition. -/
private theorem completedReduction_invertibleComposite
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    (F : B ⥤ C) (G : C ⥤ D) {x y : B} {z : C} {w : D}
    (α : x ⟶ y) (β : F.obj y ⟶ z) (γ : G.obj z ⟶ w)
    (hα : IsIso α) (hβ : IsIso β) (hγ : IsIso γ) :
    IsIso (G.map (F.map α ≫ β) ≫ γ) := by
  let := hα
  let := hβ
  let := hγ
  infer_instance

/-- The primitive complex counit is invertible when its homotopy component is. -/
private theorem completedReduction_complexCounit_isIso
    {B D : Type*} [Category* B] [Category* D] [Abelian B] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    (F : B ⥤ D) [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex B ℤ)
    (hε : IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P))) :
    IsIso (Functor.leftDerivedCounitOnComplex F L ε P) := by
  let := hε
  unfold Functor.leftDerivedCounitOnComplex
  infer_instance

/-- Invertibility of the composite computation is checked before specialization. -/
private theorem completedReductionCompositeCounitNat_isIso
    {B C D E : Type*} [Category* B] [Category* C] [Category* D] [Category* E]
    [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E]
    (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (LF : DerivedCategory B ⥤ DerivedCategory C)
    (LG : DerivedCategory C ⥤ DerivedCategory D)
    (εF : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex B ℤ)
    (hF : IsIso (Functor.leftDerivedCounitOnComplex F LF εF P))
    (hG : IsIso (Functor.leftDerivedCounitOnComplex G LG εG
      ((F.mapHomologicalComplex (.up ℤ)).obj P))) :
    IsIso ((completedReductionCompositeCounitNat F G H LF LG εF εG).app P) := by
  exact completedReduction_invertibleComposite LG H.mapDerivedCategory _ _ _ hF hG
    (by infer_instance)

/-- The pulled computation is invertible on K-flat coefficient representatives. -/
private theorem completedReductionPulledModelNat_isIso (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := pbcAdicCompletion Y d) P) :
    IsIso ((completedReductionPulledModelNat g d n).app P) := by
  let := completedReductionModuleTowerFunctor_additive Y d
  let := completedTowerModulePullback_additive g d
  have hε : IsIso ((completedReductionTowerCounit d Y).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (completedReductionTower_properties Y d).2.2 P hP
  have hα := completedReduction_complexCounit_isIso
    (completedReductionModuleTowerFunctor Y d) (completedReductionTower Y d)
    (completedReductionTowerCounit d Y) P hε
  exact completedReductionCompositeCounitNat_isIso
    (completedReductionModuleTowerFunctor Y d) (completedTowerModulePullback g d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
    (completedReductionTower Y d) (completedTowerPullback g d)
    (completedReductionTowerCounit d Y) (completedTowerPullbackCounit g d) P hα
    (completedReductionPullbackCounit_isIso g d
      (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ)).obj P))

/-- Descent through a resolving class reflects invertibility as well as uniqueness. -/
private theorem completedReduction_descend_iso
    {B D : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [Category* D]
    (good : CochainComplex B ℤ → Prop)
    (res : ∀ P, ∃ (V : CochainComplex B ℤ) (v : V ⟶ P), good V ∧ QuasiIso v)
    (H J : DerivedCategory B ⥤ D) (E F : CochainComplex B ℤ ⥤ D)
    (α : DerivedCategory.Q ⋙ H ⟶ E) (β : DerivedCategory.Q ⋙ J ⟶ F)
    (hα : ∀ P, good P → IsIso (α.app P))
    (hβ : ∀ P, good P → IsIso (β.app P)) (v : E ≅ F) :
    ∃! e : H ≅ J, ∀ P, good P →
      α.app P ≫ v.hom.app P = e.hom.app (DerivedCategory.Q.obj P) ≫ β.app P := by
  obtain ⟨τ, hτ, huniq⟩ := completedReduction_descend_map good res H J E F α β hβ v.hom
  let ff := _root_.cochainRepresentativeWhiskering good res D
  have hτiso (P : (ObjectProperty.FullSubcategory good)) :
      IsIso (τ.app (DerivedCategory.Q.obj P.obj)) := by
    have := hα P.obj P.property
    have := hβ P.obj P.property
    have : IsIso (τ.app (DerivedCategory.Q.obj P.obj) ≫ β.app P.obj) := by
      rw [← hτ P.obj P.property]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (β.app P.obj)
  have hmap : IsIso
      (((Functor.whiskeringLeft _ _ D).obj
        (ObjectProperty.ι good ⋙ DerivedCategory.Q)).map τ) := by
    have : ∀ P : ObjectProperty.FullSubcategory good,
        IsIso ((Functor.whiskerLeft (ObjectProperty.ι good ⋙ DerivedCategory.Q) τ).app P) :=
      fun P ↦ hτiso P
    change IsIso (Functor.whiskerLeft (ObjectProperty.ι good ⋙ DerivedCategory.Q) τ)
    exact NatIso.isIso_of_isIso_app _
  have : IsIso τ := ff.isIso_of_isIso_map τ
  refine ⟨asIso τ, hτ, ?_⟩
  intro e he
  exact Iso.ext (huniq e.hom he)

/-- Descent retains the ordinary comparison and the exact restriction formula. -/
private theorem completedReduction_descend_comparison_iso
    {B C D E C' D' : Type*}
    [Category* B] [Category* C] [Category* D] [Category* E]
    [Category* C'] [Category* D']
    [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian C'] [Abelian D']
    [HasDerivedCategory B] [HasDerivedCategory E] [HasDerivedCategory D']
    (good : CochainComplex B ℤ → Prop)
    (res : ∀ P, ∃ (V : CochainComplex B ℤ) (v : V ⟶ P), good V ∧ QuasiIso v)
    (F : B ⥤ C) (G : C ⥤ D) (T : D ⥤ E)
    (F' : B ⥤ C') (G' : C' ⥤ D') (R : D' ⥤ E)
    [F.Additive] [G.Additive] [T.Additive] [F'.Additive] [G'.Additive] [R.Additive]
    (H : DerivedCategory B ⥤ DerivedCategory E)
    (J : DerivedCategory B ⥤ DerivedCategory D')
    (S : DerivedCategory D' ⥤ DerivedCategory E)
    (α : DerivedCategory.Q ⋙ H ⟶ F.mapHomologicalComplex (.up ℤ) ⋙
      G.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (γ : DerivedCategory.Q ⋙ J ⟶
      F'.mapHomologicalComplex (.up ℤ) ⋙ G'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ S ≅ R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hα : ∀ P, good P → IsIso (α.app P))
    (hγ : ∀ P, good P → IsIso (γ.app P)) (t : F ⋙ G ⋙ T ≅ F' ⋙ G' ⋙ R) :
    ∃! e : H ≅ J ⋙ S, ∀ P, good P →
      α.app P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app P) =
        e.hom.app (DerivedCategory.Q.obj P) ≫ S.map (γ.app P) ≫
          δ.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj
            ((F'.mapHomologicalComplex (.up ℤ)).obj P)) := by
  let E' := F'.mapHomologicalComplex (.up ℤ) ⋙ G'.mapHomologicalComplex (.up ℤ)
  let β := Functor.whiskerRight γ S ≫ Functor.whiskerLeft E' δ.hom
  have hβ P (hP : good P) : IsIso (β.app P) := by
    have := hγ P hP
    change IsIso (S.map (γ.app P) ≫ δ.hom.app _)
    infer_instance
  exact completedReduction_descend_iso good res H (J ⋙ S) _ _ α β hα hβ
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q)

/-- The finite evaluation comparison is the descent of the specified ordinary map.
Thus it cannot be changed by an automorphism of the finite target.
Source: blueprint order 1262 (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: take a flat-term K-flat representative. The constant/completed comparison
computes the pulled reduction tower at each finite level by ordinary pullback.
Apply completedReductionOrdinaryComparison and the exact restriction comparison.
All quasi-isomorphisms between these models are inverted. Naturality and the
universal counits descend the comparison uniquely, with the displayed equation. -/
theorem completedReductionFiniteEvaluation_exists (n : ℕ) :
    ∃! e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n),
      HasCompletedReductionFiniteEvaluationNormalization g d n e := by
  let := completedReductionModuleTowerFunctor_additive Y d
  let := completedTowerModulePullback_additive g d
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let good := fun P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ ↦
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := pbcAdicCompletion Y d) P
  have res (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
      ∃ (V : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) (v : V ⟶ P),
        good V ∧ QuasiIso v := by
    obtain ⟨V, v, hV, _, hv, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (R := pbcAdicCompletion Y d) P
    exact ⟨V, v, hV, hv⟩
  unfold HasCompletedReductionFiniteEvaluationNormalization
  exact completedReduction_descend_comparison_iso good res
    (completedReductionModuleTowerFunctor Y d) (completedTowerModulePullback g d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
    (reductionChange Y (completedReductionProjection Y d n))
    (completedReductionFiniteModules g d n)
    (pbcRestrict (completedReductionProjection X d n)) _ _ _
    (completedReductionPulledModelNat g d n) (completedReductionFiniteModelNat g d n)
    (completedReductionRestrictionFactors X (completedReductionProjection X d n))
    (fun P hP ↦ completedReductionPulledModelNat_isIso g d n P hP)
    (fun P hP ↦ completedReductionFiniteModelMap_isIso g d n P hP)
    (completedReductionOrdinaryComparison g d n)

end DerivedComparisons

/-- The canonical finite evaluation isomorphism fixed by the complex computation.
Source: blueprint order 1262 (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteEvaluation (n : ℕ) :
    completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n) :=
  (completedReductionFiniteEvaluation_exists g d n).exists.choose

/-- The projection-induced reduction arrow is the scalar-extension adjunct of the
actual derived-limit projection, followed by the normalized finite evaluation map.
Source: blueprint alpha_n (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedPullbackReductionArrow
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (n : ℕ) :
    (reductionDerivedChange X (completedReductionProjection X d n)).obj
        (completedPullbackObject g d K) ⟶ (completedReductionFiniteTarget g d n).obj K :=
  ((pbcDerivedScalarAdjunction (completedReductionProjection X d n)).homEquiv _ _).symm
    ((completedReductionLimitProjection d (X := X) n).app
        ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
      (completedReductionFiniteEvaluation g d n).hom.app K)

/-- The sectionwise normalization specifying the ordinary quotient transition uniquely.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def HasCompletedReductionOrdinaryTransitionNormalization (a b : ℕ) (h : a ≤ b)
    (τ : reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h))) : Prop :=
  ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
        (f : U ⟶ (proEtaleBaseChange g).obj V)
        (s : (reductionCoefficient X d b).obj.obj (op U))
        (z : (reductionCoefficient Y d b).obj.obj (op V))
        (m : M.val.obj (op V)),
        completedReductionSectionEquation X (reductionCoefficientMap X d b a h)
          (τ.app M) (op U) (completedReductionFiniteGenerator g d b M V U f s z m)
          (completedReductionFiniteGenerator g d a M V U f
            ((reductionCoefficientMap X d b a h).hom.app (op U) s)
            ((reductionCoefficientMap Y d b a h).hom.app (op V) z) m)

attribute [irreducible] HasCompletedReductionOrdinaryTransitionNormalization

section OrdinaryTransition
variable (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
private theorem inverseImageGenerator_map {M N : pbcModules Y R} (a : M ⟶ N)
    (V : Y.ProEt) (U : X.ProEt) (f : U ⟶ (proEtaleBaseChange g).obj V)
    (m : M.val.obj (op V)) :
    (((proEtaleModuleInverseImage g R).map a).val.app (op U))
      (completedReductionInverseImageGenerator.{u} g R M V U f m) =
    completedReductionInverseImageGenerator.{u} g R N V U f (a.val.app (op V) m) := by
  let adj := @SheafOfModules.pullbackPushforwardAdjunction.{u + 1} _ _ _ _ _ _ _ _ _
    (proEtaleModelBaseChange_isContinuous g) (proEtaleModelRingUnit g R)
    (completedReductionModelPushforward_isRightAdjoint g R)
  let am := (proEtaleModuleToModel ((adicLisseForget Y).obj R)).map a
  have hn := congrArg (fun t ↦ t.val.app (op (AsSmall.up.obj V)) m)
    (adj.unit.naturality am)
  let x := (adj.unit.app ((proEtaleModuleToModel ((adicLisseForget Y).obj R)).obj M)).val.app
    (op (AsSmall.up.obj V)) m
  have hr := PresheafOfModules.naturality_apply
    ((proEtaleModuleInverseImage g R).map a).val f.op x
  unfold completedReductionInverseImageGenerator
  rw [hr]
  exact congrArg (((proEtaleModuleInverseImage g R).obj N).val.map f.op) hn.symm

private theorem ringTensor_map {M N : pbcModules Y R} (a : M ⟶ N)
    (U : X.ProEtᵒᵖ) (b : S.obj.obj U)
    (m : ((proEtaleModuleInverseImage g R).obj M).val.obj U) :
    (((proEtaleRingModulePullback g R S c).map a).val.app U)
      (ringTensor g R S c M U b m) =
    ringTensor g R S c N U b (((proEtaleModuleInverseImage g R).map a).val.app U m) := by
  let pre : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
      ((proEtaleModuleInverseImage g R).obj M) ⟶
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
      ((proEtaleModuleInverseImage g R).obj N) :=
    { app := fun W ↦ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.hom.app W).hom).map
        (((proEtaleModuleInverseImage g R).map a).val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturality c.hom _
        ((proEtaleModuleInverseImage g R).map a) }
  have hn := congrArg (fun t ↦ t.app U (b ⊗ₜ[_, (c.hom.hom.app U).hom] m))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((adicLisseForget X).obj S).obj)).unit.naturality pre)
  change
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((adicLisseForget X).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
          ((proEtaleModuleInverseImage g R).obj N))).app U
            ((ModuleCat.extendScalars (c.hom.hom.app U).hom).map
              (((proEtaleModuleInverseImage g R).map a).val.app U)
              (b ⊗ₜ[_, (c.hom.hom.app U).hom] m)) =
      ((PresheafOfModules.sheafification
        (𝟙 ((adicLisseForget X).obj S).obj)).map pre).val.app U
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((adicLisseForget X).obj S).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
                ((proEtaleModuleInverseImage g R).obj M))).app U
                  (b ⊗ₜ[_, (c.hom.hom.app U).hom] m)) at hn
  rw [ModuleCat.ExtendScalars.map_tmul] at hn
  exact hn.symm

private theorem ringGenerator_map {M N : pbcModules Y R} (a : M ⟶ N)
    (V : Y.ProEt) (U : X.ProEt) (f : U ⟶ (proEtaleBaseChange g).obj V)
    (b : S.obj.obj (op U)) (m : M.val.obj (op V)) :
    (((proEtaleRingModulePullback g R S c).map a).val.app (op U))
      (ringTensor g R S c M (op U) b
        (completedReductionInverseImageGenerator.{u} g R M V U f m)) =
      ringTensor g R S c N (op U) b
        (completedReductionInverseImageGenerator.{u} g R N V U f (a.val.app (op V) m)) := by
  rw [ringTensor_map, inverseImageGenerator_map]

private theorem finiteStepMap_exists (X : Scheme.{u})
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : R ⟶ T) (q : S ⟶ T) (hcomp : φ ≫ q = ψ)
    (M : reductionModules X R) (unitMap : M ⟶ (reductionRestrict X ψ).obj
      ((reductionChange X ψ).obj M))
    (hunit : ∀ (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      unitMap.val.app U x = reductionTensorSection X ψ M U 1 x) :
    ∃ b : (reductionChange X φ).obj M ⟶
        (reductionRestrict X q).obj ((reductionChange X ψ).obj M),
      ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        b.val.app U (reductionTensorSection X φ M U s x) =
          reductionTensorSection X ψ M U (q.hom.app U s) x := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  let N := (reductionRestrict X q).obj ((reductionChange X ψ).obj M)
  have hq (U : X.ProEtᵒᵖ) (r : R.obj.obj U) :
      q.hom.app U (φ.hom.app U r) = ψ.hom.app U r :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hcomp) r
  let ua := (PresheafOfModules.toPresheaf (reductionModuleRing X R).obj).map unitMap.val
  let a : M ⟶ (reductionRestrict X φ).obj N :=
    ⟨PresheafOfModules.homMk ua (by
        intro U r x
        have h := (unitMap.val.app U).hom.map_smul r x
        change unitMap.val.app U (r • x) =
          q.hom.app U (φ.hom.app U r) •
            (show ((reductionChange X ψ).obj M).val.obj U from unitMap.val.app U x)
        rw [hq]
        exact h)⟩
  let adj := (ordinaryAdjunction_exists X φ).choose
  let b : (reductionChange X φ).obj M ⟶ N := (adj.homEquiv M N).symm a
  refine ⟨b, ?_⟩
  intro U s x
  have hb : b.val.app U (reductionTensorSection X φ M U 1 x) = a.val.app U x := by
    have hh := (ordinaryAdjunction_exists X φ).choose_spec M N b U x
    rw [Equiv.apply_symm_apply] at hh
    exact (eq_of_heq hh).symm
  have ht := tensorSection_smul X φ M U s 1 x
  rw [mul_one] at ht
  rw [← ht, map_smul, hb]
  change q.hom.app U s •
    (show ((reductionChange X ψ).obj M).val.obj U from unitMap.val.app U x) = _
  rw [hunit, tensorSection_smul, mul_one]

private theorem restriction_faithful (T : Scheme.{u})
    {B D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : B ⟶ D) :
    (reductionRestrict T φ).Faithful where
  map_injective {_ _ f k} h := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.restrictScalars (((adicLisseForget T).map φ).hom)).map_injective
    exact congrArg (fun t ↦ t.val) h

private theorem finiteScalarTransition_exists (T : Scheme.{u})
    {B D E : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : B ⟶ D) (ψ : B ⟶ E) (q : D ⟶ E) (hcomp : φ ≫ q = ψ) :
    ∃! τ : reductionChange T φ ⟶ reductionChange T ψ ⋙ reductionRestrict T q,
      ∀ (M : reductionModules T B) (U : T.ProEtᵒᵖ)
        (s : D.obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection T φ M U s x) =
          reductionTensorSection T ψ M U (q.hom.app U s) x := by
  let := restriction_faithful T φ
  let f (M : reductionModules T B) :=
    (finiteStepMap_exists T φ ψ q hcomp M (reductionUnit T ψ M)
      (reductionUnit_apply T ψ M)).choose
  have hf (M : reductionModules T B) :=
    (finiteStepMap_exists T φ ψ q hcomp M (reductionUnit T ψ M)
      (reductionUnit_apply T ψ M)).choose_spec
  let τ : reductionChange T φ ⟶ reductionChange T ψ ⋙ reductionRestrict T q :=
    { app := f
      naturality := by
        intro M N k
        apply (reductionRestrict T φ).map_injective
        apply level_hom_ext T φ M
          ((reductionRestrict T φ).obj ((reductionRestrict T q).obj
            ((reductionChange T ψ).obj N)))
        intro U s x
        change (f N).val.app U (((reductionChange T φ).map k).val.app U
            (reductionTensorSection T φ M U s x)) =
          ((reductionChange T ψ).map k).val.app U ((f M).val.app U
            (reductionTensorSection T φ M U s x))
        rw [reductionTensor_map, hf, hf, reductionTensor_map] }
  refine ⟨τ, ?_, ?_⟩
  · intro M U s x
    exact hf M U s x
  · intro τ' hτ'
    apply NatTrans.ext
    funext M
    apply (reductionRestrict T φ).map_injective
    apply level_hom_ext T φ M
      ((reductionRestrict T φ).obj ((reductionRestrict T q).obj
        ((reductionChange T ψ).obj M)))
    intro U s x
    exact (hτ' M U s x).trans (hf M U s x).symm

private theorem ringReducedTransition_exists
    (R' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aR : R ⟶ R') (aS : S ⟶ S')
    (c' : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R' ≅ S')
    (hc : c.hom ≫ aS = (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aR ≫ c'.hom)
    (B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (φ : B ⟶ R) (ψ : B ⟶ R') (hφ : φ ≫ aR = ψ) :
    ∃! τ : reductionChange Y φ ⋙ proEtaleRingModulePullback g R S c ⟶
      reductionChange Y ψ ⋙ proEtaleRingModulePullback g R' S' c' ⋙
        SheafOfModules.restrictScalars.{u + 1} ((adicLisseForget X).map aS),
      ∀ (M : pbcModules Y B) (V : Y.ProEt) (U : X.ProEt)
        (f : U ⟶ (proEtaleBaseChange g).obj V) (s : S.obj.obj (op U))
        (z : R.obj.obj (op V)) (m : M.val.obj (op V)),
        completedReductionSectionEquation X aS (τ.app M) (op U)
          (ringTensor g R S c _ (op U) s
            (completedReductionInverseImageGenerator.{u} g R
              ((reductionChange Y φ).obj M) V U f (reductionTensorSection Y φ M (op V) z m)))
          (ringTensor g R' S' c' _ (op U) (aS.hom.app (op U) s)
            (completedReductionInverseImageGenerator.{u} g R'
              ((reductionChange Y ψ).obj M) V U f
                (reductionTensorSection Y ψ M (op V) (aR.hom.app (op V) z) m))) := by
  unfold completedReductionSectionEquation
  obtain ⟨θ, hθ, _⟩ := finiteScalarTransition_exists Y φ ψ aR hφ
  let k := proEtaleRingRestrictionPullbackInv g R R' S S' aR aS c c' hc
  let τ := Functor.whiskerRight θ (proEtaleRingModulePullback g R S c) ≫
    Functor.whiskerLeft (reductionChange Y ψ) k
  have hτ (M : pbcModules Y B) (V : Y.ProEt) (U : X.ProEt)
      (f : U ⟶ (proEtaleBaseChange g).obj V) (s : S.obj.obj (op U))
      (z : R.obj.obj (op V)) (m : M.val.obj (op V)) :
      (τ.app M).val.app (op U)
        (ringTensor g R S c _ (op U) s
          (completedReductionInverseImageGenerator.{u} g R
            ((reductionChange Y φ).obj M) V U f (reductionTensorSection Y φ M (op V) z m))) =
        ringTensor g R' S' c' _ (op U) (aS.hom.app (op U) s)
          (completedReductionInverseImageGenerator.{u} g R'
            ((reductionChange Y ψ).obj M) V U f
              (reductionTensorSection Y ψ M (op V) (aR.hom.app (op V) z) m)) := by
    simp only [τ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [ringGenerator_map, hθ]
    exact ringRestriction_generator_local g R S c R' S' aR aS c' hc
      ((reductionChange Y ψ).obj M) V U f s _
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext M
  apply ((proEtaleRingModuleAdjunction g R S c).homEquiv _ _).injective
  let := restriction_faithful Y φ
  apply (reductionRestrict Y φ).map_injective
  apply level_hom_ext Y φ M
  intro U z m
  cases U with
  | op V =>
    let adj := proEtaleRingModuleAdjunction g R S c
    change ((adj.homEquiv _ _) (τ'.app M)).val.app (op V)
        (reductionTensorSection Y φ M (op V) z m) =
      ((adj.homEquiv _ _) (τ.app M)).val.app (op V)
        (reductionTensorSection Y φ M (op V) z m)
    rw [ringAdjunction_generator, ringAdjunction_generator]
    exact (hτ' M V ((proEtaleBaseChange g).obj V) (𝟙 _) 1 z m).trans
      (hτ M V ((proEtaleBaseChange g).obj V) (𝟙 _) 1 z m).symm

end OrdinaryTransition

private theorem finiteCoefficient_naturality (a b : ℕ) (h : a ≤ b) :
    completedFiniteCoefficientMap g d b ≫ reductionCoefficientMap X d b a h =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (reductionCoefficientMap Y d b a h) ≫ completedFiniteCoefficientMap g d a := by
  let t : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⟶
      adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence (fun k ↦ (proEtaleConstantComparison g).app
      (CommRingCat.of (A ⧸ d.ideal ^ (k + 1)))) (by
        intro k
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison g).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (k + 1))))
  let s : reductionCoefficientSystem Y d ⋙
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⟶ reductionCoefficientSystem X d :=
    Functor.whiskerRight (pbcConstantSystemComparison Y d).inv
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}) ≫ t ≫
        (pbcConstantSystemComparison X d).hom
  exact (s.naturality (homOfLE h).op).symm

private theorem finiteGenerator_eq (n : ℕ)
    (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
    (f : U ⟶ (proEtaleBaseChange g).obj V)
    (s : (reductionCoefficient X d n).obj.obj (op U))
    (z : (reductionCoefficient Y d n).obj.obj (op V)) (m : M.val.obj (op V)) :
    completedReductionFiniteGenerator g d n M V U f s z m =
      ringTensor g (reductionCoefficient Y d n) (reductionCoefficient X d n)
        (asIso (completedFiniteCoefficientMap g d n))
        ((reductionChange Y (completedReductionProjection Y d n)).obj M) (op U) s
          (completedReductionInverseImageGenerator g (reductionCoefficient Y d n)
            ((reductionChange Y (completedReductionProjection Y d n)).obj M) V U f
              (reductionTensorSection Y (completedReductionProjection Y d n) M (op V) z m)) := by
  unfold completedReductionFiniteGenerator completedReductionFiniteTensor ringTensor
  rfl

/-- The finite quotient transition before localization, fixed on all local generators.
Source: blueprint transition clause (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: apply the quotient to each coefficient in an inverse-image tensor. The square
of finite coefficient structure maps commutes with the quotients, so balancing and
restriction are respected. Local generators determine the map uniquely. Naturality
in the module follows from the same formula. -/
theorem completedReductionOrdinaryTransition_exists (a b : ℕ) (h : a ≤ b) :
    ∃! τ : reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h)),
      HasCompletedReductionOrdinaryTransitionNormalization g d a b h τ := by
  obtain ⟨τ, hτ, huniq⟩ := ringReducedTransition_exists g (reductionCoefficient Y d b)
    (reductionCoefficient X d b) (asIso (completedFiniteCoefficientMap g d b))
    (reductionCoefficient Y d a) (reductionCoefficient X d a)
    (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
    (asIso (completedFiniteCoefficientMap g d a)) (finiteCoefficient_naturality g d a b h)
    (pbcAdicCompletion Y d) (completedReductionProjection Y d b)
    (completedReductionProjection Y d a) (completedReductionProjection_comp Y d b a h)
  refine ⟨τ, ?_, ?_⟩
  · unfold HasCompletedReductionOrdinaryTransitionNormalization
    intro M V U f s z m
    rw [finiteGenerator_eq, finiteGenerator_eq]
    exact hτ M V U f s z m
  · intro τ' hτ'
    unfold HasCompletedReductionOrdinaryTransitionNormalization at hτ'
    apply huniq τ'
    intro M V U f s z m
    have hn := hτ' M V U f s z m
    rw [finiteGenerator_eq, finiteGenerator_eq] at hn
    exact hn

/-- The actual quotient transition on ordinary finite pullback reductions.
Source: blueprint transitions (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionOrdinaryTransition (a b : ℕ) (h : a ≤ b) :
    reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h)) :=
  (completedReductionOrdinaryTransition_exists g d a b h).exists.choose

/-- The representative normalization specifying the derived quotient transition comparison uniquely.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def HasCompletedReductionTargetTransitionNormalization (a b : ℕ) (h : a ≤ b)
    (τ : completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h)) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
        completedReductionFiniteModelMap g d b P ≫ DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (completedReductionOrdinaryTransition g d a b h) (.up ℤ)).app P) =
          τ.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict (reductionCoefficientMap X d b a h)).map
              (completedReductionFiniteModelMap g d a P) ≫
            (completedReductionRestrictionFactors X
              (reductionCoefficientMap X d b a h)).hom.app
                  (((completedReductionFiniteModules g d a).mapHomologicalComplex (.up ℤ)).obj
                    (((reductionChange Y
                      (completedReductionProjection Y d a)).mapHomologicalComplex
                        (.up ℤ)).obj P))

attribute [irreducible] HasCompletedReductionTargetTransitionNormalization

/-- The derived quotient transition, characterized by the universal K-flat comparisons.
Source: blueprint transitions (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: the ordinary quotient formula is natural on K-flat complexes and commutes
with differentials. Both finite pullback and coefficient restriction are exact.
Invert the scalar-extension comparisons on K-flat representatives and descend the
ordinary map. The universal derived comparisons give its unique natural descent. -/
theorem completedReductionTargetTransition_exists (a b : ℕ) (h : a ≤ b) :
    ∃! τ : completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h),
      HasCompletedReductionTargetTransitionNormalization g d a b h τ := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let good := fun P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ ↦
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := pbcAdicCompletion Y d) P
  have res (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
      ∃ (V : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) (v : V ⟶ P),
        good V ∧ QuasiIso v := by
    obtain ⟨V, v, hV, _, hv, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (R := pbcAdicCompletion Y d) P
    exact ⟨V, v, hV, hv⟩
  unfold HasCompletedReductionTargetTransitionNormalization
  exact completedReduction_descend_composite good res
    (reductionChange Y (completedReductionProjection Y d b))
    (completedReductionFiniteModules g d b)
    (reductionChange Y (completedReductionProjection Y d a))
    (completedReductionFiniteModules g d a)
    (pbcRestrict (reductionCoefficientMap X d b a h))
    (completedReductionFiniteTarget g d b) (completedReductionFiniteTarget g d a)
    (pbcDerivedRestrict (reductionCoefficientMap X d b a h))
    (completedReductionFiniteModelNat g d b) (completedReductionFiniteModelNat g d a)
    (completedReductionRestrictionFactors X (reductionCoefficientMap X d b a h))
    (fun P hP ↦ completedReductionFiniteModelMap_isIso g d a P hP)
    (completedReductionOrdinaryTransition g d a b h)

/-- The canonical derived transition before scalar-extension adjunction.
Source: blueprint transitions (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionTargetTransition (a b : ℕ) (h : a ≤ b) :
    completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h) :=
  (completedReductionTargetTransition_exists g d a b h).exists.choose

/-- Normalization of the pulled reduction tower is the scalar-extension adjunct of
its genuine quotient transition, with no reference to alpha or an arbitrary map.
Source: blueprint normalization clause (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionTargetNormalization
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (a b : ℕ) (h : a ≤ b) :=
  ((pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h)).homEquiv _ _).symm
    ((completedReductionTargetTransition g d a b h).app K)

/-- Equal-index restriction is the identity, fixed sectionwise.
Source: blueprint unit clause (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: the equal-index quotient is identity. Forgetting the restricted action leaves
every section unchanged, defining inverse natural maps whose section maps are identities. -/
theorem completedReductionOrdinaryRestrictionUnit_exists (T : Scheme.{u}) (a : ℕ) :
    ∃! e : SheafOfModules.restrictScalars.{u + 1}
        ((adicLisseForget T).map (reductionCoefficientMap T d a a (le_refl a))) ≅ 𝟭 _,
      ∀ (M : pbcModules T (reductionCoefficient T d a))
        (U : T.ProEtᵒᵖ) (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  classical
  have hφ : (adicLisseForget T).map
      (reductionCoefficientMap T d a a (le_refl a)) = 𝟙 _ := by
    rw [reductionCoefficientMap_id, CategoryTheory.Functor.map_id]
  let e : SheafOfModules.restrictScalars.{u + 1}
      ((adicLisseForget T).map (reductionCoefficientMap T d a a (le_refl a))) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk
          (fun U ↦ ModuleCat.restrictScalarsId'App _ (by rw [hφ]; rfl) (M.val.obj U))
          (by intros; rfl))) (by intros; rfl)
  refine ⟨e, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact he' M U x

/-- The sectionwise identity comparison for equal-index restriction.
Source: blueprint unit clause (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionRestrictionUnit (T : Scheme.{u}) (a : ℕ) :
    pbcDerivedRestrict (reductionCoefficientMap T d a a (le_refl a)) ≅ 𝟭 _ :=
  letI := HasDerivedCategory.standard
    (pbcModules T (reductionCoefficient T d a))
  Functor.mapDerivedCategoryNatIso
    (completedReductionOrdinaryRestrictionUnit_exists d T a).exists.choose ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The canonical equal-index scalar-extension unitor, from the normalized adjunction.
Source: blueprint unit clause (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionUnit (T : Scheme.{u}) (a : ℕ)
    (M : DerivedCategory
      (pbcModules T (reductionCoefficient T d a))) :=
  (reductionDerivedChange T (reductionCoefficientMap T d a a (le_refl a))).map
      ((completedReductionRestrictionUnit d T a).inv.app M) ≫
    (pbcDerivedScalarAdjunction (reductionCoefficientMap T d a a (le_refl a))).counit.app M

/-- Reduction of completed pullback, including the actual projection-induced arrows,
functoriality, transition maps, normalization, quotient cocycle and equal-index unit.
The parameter n denotes the positive level n+1; representatives are arbitrary.
No boundedness, nonempty scheme, nonzero ring, or nonempty generator tuple is required.

Source: blueprint order 1262; Stacks Tag 099N (5)
(blueprint: lemma-weil-pbc-completed-pullback-reduction).

Proof:
1. Restrict to constant A-coefficients using lem-weil-pbc-constant-completion-equivalence.
The defining pulled strict tower becomes the reduction tower of ordinary pullback N,
including its quotient units and finite projections; no infinite limit is pulled back.
2. Apply lem-weil-pbc-ringed-koszul-completion-reflector. Its completed value is complete.
The constant/completed comparison identifies its Koszul unit with the unit for L;
exact scalar restriction reflects invertibility, giving intrinsic completeness over A_X.
3. Use the strict-perfect coefficient package and projection-formula totalization to
commute reduction by P_a with the Koszul derived limit. On the tail m>=a the reduced
Koszul differential vanishes. The degree-zero summand is constant N_a; negative
summands have zero transition across a gap of a. The strict-tower homotopy-limit
lemma kills their derived limit, and also permits discarding the finite initial tail.
The product triangle computes the constant tower as N_a by finite partial sums.
Thus reduction of the completion unit is invertible.
4. The projection-induced arrow composed with that reduced unit is identity by the
normalized scalar adjunction: x tensor s maps to (x tensor 1)s. Hence alpha is the
inverse of the reduced unit. Natural finite comparisons give functoriality.
5. Naturality of tensoring the single completion unit with each quotient gives the
transition square. Apply scalar associativity to the same unit and invert its
reductions to obtain normalization compatibility. Associativity of scalar multiplication
in the ordinary balanced formulas gives the quotient cocycle; the identity quotient
gives the stated unitor. All maps here are the uniquely normalized maps above. -/
theorem completedPullback_reduction
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic Y d r f hf K C e) :
    (∀ (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (eP : DerivedCategory.Q.obj P ≅ completedPullbackObject g d K),
      IsDerivedCompleteIntrinsic X d r f hf (completedPullbackObject g d K) P eP) ∧
    (∀ n : ℕ, IsIso (completedPullbackReductionArrow g d K n)) ∧
    (∀ (K' : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (C' : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
      (e' : DerivedCategory.Q.obj C' ≅ K')
      (_hK' : IsDerivedCompleteIntrinsic Y d r f hf K' C' e') (v : K ⟶ K') (n : ℕ),
      (reductionDerivedChange X (completedReductionProjection X d n)).map
          ((completedPullbackFunctor g d).map v) ≫ completedPullbackReductionArrow g d K' n =
        completedPullbackReductionArrow g d K n ≫
          (completedReductionFiniteTarget g d n).map v) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      IsIso (completedReductionTargetNormalization g d K a b h) ∧
      ((pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h)).homEquiv _ _
          ((completedPullbackSourceNormalization d X a b h (completedPullbackObject g d K)).hom)) ≫
            (pbcDerivedRestrict (reductionCoefficientMap X d b a h)).map
              (completedPullbackReductionArrow g d K a) =
        completedPullbackReductionArrow g d K b ≫
          (completedReductionTargetTransition g d a b h).app K) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedPullbackReductionArrow g d K b) ≫
            completedReductionTargetNormalization g d K a b h =
        (completedPullbackSourceNormalization d X a b h (completedPullbackObject g d K)).hom ≫
          completedPullbackReductionArrow g d K a) ∧
    (∀ (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
          (completedReductionTargetNormalization g d K b c hbc) ≫
            completedReductionTargetNormalization g d K a b hab =
        (completedReductionQuotientAssoc d X a b c hab hbc
            ((completedReductionFiniteTarget g d c).obj K)).hom ≫
          completedReductionTargetNormalization g d K a c (hab.trans hbc)) ∧
    ∀ a : ℕ, completedReductionTargetNormalization g d K a a (le_refl a) =
      completedReductionUnit d X a ((completedReductionFiniteTarget g d a).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
