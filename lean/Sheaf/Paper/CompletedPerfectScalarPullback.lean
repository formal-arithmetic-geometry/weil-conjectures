/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Paper.IntegralPullbackCompletedComparison
public import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Completed perfect scalar models under arbitrary pullback

Source: Bhatt--Scholze, Lemma 6.5.9(4)--(5), Proposition 6.6.11;
Stacks Tags 093J, 093M, 03EL, 06YQ and 0941
(blueprint: lem-a1-completed-perfect-scalar-pullback).

## Main definitions

- `model`: the given scalar complex extended to the completed constant coefficients.
- `Comparisons`: normalized reductions, strict towers, pullback and amplitude.
- `completedPerfectScalarPullback`: all comparisons for an arbitrary scheme morphism.

The index n denotes the positive exponent n+1. Scheme and coefficient universes
are independent. ULift changes only the presentation of the scalar ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures.CompletedPerfectScalar

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral scalars, lifted only for the site size.
Source: Bhatt--Scholze 6.5.9 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev Scalars := ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)

/-- Scalar cochain complexes with their original differentials.
Source: Bhatt--Scholze 6.6.11 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev Complex := CochainComplex (ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)) ℤ

/-- Constant module presheaves in the actual coefficient universe.
Source: Stacks 093J (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def constantPresheaf (T : Scheme.{t}) (R : Type (max u (t + 1))) [CommRing R] :
    ModuleCat.{max u (t + 1)} R ⥤ PresheafOfModules.{max u (t + 1)}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of R)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

/-- The standard constant commutative ring sheaf.
Source: Stacks 093J (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev constantRing (T : Scheme.{t}) (R : Type (max u (t + 1))) [CommRing R] :=
  (constantSheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}).obj (CommRingCat.of R)

/-- Sheafification unit, with commutativity forgotten.
Source: Stacks 03CY (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def constantUnit (T : Scheme.{t}) (R : Type (max u (t + 1))) [CommRing R] :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of R) ⟶
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat RingCat)).obj
        (constantRing T R)).obj :=
  Functor.whiskerRight
    (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of R)))
    (forget₂ CommRingCat RingCat)

/-- Local bijectivity of the constant unit after forgetting commutativity.
Source: Stacks 03CY (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: the underlying section functions and their covering image and equalizer
sieves are unchanged by forgetting commutativity. Apply local bijectivity of
sheafification to those same sieves. -/
theorem constantUnit_local (T : Scheme.{t}) (R : Type (max u (t + 1))) [CommRing R] :
    Presheaf.IsLocallyInjective (ProEt.topology T) (constantUnit T R) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (constantUnit T R) := by
  let : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let : (ProEt.topology T).WEqualsLocallyBijective CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, max u (t + 1),
      t + 1, max u (t + 1) + 1, max u (t + 1)} _
  constructor
  · constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem (ProEt.topology T)
      (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of R)))
      x y h
  · constructor
    intro U s
    exact Presheaf.imageSieve_mem (ProEt.topology T)
      (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of R))) s

/-- Constant module sheafification; coefficients may be larger than the site.
Source: Stacks 093J (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def constant (T : Scheme.{t}) (R : Type (max u (t + 1))) [CommRing R] :
    ModuleCat.{max u (t + 1)} R ⥤ SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat RingCat)).obj
        (constantRing T R)) :=
  letI := (constantUnit_local T R).1
  letI := (constantUnit_local T R).2
  constantPresheaf T R ⋙ PresheafOfModules.sheafification.{max u (t + 1)} (constantUnit T R)

/-- Additivity of constant realization.
Source: Stacks 093J (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: the constant presheaf functor preserves pointwise addition, and module
sheafification is additive. Their composite therefore preserves addition. -/
@[instance] theorem constant_additive (T : Scheme.{t}) (R : Type (max u (t + 1))) [CommRing R] :
    (constant T R).Additive := by
  have : (constantPresheaf T R).Additive := by
    constructor
    intro M N f g
    rfl
  let := (constantUnit_local T R).1
  let := (constantUnit_local T R).2
  let := integralCoefficientAbLocallyBijective.{t, u} T
  have h : (PresheafOfModules.sheafification.{max u (t + 1)}
      (constantUnit T R)).Additive := by
    apply leftExactFunctor_le_additiveFunctor _ _
    rw [leftExactFunctor_iff]
    infer_instance
  unfold constant
  infer_instance

/-- The recorded constant-to-completion morphism in commutative rings.
Source: Stacks 093M (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def scalarMap (T : Scheme.{t}) : constantRing T (Scalars.{t, u} l E) ⟶
    completedIntegralCommRingSheafUnrestricted l E T :=
  (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).preimage
      (integralConstantToCompletionOfUniverses l E T)

/-- Standard ambient localization for constant integral modules.
Source: Stacks 05RU (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
instance scalarHasDerived (T : Scheme.{t}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (ProEt.topology T) (constantRing T (Scalars.{t, u} l E)))) := HasDerivedCategory.standard _

/-- Universal derived change of rings, retaining its ordinary functor and counit.
Source: Stacks 06YY (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def scalarChange (T : Scheme.{t}) :=
  (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel (scalarMap l E T)).some

/-- Ordinary completed scalar realization M ↦ B_T tensor_R constant M.
Source: Bhatt--Scholze 6.6.11 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def modelModules (T : Scheme.{t}) := constant T (Scalars.{t, u} l E) ⋙ (scalarChange l E T).E

/-- Additivity of completed scalar realization.
Source: Stacks 093J, 03EK (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
instance modelModules_additive (T : Scheme.{t}) : (modelModules l E T).Additive :=
  inferInstanceAs ((constant T (Scalars.{t, u} l E)) ⋙ (scalarChange l E T).E).Additive

/-- The actual chain complex C_T(P).
Source: Bhatt--Scholze 6.6.11 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev model (T : Scheme.{t}) := (modelModules l E T).mapHomologicalComplex (.up ℤ)

/-- C_T(P) in the ambient derived category.
Source: Bhatt--Scholze 6.6.11 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev derivedModel (T : Scheme.{t}) := model l E T ⋙ DerivedCategory.Q

/-- Standard ambient localization for finite coefficient modules.
Source: Stacks 06YY (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
instance finiteHasDerived (T : Scheme.{t}) (n : ℕ) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients (ProEt.topology T)
        (integralCoefficientCommRingSheaf l E T n))) := HasDerivedCategory.standard _

/-- The actual finite scalar quotient morphism.
Source: Stacks 093M (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def finiteScalarMap (T : Scheme.{t}) (n : ℕ) :
    constantRing T (Scalars.{t, u} l E) ⟶ integralCoefficientCommRingSheaf l E T n :=
  (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).preimage
      (integralConstantQuotientOfUniverses l E T n)

/-- Finite scalar extension with its tensor-normalized universal counit.
Source: Stacks 06YY (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def finiteChange (T : Scheme.{t}) (n : ℕ) :=
  (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel (finiteScalarMap l E T n)).some

/-- The ordinary finite scalar model, retaining its differential.
Source: Bhatt--Scholze 6.6.11 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev finiteModel (T : Scheme.{t}) (n : ℕ) :=
  (constant T (Scalars.{t, u} l E) ⋙ (finiteChange l E T n).E).mapHomologicalComplex (.up ℤ)

/-- Constant sections through the module sheafification adjunction.
Source: Stacks 093J (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def constantSection (T : Scheme.{t}) (M : ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E))
    (U : T.ProEtᵒᵖ) (x : M) : ((constant T (Scalars.{t, u} l E)).obj M).val.obj U :=
  letI := (constantUnit_local T (Scalars.{t, u} l E)).1
  letI := (constantUnit_local T (Scalars.{t, u} l E)).2
  (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (constantUnit T (Scalars.{t, u} l E))).unit.app
      ((constantPresheaf T (Scalars.{t, u} l E)).obj M)).app U x)

/-- Sheafified pure tensors in the completed scalar model.
Source: Stacks 03EK (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def modelSection (T : Scheme.{t})
    (M : ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)) (U : T.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
    (x : ((constant T (Scalars.{t, u} l E)).obj M).val.obj U) :
    ((modelModules l E T).obj M).val.obj U :=
  (eqToHom ((scalarChange l E T).obj_eq _).symm).val.app U
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (scalarMap l E T)
        ((constant T (Scalars.{t, u} l E)).obj M)).presheaf).app U
      (b ⊗ₜ[(constantRing T (Scalars.{t, u} l E)).obj.obj U,
        ((scalarMap l E T).hom.app U).hom] x))

/-- Sheafified pure tensors in the finite scalar model.
Source: Stacks 03EK (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def finiteSection (T : Scheme.{t}) (n : ℕ)
    (M : ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)) (U : T.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E T n).obj.obj U)
    (x : ((constant T (Scalars.{t, u} l E)).obj M).val.obj U) :
    ((finiteChange l E T n).E.obj ((constant T (Scalars.{t, u} l E)).obj M)).val.obj U :=
  (eqToHom ((finiteChange l E T n).obj_eq _).symm).val.app U
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (finiteScalarMap l E T n)
        ((constant T (Scalars.{t, u} l E)).obj M)).presheaf).app U
      (a ⊗ₜ[(constantRing T (Scalars.{t, u} l E)).obj.obj U,
        ((finiteScalarMap l E T n).hom.app U).hom] x))

/-- The termwise hypothesis on the specified representative, not a replacement up to isomorphism.
Source: Bhatt--Scholze 6.6.11 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def IsModel (P : Complex.{t, u} l E) : Prop :=
  (∃ c d : ℤ, ∀ j : ℤ, j < c ∨ d < j → IsZero (P.X j)) ∧
    ∀ j : ℤ, Module.Finite (Scalars.{t, u} l E) (P.X j) ∧
      Module.Projective (Scalars.{t, u} l E) (P.X j)

/-- Restriction along the completed coefficient projection, on complexes.
Source: Stacks 03DA (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev restrictComplex (T : Scheme.{t}) (n : ℕ) := integralOperationsRestrict l E T n

/-- Chain-level finite reductions.
Source: Stacks 093M, 06YQ (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev Reductions (T : Scheme.{t}) (P : Complex.{t, u} l E) :=
  ∀ n : ℕ, (unrestrictedIntegralFiniteComplex l E T n).obj ((model l E T).obj P) ≅
    (finiteModel l E T n).obj P

/-- The ordinary finite scalar-model tower with its transported quotient transitions.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def quotientTower (T : Scheme.{t}) (P : Complex.{t, u} l E) (r : Reductions l E T P) :=
  Functor.ofOpSequence
    (X := fun n ↦ (restrictComplex l E T n).obj ((finiteModel l E T n).obj P))
    (fun n ↦ (restrictComplex l E T (n + 1)).map (r (n + 1)).inv ≫
      (unrestrictedIntegralTransition l E T n).app ((model l E T).obj P) ≫
        (restrictComplex l E T n).map (r n).hom)

/-- The ordinary quotient augmentation.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def quotientMap (T : Scheme.{t}) (P : Complex.{t, u} l E) (r : Reductions l E T P) (n : ℕ) :=
  unrestrictedTowerUnit l E T ((model l E T).obj P) n ≫
    (restrictComplex l E T n).map (r n).hom

/-- The actual strict Roos complex of the finite scalar tower.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev limitModel (T : Scheme.{t}) (P : Complex.{t, u} l E) (r : Reductions l E T P) :=
  integralOperationsRoos (quotientTower l E T P r)

/-- The derived-limit projection from the cone to its nth product leg.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def limitProjection (T : Scheme.{t}) (P : Complex.{t, u} l E) (r : Reductions l E T P)
    (n : ℕ) :
    DerivedCategory.Q.obj (limitModel l E T P r) ⟶
      DerivedCategory.Q.obj ((restrictComplex l E T n).obj ((finiteModel l E T n).obj P)) :=
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun n ↦ (quotientTower l E T P r).obj (op n))
        (integralOperationsTowerStep (quotientTower l E T P r))) ≫
      Pi.π (fun n ↦ (quotientTower l E T P r).obj (op n)) n)

/-- Exactness over the constant scalar ring, not flatness of a pullback coefficient map.
Source: Stacks 093J, 093M (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: R is Noetherian, and 093M makes its constant completion flat over constant R.
By 093J constants are exact. Their composite with this flat scalar extension
preserves kernels and cokernels and hence finite limits and colimits. -/
theorem modelModules_exact (T : Scheme.{t}) :
    PreservesFiniteLimits (modelModules l E T) ∧
      PreservesFiniteColimits (modelModules l E T) := by
  sorry

/-- Finite limits of scalar realization.
Source: Stacks 093M (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
instance modelModules_limits (T : Scheme.{t}) :
    PreservesFiniteLimits (modelModules l E T) := (modelModules_exact l E T).1

/-- Finite colimits of scalar realization.
Source: Stacks 093M (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
instance modelModules_colimits (T : Scheme.{t}) :
    PreservesFiniteColimits (modelModules l E T) := (modelModules_exact l E T).2

/-- The canonical cohomology map, from preservation of cycles and boundaries.
Source: Stacks 093J, 093M, 010N (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def cohomologyIso (T : Scheme.{t}) (P : Complex.{t, u} l E) (j : ℤ) :
    (DerivedCategory.homologyFunctor (integralTowerModules l E T) j).obj
      ((derivedModel l E T).obj P) ≅ (modelModules l E T).obj (P.homology j) :=
  (DerivedCategory.homologyFunctorFactors (integralTowerModules l E T) j).app
    ((model l E T).obj P) ≪≫ (P.sc j).mapHomologyIso (modelModules l E T)

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Canonical constant-section finite coefficient maps, in direct-image adjoint form.
Source: Stacks 0H7J (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def finiteDirectMap (n : ℕ) :=
  (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    (coefficientProEtaleDirectRingMap.{t, u} g
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

/- Naturality before forgetting commutativity; compare the sheafification units. -/
private theorem coefficient_direct_naturality
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a ≫
        coefficientProEtaleDirectRingMap g B =
      coefficientProEtaleDirectRingMap g A ≫
        ((proEtaleBaseChange g).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv _ _ |>.injective
  dsimp only [constantSheaf, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [coefficientProEtaleDirectRingMap, constantSheaf,
    Functor.comp_obj, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congr_app ((sheafificationAdjunction (ProEt.topology X)
    CommRingCat.{max u (t + 1)}).unit.naturality
      ((Functor.const X.ProEtᵒᵖ).map a)) ((proEtaleBaseChange g).op.obj U)

attribute [local irreducible] coefficientProEtaleDirectRingMap

/-- The completed coefficient map is uniquely fixed by all finite projections.
Source: Stacks 03EL, 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: constant-section maps commute with consecutive quotients. Direct image
preserves limits; lift the resulting cone uniquely to the target completed limit.
Its inverse-image adjoint is the projection-induced structure morphism. -/
theorem directMap_existsUnique :
    ∃! ρ : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).obj
          (completedIntegralCoefficientSheafUnrestricted l E X),
      ∀ n : ℕ, ρ ≫ ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).map
          (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
        limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫ finiteDirectMap l E g n := by
  let F := (proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)
  let τ : integralCoefficientSheafSystem l E Y ⟶ integralCoefficientSheafSystem l E X ⋙ F :=
    NatTrans.ofOpSequence (finiteDirectMap l E g) (by
      intro n
      simp only [integralCoefficientSheafSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      have h := congrArg
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map)
        (coefficient_direct_naturality g
          (CommRingCat.ofHom
            ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
              ((Padic.coefficientExtensionTransition l E (n + 1)).comp
                (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))
      rw [Functor.map_comp, Functor.map_comp] at h
      exact h)
  let c : Cone (integralCoefficientSheafSystem l E X ⋙ F) :=
    { pt := completedIntegralCoefficientSheafUnrestricted l E Y
      π := (limit.cone (integralCoefficientSheafSystem l E Y)).π ≫ τ }
  let hc := isLimitOfPreserves F (limit.isLimit (integralCoefficientSheafSystem l E X))
  refine ⟨hc.lift c, ?_, ?_⟩
  · intro n
    exact hc.fac c (op n)
  · intro ρ hρ
    apply hc.hom_ext
    intro n
    exact (hρ n.unop).trans (hc.fac c n).symm

/-- The unique projection-induced coefficient map.
Source: Stacks 03EL (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def directMap := (directMap_existsUnique l E g).exists.choose

/-- Module direct image through that actual coefficient map.
Source: Stacks 03D2 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def ordinaryPush : integralTowerModules l E X ⥤ integralTowerModules l E Y :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := proEtaleBaseChange g)
    (J := ProEt.topology Y) (K := ProEt.topology X) (directMap l E g)

/-- Ordinary ringed pullback exists as the sheafified module Kan extension.
Source: Stacks 03D2 (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: use coefficient-sized small models of both sites, form the module presheaf
Kan extension along the displayed coefficient morphism, and sheafify. Transport
back. Its right adjoint is exactly the displayed sectionwise module direct image. -/
@[instance] theorem ordinaryPush_isRightAdjoint : (ordinaryPush l E g).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes (directMap l E g)

/-- Ordinary ringed tensor pullback, determined together with its adjunction unit.
Source: Stacks 03EL (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def ordinaryPull : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  (ordinaryPush l E g).leftAdjoint

/-- The universal adjunction for ordinary ringed pullback.
Source: Stacks 03D2 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def ordinaryAdjunction : ordinaryPull l E g ⊣ ordinaryPush l E g :=
  Adjunction.ofIsRightAdjoint (ordinaryPush l E g)

/-- The generator 1 tensor g inverse x through the actual adjunction unit.
Source: Stacks 03EL (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def ordinaryGenerator (M : integralTowerModules l E Y) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    ((ordinaryPull l E g).obj M).val.obj (op ((proEtaleBaseChange g).obj V)) :=
  ((ordinaryAdjunction l E g).unit.app M).val.app (op V) x

/-- Ordinary balanced tensors, with both forward and inverse formulas retained.
Source: Stacks 03EL (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
structure OrdinaryComparison where
  iso : modelModules l E Y ⋙ ordinaryPull l E g ≅ modelModules l E X
  hom_formula : ∀ (N : ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E))
    (V : Y.ProEt) (n : N)
    (b : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
    (b' : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
      (op ((proEtaleBaseChange g).obj V))),
    ((iso.hom.app N).val.app (op ((proEtaleBaseChange g).obj V)))
      (b' • ordinaryGenerator l E g ((modelModules l E Y).obj N) V
        (modelSection l E Y N (op V) b (constantSection l E Y N (op V) n))) =
      modelSection l E X N (op ((proEtaleBaseChange g).obj V))
        (b' * (@id ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
          (op ((proEtaleBaseChange g).obj V))) ((directMap l E g).hom.app (op V) b)))
        (constantSection l E X N (op ((proEtaleBaseChange g).obj V)) n)
  inv_formula : ∀ (N : ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E))
    (V : Y.ProEt) (n : N)
    (b' : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
      (op ((proEtaleBaseChange g).obj V))),
    ((iso.inv.app N).val.app (op ((proEtaleBaseChange g).obj V)))
      (modelSection l E X N (op ((proEtaleBaseChange g).obj V)) b'
        (constantSection l E X N (op ((proEtaleBaseChange g).obj V)) n)) =
      b' • ordinaryGenerator l E g ((modelModules l E Y).obj N) V
        (modelSection l E Y N (op V) 1 (constantSection l E Y N (op V) n))

/- The local-relation proof of ConstantModuleFlat, at independent coefficient sizes. -/
private theorem constant_flat (T : Scheme.{t})
    (R : Type (max u (t + 1))) [CommRing R] (M : ModuleCat.{max u (t + 1)} R)
    (hM : Module.Flat R M) :
    SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (J := ProEt.topology T) (R := constantRing T R) ((constant T R).obj M) := by
  let J := ProEt.topology T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  classical
  let := (constantUnit_local T R).1
  let := (constantUnit_local T R).2
  let N := (constant T R).obj M
  let P := (constantPresheaf T R).obj M
  let η := toSheafify J P.presheaf
  let α := constantUnit T R
  let τ := PresheafOfModules.toSheafify α η
  have ηsurj : Presheaf.IsLocallySurjective J η := inferInstance
  have ηinj : Presheaf.IsLocallyInjective J η := inferInstance
  have αsurj : Presheaf.IsLocallySurjective J α := inferInstance
  have hn (V W : T.ProEtᵒᵖ) (f : V ⟶ W) (x : M) :
      N.val.map f (η.app V x) = η.app W x :=
    (PresheafOfModules.naturality_apply τ f x).symm
  have hr (V W : T.ProEtᵒᵖ) (f : V ⟶ W) (a : R) :
      (constantRing T R).obj.map f (α.app V a) = α.app W a :=
    (NatTrans.naturality_apply α f a).symm
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion (constantRing T R) N
  intro U n a s hs
  let cover : Sieve U :=
    { arrows V f := ∃ (c : Fin n → R) (x : Fin n → M),
        (∀ i, α.app (op V) (c i) = (constantRing T R).obj.map f.op (a i)) ∧
        (∀ i, η.app (op V) (x i) = N.val.map f.op (s i)) ∧
        (∑ i, c i • x i) = 0
      downward_closed := by
        intro V W f hf g
        obtain ⟨c, x, hc, hx, hcx⟩ := hf
        refine ⟨c, x, ?_, ?_, hcx⟩
        · intro i
          rw [← hr _ _ g.op, hc]
          exact ((constantRing T R).obj.map_comp_apply f.op g.op (a i)).symm
        · intro i
          rw [← hn _ _ g.op, hx]
          exact (N.val.map_comp_apply f.op g.op (s i)).symm }
  have hT : cover ∈ J U := by
    let A : J.Cover U := Finset.univ.inf fun i : Fin n ↦
      ⟨Presheaf.imageSieve α (a i), Presheaf.imageSieve_mem J α (a i)⟩
    let B : J.Cover U := Finset.univ.inf fun i : Fin n ↦
      ⟨Presheaf.imageSieve η (s i), Presheaf.imageSieve_mem J η (s i)⟩
    apply J.transitive (J.intersection_covering A.property B.property) cover
    intro V f hf
    have hliftc (i : Fin n) : ∃ c : R,
        α.app (op V) c = (constantRing T R).obj.map f.op (a i) := by
      exact (Finset.inf_le (Finset.mem_univ i) : A ≤ _) f hf.1
    have hliftx (i : Fin n) : ∃ x : M, η.app (op V) x = N.val.map f.op (s i) := by
      exact (Finset.inf_le (Finset.mem_univ i) : B ≤ _) f hf.2
    choose c hc using hliftc
    choose x hx using hliftx
    have heq : η.app (op V) (∑ i, c i • x i) = η.app (op V) 0 := by
      change (τ.app (op V)) (∑ i, c i • x i) = (τ.app (op V)) 0
      rw [map_sum, map_zero]
      simp_rw [map_smul]
      change (∑ i, (α.app (op V) (c i)) •
        (show N.val.obj (op V) from η.app (op V) (x i))) = 0
      calc
        _ = ∑ i, (show N.val.obj (op V) from N.val.map f.op (a i • s i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hc, hx]
          exact (N.val.map_smul f.op (a i) (s i)).symm
        _ = 0 := by
          have h := (map_sum (N.val.map f.op).hom.toAddMonoidHom
            (fun i ↦ a i • s i) Finset.univ).symm
          rw [hs, map_zero] at h
          convert h using 1 <;> rfl
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J η _ _ heq)
    intro W g hg
    refine ⟨c, x, ?_, ?_, ?_⟩
    · intro i
      rw [← hr _ _ g.op, hc]
      exact ((constantRing T R).obj.map_comp_apply f.op g.op (a i)).symm
    · intro i
      rw [← hn _ _ g.op, hx]
      exact (N.val.map_comp_apply f.op g.op (s i)).symm
    · exact hg
  refine ⟨cover, hT, ?_⟩
  intro V f hf
  obtain ⟨c, x, hc, hx, hcx⟩ := hf
  let := hM
  obtain ⟨l, b, t, hb, hbt⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hcx
  refine ⟨l, fun i j ↦ α.app (op V) (b i j), fun j ↦ η.app (op V) (t j), ?_, ?_⟩
  · intro i
    rw [← hx, hb]
    change (τ.app (op V)) (∑ j, b i j • t j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (τ.app (op V)).hom.map_smul (b i j) (t j)
  · intro j
    simp_rw [← hc]
    simpa only [map_sum, map_mul, map_zero] using
      congrArg (fun z : R ↦ α.app (op V) z) (hbt j)

/-- The bounded scalar model is K-flat with flat terms.
Source: Stacks 06YQ (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: projective terms are flat. Lift finite relations locally through the constant
sheafification units to show that their constant module sheaves are flat. Boundedness
gives K-flatness at independent coefficient universes. Change of rings preserves
K-flatness and termwise flatness, giving the result for the completed scalar model. -/
theorem model_good (T : Scheme.{t}) (P : Complex.{t, u} l E) (hP : IsModel l E P) :
    integralOperationsGoodComplex l E T ((model l E T).obj P) := by
  let R := constantRing T (Scalars.{t, u} l E)
  let C := (constant T (Scalars.{t, u} l E)).mapHomologicalComplex (.up ℤ)
  let K := C.obj P
  have hf (i : ℤ) : SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (J := ProEt.topology T) (R := R) (K.X i) := by
    have : Module.Projective (Scalars.{t, u} l E) (P.X i) := (hP.2 i).2
    exact constant_flat T (Scalars.{t, u} l E) (P.X i) inferInstance
  obtain ⟨c, d, hcd⟩ := hP.1
  have : CochainComplex.IsStrictlyLE K d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (constant T (Scalars.{t, u} l E)).map_isZero (hcd i (Or.inr hi))
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R K d hf
  let S := completedIntegralCommRingSheafUnrestricted l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  have hf' (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (K.X i)) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R (K.X i)) (hf i)
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (scalarMap l E T) K (scalarChange l E T).E
    (scalarChange l E T).obj_eq (scalarChange l E T).map_eq hk hf'
  refine ⟨h.1, fun i ↦ ?_⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S (((model l E T).obj P).X i)).symm (h.2 i)

/-- Derived reduction through the universal counit, followed by ordinary reduction.
Source: Stacks 06YY, 06YQ (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def derivedReductionIso (T : Scheme.{t}) (P : Complex.{t, u} l E)
    (hP : IsModel l E P) (r : Reductions l E T P) (n : ℕ) :
    (scalarReductionDerivedExtension l E T n).obj ((derivedModel l E T).obj P) ≅
      DerivedCategory.Q.obj ((finiteModel l E T n).obj P) :=
  unrestrictedTowerResolutionIso l E T n (𝟙 ((model l E T).obj P))
    ⟨inferInstance, (model_good l E T P hP).1⟩ ≪≫ DerivedCategory.Q.mapIso (r n)

/-- Naturality of the strict tower identification.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: the consecutive transition is defined by conjugating the original transition.
Cancel the adjacent inverse pairs. Compose consecutive arrows to obtain the equality
for any tower arrow; the identity case follows from the functor identity laws. -/
theorem quotientTowerIso_naturality (T : Scheme.{t}) (P : Complex.{t, u} l E)
    (r : Reductions l E T P) (i j : ℕᵒᵖ) (f : i ⟶ j) :
    (unrestrictedIntegralComplexTower l E T ((model l E T).obj P)).map f ≫
        (restrictComplex l E T j.unop).map (r j.unop).hom =
      (restrictComplex l E T i.unop).map (r i.unop).hom ≫
        (quotientTower l E T P r).map f := by
  let α : unrestrictedIntegralComplexTower l E T ((model l E T).obj P) ⟶
      quotientTower l E T P r :=
    NatTrans.ofOpSequence (fun n ↦ (restrictComplex l E T n).map (r n).hom) (by
      intro n
      simp only [unrestrictedIntegralComplexTower, quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
      rw [(restrictComplex l E T (n + 1)).map_id, Category.id_comp])
  exact α.naturality f

/-- The strict tower comparison, retaining every quotient transition.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def quotientTowerIso (T : Scheme.{t}) (P : Complex.{t, u} l E)
    (r : Reductions l E T P) :
    unrestrictedIntegralComplexTower l E T ((model l E T).obj P) ≅ quotientTower l E T P r :=
  NatIso.ofComponents (fun n ↦ (restrictComplex l E T n.unop).mapIso (r n.unop))
    (fun {i j} f ↦ quotientTowerIso_naturality l E T P r i j f)

/-- Naturality of consecutive reduction maps on the specified scalar chain map.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: use naturality of unrestrictedIntegralTransition at model.map f. The
consecutive-arrow formula for Functor.ofOpSequence identifies its two components
with the consecutive structure maps of the two strict reduction towers. -/
theorem reductionTowerMap_condition (T : Scheme.{t}) {P Q : Complex.{t, u} l E}
    (f : P ⟶ Q) (n : ℕ) :
    (unrestrictedIntegralComplexTower l E T ((model l E T).obj P)).map
        (homOfLE (Nat.le_succ n)).op ≫
      (unrestrictedIntegralComplexFunctor l E T n).map ((model l E T).map f) =
    (unrestrictedIntegralComplexFunctor l E T (n + 1)).map ((model l E T).map f) ≫
      (unrestrictedIntegralComplexTower l E T ((model l E T).obj Q)).map
        (homOfLE (Nat.le_succ n)).op := by
  simpa only [unrestrictedIntegralComplexTower,
    Functor.ofOpSequence_map_homOfLE_succ] using
      ((unrestrictedIntegralTransition l E T n).naturality ((model l E T).map f)).symm

/-- Strict reduction-tower maps induced by the original scalar chain maps.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def reductionTowerMap (T : Scheme.{t}) {P Q : Complex.{t, u} l E} (f : P ⟶ Q) :
    unrestrictedIntegralComplexTower l E T ((model l E T).obj P) ⟶
      unrestrictedIntegralComplexTower l E T ((model l E T).obj Q) :=
  NatTrans.ofOpSequence
    (fun n ↦ (unrestrictedIntegralComplexFunctor l E T n).map ((model l E T).map f))
    (reductionTowerMap_condition l E T f)

/-- The induced map of ordinary finite scalar towers.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def quotientTowerMap (T : Scheme.{t}) {P Q : Complex.{t, u} l E} (f : P ⟶ Q)
    (rP : Reductions l E T P) (rQ : Reductions l E T Q) :=
  (quotientTowerIso l E T P rP).inv ≫ reductionTowerMap l E T f ≫
    (quotientTowerIso l E T Q rQ).hom

/-- Product of the ordinary quotient maps.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def quotientProduct (T : Scheme.{t}) (P : Complex.{t, u} l E) (r : Reductions l E T P) :=
  Pi.lift (fun n ↦ quotientMap l E T P r n)

attribute [local irreducible] scalarChange finiteChange constant
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence

/- Quotient maps preserve 1, so the normalized adjunction units form a cone. -/
private theorem quotient_unit_transition (T : Scheme.{t})
    (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :
    unrestrictedTowerUnit l E T P (n + 1) ≫
      (unrestrictedIntegralTransition l E T n).app P = unrestrictedTowerUnit l E T P n := by
  ext j U x
  change (((unrestrictedIntegralTransition l E T n).app P).f j).val.app U
    (((unrestrictedTowerUnit l E T P (n + 1)).f j).val.app U x) = _
  rw [unrestrictedTowerUnit_condition]
  change (((unrestrictedIntegralTransition l E T n).app P).f j).val.app U
    (unrestrictedIntegralTensorSection l E T (n + 1) (P.X j) U 1 x) = _
  have h := (unrestrictedIntegralTransition_existsUnique l E T n).exists.choose_spec
    P j U 1 x
  change (((unrestrictedIntegralTransition l E T n).app P).f j).val.app U
    (unrestrictedIntegralTensorSection l E T (n + 1) (P.X j) U 1 x) = _ at h
  have hu := unrestrictedTowerUnit_condition l E T P n j U x
  change (((unrestrictedTowerUnit l E T P n).f j).val.app U x) =
    unrestrictedIntegralTensorSection l E T n (P.X j) U 1 x at hu
  rw [map_one] at h
  exact h.trans hu.symm

/- The product equation depends only on the cone equations, not on scalar models. -/
private theorem product_unit_condition {A : Type v} [Category.{w} A] [Preadditive A]
    {K : ℕ → A} [HasProduct K] {M : A} (q : ∀ n, M ⟶ K n)
    (f : ∀ n, K (n + 1) ⟶ K n) (hq : ∀ n, q (n + 1) ≫ f n = q n) :
    Pi.lift q ≫ towerTransitionEndomorphism f = 0 := by
  apply Pi.hom_ext
  intro n
  simpa [towerTransitionEndomorphism, towerProductShift, Category.assoc] using
    sub_eq_zero.mpr (hq n).symm

/-- The quotient family with zero second coordinate defines a Roos chain map.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback).
Proof: after each product projection the consecutive quotient units agree, since
quotient maps preserve 1. Conjugate by the reduction isomorphisms and cancel their
inverse pairs. Thus 1-s kills the family. Product projections are jointly monic
and the differential of the zero cochain is zero. -/
theorem limitUnit_condition (T : Scheme.{t}) (P : Complex.{t, u} l E)
    (r : Reductions l E T P) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain ((model l E T).obj P)
        (∏ᶜ fun n : ℕ ↦ (quotientTower l E T P r).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (quotientProduct l E T P r ≫ towerTransitionEndomorphism
          (K := fun n ↦ (quotientTower l E T P r).obj (op n))
          (integralOperationsTowerStep (quotientTower l E T P r))) = 0 := by
  have hu (n : ℕ) : quotientMap l E T P r (n + 1) ≫
      integralOperationsTowerStep (quotientTower l E T P r) n = quotientMap l E T P r n := by
    simp only [quotientMap, integralOperationsTowerStep, quotientTower,
      Functor.ofOpSequence_map_homOfLE_succ, Category.assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id]
    rw [(restrictComplex l E T (n + 1)).map_id]
    erw [Category.id_comp]
    rw [← Category.assoc, quotient_unit_transition]
  have hz : quotientProduct l E T P r ≫ towerTransitionEndomorphism
      (K := fun n ↦ (quotientTower l E T P r).obj (op n))
      (integralOperationsTowerStep (quotientTower l E T P r)) = 0 := by
    exact product_unit_condition (fun n ↦ quotientMap l E T P r n)
      (integralOperationsTowerStep (quotientTower l E T P r)) hu
  simp only [CochainComplex.HomComplex.δ_zero, zero_add]
  exact (congrArg CochainComplex.HomComplex.Cochain.ofHom hz).trans
    (CochainComplex.HomComplex.Cochain.ofHom_zero _ _)

/-- Canonical map to the Roos model: quotient family and zero cone coordinate.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def limitUnit (T : Scheme.{t}) (P : Complex.{t, u} l E) (r : Reductions l E T P) :
    (model l E T).obj P ⟶ limitModel l E T P r :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism (K := fun n ↦ (quotientTower l E T P r).obj (op n))
      (integralOperationsTowerStep (quotientTower l E T P r)))
    (quotientProduct l E T P r) 0 (limitUnit_condition l E T P r)

attribute [local irreducible] integralOperationsRoos

/-- Ordinary reduction on every sheafified pure tensor.
Source: Stacks 093M (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def ReductionFormula (T : Scheme.{t}) (P : Complex.{t, u} l E) (r : Reductions l E T P) :
    Prop :=
  ∀ (n : ℕ) (j : ℤ) (U : T.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
    (a : (integralCoefficientCommRingSheaf l E T n).obj.obj U)
    (x : ((constant T (Scalars.{t, u} l E)).obj (P.X j)).val.obj U),
    (((r n).hom.f j).val.app U)
      (unrestrictedIntegralTensorSection l E T n (((model l E T).obj P).X j) U a
        (modelSection l E T (P.X j) U b x)) =
      finiteSection l E T n (P.X j) U
        (a * (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U b) x

/-- The ordinary quotient transitions, before localization.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def TransitionFormula (T : Scheme.{t}) (P : Complex.{t, u} l E) (r : Reductions l E T P) :
    Prop :=
  ∀ (n : ℕ) (j : ℤ) (U : T.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E T (n + 1)).obj.obj U)
    (x : ((constant T (Scalars.{t, u} l E)).obj (P.X j)).val.obj U),
    (((integralOperationsTowerStep (quotientTower l E T P r) n).f j).val.app U)
      (finiteSection l E T (n + 1) (P.X j) U a x) =
      finiteSection l E T n (P.X j) U
        ((integralCoefficientSheafTransition l E T n).hom.app U a) x

/-- Normalized finite scalar-model reductions, natural in the original chain maps.
Source: Stacks 093M, 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
structure ModelReductions (T : Scheme.{t}) where
  reduction : ∀ (P : Complex.{t, u} l E), IsModel l E P → Reductions l E T P
  formula : ∀ (P : Complex.{t, u} l E) (hP : IsModel l E P),
    ReductionFormula l E T P (reduction P hP)
  transition : ∀ (P : Complex.{t, u} l E) (hP : IsModel l E P),
    TransitionFormula l E T P (reduction P hP)
  naturality : ∀ (P Q : Complex.{t, u} l E) (hP : IsModel l E P)
    (hQ : IsModel l E Q) (f : P ⟶ Q) (n : ℕ),
    (unrestrictedIntegralFiniteComplex l E T n).map ((model l E T).map f) ≫
        (reduction Q hQ n).hom =
      (reduction P hP n).hom ≫ (finiteModel l E T n).map f

/-- Isomorphisms from the explicit Roos limits to the actual scalar complexes.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev LimitIsos (T : Scheme.{t}) (r : ModelReductions l E T) :=
  ∀ (P : Complex.{t, u} l E) (hP : IsModel l E P),
    DerivedCategory.Q.obj (limitModel l E T P (r.reduction P hP)) ≅
      (derivedModel l E T).obj P

/-- The inverse comparison is the specified zero-second-coordinate quotient unit.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def LimitUnitFormula (T : Scheme.{t}) (r : ModelReductions l E T) (e : LimitIsos l E T r) :
    Prop :=
  ∀ (P : Complex.{t, u} l E) (hP : IsModel l E P),
    (e P hP).inv = DerivedCategory.Q.map (limitUnit l E T P (r.reduction P hP))

/-- Every derived-limit projection is the ordinary quotient map.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def LimitProjectionFormula (T : Scheme.{t}) (r : ModelReductions l E T)
    (e : LimitIsos l E T r) : Prop :=
  ∀ (P : Complex.{t, u} l E) (hP : IsModel l E P) (n : ℕ),
    (e P hP).inv ≫ limitProjection l E T P (r.reduction P hP) n =
      DerivedCategory.Q.map (quotientMap l E T P (r.reduction P hP) n)

/-- Naturality of the specified limit comparison under original scalar chain maps.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def LimitNaturality (T : Scheme.{t}) (r : ModelReductions l E T) (e : LimitIsos l E T r) :
    Prop :=
  ∀ (P Q : Complex.{t, u} l E) (hP : IsModel l E P)
    (hQ : IsModel l E Q) (f : P ⟶ Q),
    DerivedCategory.Q.map ((integralOperationsRoosFunctor (A := integralTowerModules l E T)).map
        (quotientTowerMap l E T f (r.reduction P hP) (r.reduction Q hQ))) ≫
        (e Q hQ).hom = (e P hP).hom ≫ (derivedModel l E T).map f

/-- Derived completeness of the actual scalar model, in the recorded ambient predicate.
Source: Bhatt--Scholze 6.6.11 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def CompleteModel (T : Scheme.{t}) (P : Complex.{t, u} l E) : Prop :=
  IntegralOnSlice.IsComplete l E T none ((derivedModel l E T).obj P)

/-- The normalized derived limit of the finite scalar models.
Source: Stacks 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
structure ModelComparisons (T : Scheme.{t}) extends ModelReductions l E T where
  limitIso : LimitIsos l E T toModelReductions
  limit_unit : LimitUnitFormula l E T toModelReductions limitIso
  projections : LimitProjectionFormula l E T toModelReductions limitIso
  limit_natural : LimitNaturality l E T toModelReductions limitIso
  complete : ∀ (P : Complex.{t, u} l E) (_hP : IsModel l E P), CompleteModel l E T P


/-- Finite pullback of the actual source reduction.
Source: Stacks 03EL, 099N (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
abbrev pulledFinite (n : ℕ) :=
  model l E Y ⋙ unrestrictedIntegralFiniteComplex l E Y n ⋙
    (integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)

/-- Integral pullback computed on the actual good representative and its strict tower.
Source: Bhatt--Scholze 6.5.9(4)--(5) (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def pullbackIso (P : Complex.{t, u} l E) (hP : IsModel l E P)
    (r : Reductions l E X P)
    (e : (integralOperationsPullbackTowerFunctor l E g).obj ((model l E Y).obj P) ≅
      quotientTower l E X P r) :
    (integralDerivedPullback l E g).obj ((derivedModel l E Y).obj P) ≅
      DerivedCategory.Q.obj (limitModel l E X P r) :=
  (integralDerivedPullbackComparison l E g).app
    ⟨(model l E Y).obj P, model_good l E Y P hP⟩ ≪≫
      DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso e)

/-- Finite pullback sends constant-section tensor generators to themselves.
Source: Stacks 03EL, 0H7J (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def FiniteFormula (P : Complex.{t, u} l E) (n : ℕ)
    (e : (pulledFinite l E g n).obj P ≅ (finiteModel l E X n).obj P) : Prop :=
  ∀ (j : ℤ) (V : Y.ProEt) (p : P.X j)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V)),
    ((e.hom.f j).val.app (op ((proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator l E g n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj ((model l E Y).obj P)).X j) V
        (unrestrictedIntegralTensorSection l E Y n (((model l E Y).obj P).X j) (op V) a
          (modelSection l E Y (P.X j) (op V) 1
            (constantSection l E Y (P.X j) (op V) p)))) =
      finiteSection l E X n (P.X j) (op ((proEtaleBaseChange g).obj V))
        (@id ((integralCoefficientCommRingSheaf l E X n).obj.obj
          (op ((proEtaleBaseChange g).obj V))) ((finiteDirectMap l E g n).hom.app (op V) a))
        (constantSection l E X (P.X j) (op ((proEtaleBaseChange g).obj V)) p)

/-- All finite pullback comparisons preserve the original differentials and chain maps.
Source: Stacks 03EL, 0941 (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
structure FinitePullComparisons where
  finitePull : ∀ (P : Complex.{t, u} l E) (_hP : IsModel l E P) (n : ℕ),
    (pulledFinite l E g n).obj P ≅ (finiteModel l E X n).obj P
  formula : ∀ (P : Complex.{t, u} l E) (hP : IsModel l E P) (n : ℕ),
    FiniteFormula l E g P n (finitePull P hP n)
  naturality : ∀ (P Q : Complex.{t, u} l E) (hP : IsModel l E P)
    (hQ : IsModel l E Q) (f : P ⟶ Q) (n : ℕ),
    (pulledFinite l E g n).map f ≫ (finitePull Q hQ n).hom =
      (finitePull P hP n).hom ≫ (finiteModel l E X n).map f

/-- Cohomological amplitude of the source scalar model persists after pullback.
Source: Stacks 03EL, 093M (blueprint: lem-a1-completed-perfect-scalar-pullback). -/
def Amplitude : Prop :=
  ∀ (P : Complex.{t, u} l E) (_hP : IsModel l E P) (a b : ℤ), a ≤ b →
    (∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor (integralTowerModules l E Y) j).obj
        ((derivedModel l E Y).obj P))) →
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor (integralTowerModules l E X) j).obj
        ((derivedModel l E X).obj P))

/-- All comparisons, retaining strict transitions and the balanced-tensor normalization.
Source: Bhatt--Scholze 6.5.9(4)--(5), 6.6.11; Stacks 03EL, 093M and 0941
(blueprint: lem-a1-completed-perfect-scalar-pullback). -/
structure Comparisons extends FinitePullComparisons l E g where
  source : ModelComparisons l E Y
  target : ModelComparisons l E X
  tower : ∀ (P : Complex.{t, u} l E) (hP : IsModel l E P),
    (integralOperationsPullbackTowerFunctor l E g).obj ((model l E Y).obj P) ≅
      quotientTower l E X P (target.reduction P hP)
  tower_evaluation : ∀ (P : Complex.{t, u} l E) (hP : IsModel l E P) (n : ℕ),
    (tower P hP).hom.app (op n) = (restrictComplex l E X n).map (finitePull P hP n).hom
  pull_natural : ∀ (P Q : Complex.{t, u} l E) (hP : IsModel l E P)
    (hQ : IsModel l E Q) (f : P ⟶ Q),
    (integralDerivedPullback l E g).map ((derivedModel l E Y).map f) ≫
        (pullbackIso l E g Q hQ (target.reduction Q hQ) (tower Q hQ)).hom ≫
          (target.limitIso Q hQ).hom =
      (pullbackIso l E g P hP (target.reduction P hP) (tower P hP)).hom ≫
        (target.limitIso P hP).hom ≫ (derivedModel l E X).map f
  ordinary : OrdinaryComparison l E g
  amplitude : Amplitude l E (X := X) (Y := Y)

/-- Completed perfect scalar models, with their canonical pullback and cohomology comparisons.
The cohomology comparison is `cohomologyIso`; the ordinary comparison applies to
all scalar modules, in particular to every H^j(P).
Source: Bhatt--Scholze 6.5.9(4)--(5), 6.6.11; Stacks 093M, 03EL, 06YQ, 0941
(blueprint: lem-a1-completed-perfect-scalar-pullback).

Proof, following the nine DAG steps:
1. The integer ring is a complete DVR with finite residue field. Positive quotients
are finite torsion and have the two-term free resolution [R --pi^(n+1)--> R].
Use the actual integral coefficient sheaves, quotient maps and completed limit.
2. Split each finite projective term off a finite free module. Constants and scalar
extension preserve these splittings. Thus model_good gives a bounded K-flat complex
with flat terms. Its universal derived counit computes reduction on the given complex.
The ordinary map sends a tensor (b tensor x) to a pr_n(b) tensor x; its inverse inserts 1.
Balancing proves these inverse; the formulas commute with differentials and quotients.
3. Completed perfect-model completeness and the Roos/intrinsic equivalence give the
recorded derived completeness condition on both schemes. No scheme finiteness is used.
4. Finite free retracts identify the ordinary limit cone with the quotient augmentation.
Consecutive maps are epi. The surjective-tower theorem and exact countable products
make the map (quotient family,0) to the Roos cone a quasi-isomorphism: its cokernel
is the contractible cone of identity. Strict Roos comparison retains the augmentation
and all projections. Its naturality gives limit_unit, projections and limit_natural.
5. Constant-module inverse image and tensor comparison give the finite chain
isomorphisms. They preserve constant sections, differentials and every quotient map.
These equalities hold locally on pure tensors, so give the strict tower isomorphism.
6. Compute the specified integral pullback on the good representative and apply Rlim
to that tower isomorphism. Invert the target limit comparison. The integral/completed
pullback comparison on the complete input identifies this with completed pullback,
with the same projections. Naturality follows from the strict maps of towers.
7. Constants are exact by 093J and completion is flat over constant R by 093M.
Thus scalar realization is exact. Preservation of cycles and boundaries gives the
canonical cohomologyIso for every degree, with no flatness assertion about g-sharp.
8. Cancel balanced tensors for every N: b' tensor (b tensor n) maps to
b'g-sharp(b) tensor n, with inverse inserting 1. The coefficient square commutes
after all finite projections, hence by the limit universal property. Balancing
proves both inverse equations. The maps descend through sheafification and are natural.
9. For j outside [a,b], ordinary pullback takes the assumed zero source cohomology
to zero. Steps 7 and 8 with N=H^j(P) identify it with the target cohomology. This
uses the cohomological interval, not support degrees of the chosen representative. -/
theorem completedPerfectScalarPullback
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Comparisons l E g) := by
  sorry

end WeilConjectures.CompletedPerfectScalar
