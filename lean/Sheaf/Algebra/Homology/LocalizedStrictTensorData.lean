/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat
public import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.Paper.ReductionPullbackDerivedTower
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness

/-! # Normalized localized extension on derived strict coefficient towers

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor;
Cohomology on Sites, Tags 06YS and 06YU; Categories, Tags 04VG and 04VK.
(blueprint: def-sf-localized-strict-tensor-comparison-data).

Strict towers are localized after taking complexes. The reduction functor is the
universal left derived functor of the actual ordinary tensor tower, equivalently
the diagram-site tensor of the constant diagram with the coefficient tower.
The counit fixes all representative comparisons; no functorial resolution is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace SheafOfModules.LocalizedStrictTensor

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

/-- The existing underlying ring sheaf. Source: Stacks 03DA
(blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev ring (R : Sheaf J CommRingCat.{max c v r}) :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

/-- The existing category of module sheaves. Source: Stacks 03DA
(blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev Modules (R : Sheaf J CommRingCat.{max c v r}) :=
  ringedSiteModules.{max c v r} (ring.{c, v, r} R)

/-- Underlying module of a unital algebra sheaf, by actual scalar restriction.
Source: Stacks 03DA (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def algebraModule (R : Sheaf J CommRingCat.{max c v r}) (A : Under R) : Modules.{c, v, r} R :=
  (restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map A.hom)).obj
    (unit (ring.{c, v, r} A.right))

/-- The section maps of an algebra map, regarded as module maps.
Source: Stacks 03DA (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def algebraModules (R : Sheaf J CommRingCat.{max c v r}) : Under R ⥤ Modules.{c, v, r} R where
  obj := algebraModule.{c, v, r} R
  map {A B} f :=
    { val := PresheafOfModules.homMk
        (Functor.whiskerRight f.right.hom
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r} ⋙
            forget₂ RingCat.{max c v r} AddCommGrpCat.{max c v r})) (by
          intro W a b
          change A.right.obj.obj W at b
          change R.obj.obj W at a
          change (f.right.hom.app W).hom ((A.hom.hom.app W).hom a * b) =
            (B.hom.hom.app W).hom a * (f.right.hom.app W).hom b
          rw [map_mul]
          congr 1
          exact congrArg (fun t ↦ t.hom.app W a) (Under.w f)) }

/-- Positive levels are indexed by n+1; maps preserve R and 1 by construction.
Source: Stacks 03DA, inverse-sequence convention
(blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev AlgebraTowers (R : Sheaf J CommRingCat.{max c v r}) := ℕᵒᵖ ⥤ Under R

/-- The actual tensor tower M tensor_R S_n, with transitions 1 tensor s_n.
Source: Stacks 03EK and 0E8I
(blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev reduction (R : Sheaf J CommRingCat.{max c v r})
    (S : AlgebraTowers.{c, v, r} R) :=
  CategoryTheory.StrictReduction.reduction (S ⋙ algebraModules.{c, v, r} R)

/-- Restrict an algebra tower to the actual localized site.
Source: Stacks 03DA (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def sliceAlgebras (R : Sheaf J CommRingCat.{max c v r}) (V : C) :
    Under R ⥤ Under (R.over V) :=
  Under.post (X := R) (J.overPullback CommRingCat.{max c v r} V)

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The recorded strict reduction is additive.
Source: Stacks 03EK (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance reduction_additive (R : Sheaf J CommRingCat.{max c v r})
    (S : AlgebraTowers.{c, v, r} R) : (reduction.{c, v, r} R S).Additive :=
  letI := cochainModulesPreadditive.{c, v, max c v r} R
  CategoryTheory.StrictReduction.reduction_additive
    (S ⋙ algebraModules.{c, v, r} R)

/-- Termwise localized extension on strict towers.
Source: Stacks 03DI--03DJ (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev towerExtension :=
  CategoryTheory.StrictReduction.termwise (localizedSystemExtension.{c, v, r} R V)

/-- Additivity of the actual termwise localized extension.
Source: Stacks 03DJ (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance towerExtension_additive : (towerExtension.{c, v, r} R V).Additive :=
  inferInstanceAs ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (localizedSystemExtension.{c, v, r} R V)).Additive

/-- Finite limits for the recorded termwise extension construction.
Source: Stacks 03DJ (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance towerExtension_limits : PreservesFiniteLimits (towerExtension.{c, v, r} R V) :=
  CategoryTheory.StrictReduction.termwise_limits _

/-- Finite colimits for the recorded termwise extension construction.
Source: Stacks 03DJ (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance towerExtension_colimits : PreservesFiniteColimits (towerExtension.{c, v, r} R V) :=
  CategoryTheory.StrictReduction.termwise_colimits _

/-- Ordinary reduction is functorial in the whole algebra tower.
Source: Stacks 03EK (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def reductionFamily : AlgebraTowers.{c, v, r} R ⥤
    Modules.{c, v, r} R ⥤ (ℕᵒᵖ ⥤ Modules.{c, v, r} R) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (algebraModules.{c, v, r} R) ⋙
    (curriedTensor (ℕᵒᵖ ⥤ Modules.{c, v, r} R)).flip ⋙
      (Functor.whiskeringLeft (Modules.{c, v, r} R)
        (ℕᵒᵖ ⥤ Modules.{c, v, r} R) (ℕᵒᵖ ⥤ Modules.{c, v, r} R)).obj
          (Functor.const ℕᵒᵖ)

/-- Additivity of the same family presentation of reduction.
Source: Stacks 03EK (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance reductionFamily_additive (S : AlgebraTowers.{c, v, r} R) :
    ((reductionFamily.{c, v, r} R).obj S).Additive :=
  reduction_additive.{c, v, r} R S

/-- The standard localization size convention for module sheaves.
Source: Stacks 05RU (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance modulesDerived {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K RingCat.{r}) [HasSheafify K AddCommGrpCat.{r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] :
    HasDerivedCategory.{max c v (r + 1)} (SheafOfModules.{r} A) :=
  HasDerivedCategory.standard _

/-- Localize complexes of strict towers, in the standard size convention.
Source: Stacks 05RU (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance towersDerived {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K RingCat.{r}) [HasSheafify K AddCommGrpCat.{r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] :
    HasDerivedCategory.{max c v (r + 1)} (ℕᵒᵖ ⥤ SheafOfModules.{r} A) :=
  HasDerivedCategory.standard _

/-- The existing ordinary derived category, in the standard size convention.
Source: Stacks 05RU (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev D := DerivedCategory (Modules.{c, v, r} R)

/-- The ordinary derived category of strict towers.
Source: Stacks 05RU (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev DT := DerivedCategory (ℕᵒᵖ ⥤ Modules.{c, v, r} R)

/-- Flat-term K-flat representatives, with the recorded predicates.
Source: Stacks 06YS (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def Resolving (P : CochainComplex (Modules.{c, v, r} R) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
    ∀ i : ℤ, IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R) (P.X i)

/-- A presentation of the derived strict reduction with its universal counit.
All fields describe the actual ordinary tensor tower; this record is produced
by the theorem, rather than assumed as a mathematical hypothesis.
Source: Stacks 06YS--06YU (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
structure ReductionModel where
  /-- Functoriality in coefficient towers and in derived modules. -/
  F : AlgebraTowers.{c, v, r} R ⥤ D.{c, v, r} R ⥤ DT.{c, v, r} R
  /-- The universal comparison with the specified ordinary tensor construction. -/
  ε : ∀ S : AlgebraTowers.{c, v, r} R,
    DerivedCategory.Q ⋙ F.obj S ⟶
      (reduction.{c, v, r} R S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- The left derived universal property fixes this model up to unique compatible iso. -/
  universal : ∀ S, (F.obj S).IsLeftDerivedFunctor (ε S)
    (HomologicalComplex.quasiIso (Modules.{c, v, r} R) (.up ℤ))
  /-- Every flat-term K-flat representative computes reduction. -/
  computes : ∀ S P, Resolving.{c, v, r} R P → IsIso ((ε S).app P)
  /-- The computation comparisons are natural in every coefficient-tower map. -/
  coefficient : ∀ (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T)
    (P : CochainComplex (Modules.{c, v, r} R) ℤ),
    (F.map a).app (DerivedCategory.Q.obj P) ≫ (ε T).app P =
      (ε S).app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ((reductionFamily.{c, v, r} R).map a)
          (.up ℤ)).app P)

open Classical in
/-- A summand of extension, followed by the canonical sheafification unit.
Source: Stacks 03DI (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def extensionSection
    (M : Modules.{max c v, v, r} (R.over V)) (W : C) (a : W ⟶ V)
    (x : M.val.obj (op (Over.mk a))) :
    ((localizedSystemExtension.{c, v, r} R V).obj M).val.obj (op W) :=
  ((PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c}
    (𝟙 (ring.{c, v, r} R).obj)).unit.app
      ((extensionByZeroPresheaf (ring.{c, v, r} R) V).obj M)).app (op W)
        (DirectSum.of _ a x)

/-- Pure tensors in the existing localization monoidal structure.
Source: Stacks 03EK (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def pure (M N : Modules.{c, v, r} R) (W : Cᵒᵖ)
    (x : M.val.obj W) (y : N.val.obj W) : (M ⊗ N).val.obj W :=
  (tensorObjIsoSheafification (R := R) M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ring.{c, v, r} R).obj)).unit.app
      (M.val ⊗ N.val)).app W (x ⊗ₜ[R.obj.obj W] y))

/-- The specified generator normalization of the ordinary strict comparison.
The case s=1 is the scalar-unit clause, and the NatIso already commutes with
all transitions before localization.
Source: Stacks 0E8I (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def OrdinaryNormalized
    (S : AlgebraTowers.{c, v, r} R)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V) : Prop :=
  ∀ (M : Modules.{max c v, v, r} (R.over V)) (n : ℕᵒᵖ)
    (W : C) (a : W ⟶ V) (p : M.val.obj (op (Over.mk a)))
    (s : (S.obj n).right.obj.obj (op W)),
    ((η.hom.app M).app n).val.app (op W)
      (pure.{c, v, r} R _ _ (op W) (extensionSection.{c, v, r} R V M W a p) s) =
      extensionSection.{c, v, r} R V _ W a
        (pure.{max c v, v, r} (R.over V) _ _ (op (Over.mk a)) p s)

/-- Apply the strict module comparison in each degree, using the actual additive instances.
Source: Stacks 0E8I (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def comparisonOnComplexes
    (S : AlgebraTowers.{c, v, r} R)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V) :=
  letI := reduction_additive.{c, v, r} R S
  letI := reduction_additive.{max c v, v, r} (R.over V)
    (S ⋙ sliceAlgebras.{c, v, r} R V)
  letI := towerExtension_additive.{c, v, r} R V
  NatIso.mapHomologicalComplex η (.up ℤ)

/-- Representative normalization uses exactly the two universal computation counits
and the exact functors' localization comparisons. It quantifies over every
flat-term K-flat representative, hence retains representative independence.
Source: Stacks 06YU and 0E8I
(blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def DerivedNormalized
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V)
    (ρ : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ m.F.obj S ≅
      mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        (towerExtension.{c, v, r} R V).mapDerivedCategory) : Prop :=
  ∀ (P : CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ),
    Resolving.{max c v, v, r} (R.over V) P →
      (m.F.obj S).map
        ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app P) ≫
      (m.ε S).app
        (((localizedSystemExtension.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((comparisonOnComplexes.{c, v, r} R V S η).hom.app P) =
      ρ.hom.app (DerivedCategory.Q.obj P) ≫
      (towerExtension.{c, v, r} R V).mapDerivedCategory.map
        ((mV.ε (S ⋙ sliceAlgebras.{c, v, r} R V)).app P) ≫
      (towerExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app
        (((reduction.{max c v, v, r} (R.over V)
          (S ⋙ sliceAlgebras.{c, v, r} R V)).mapHomologicalComplex (.up ℤ)).obj P)

/-- Existing scalar restriction, with the coefficient size fixed explicitly.
Source: Stacks 03DA (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev scalars (A : Under R) : Modules.{c, v, r} A.right ⥤ Modules.{c, v, r} R :=
  restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map A.hom)

/-- Restriction of scalars preserves finite limits by the recorded coefficient adjunction.
Source: Stacks 03DA (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance scalars_limits (A : Under R) : PreservesFiniteLimits (scalars.{c, v, r} R A) :=
  letI := modulesDerived.{c, v, max c v r} (ring.{c, v, r} R)
  letI := modulesDerived.{c, v, max c v r} (ring.{c, v, r} A.right)
  (sheafRingDerivedCoefficientAdjunction.{max (c + 1) (v + 1) (r + 1), max c v r, c, v}
    A.hom).choose

/-- Restriction of scalars preserves finite colimits by the recorded coefficient adjunction.
Source: Stacks 03DA (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
instance scalars_colimits (A : Under R) : PreservesFiniteColimits (scalars.{c, v, r} R A) :=
  letI := modulesDerived.{c, v, max c v r} (ring.{c, v, r} R)
  letI := modulesDerived.{c, v, max c v r} (ring.{c, v, r} A.right)
  (sheafRingDerivedCoefficientAdjunction.{max (c + 1) (v + 1) (r + 1), max c v r, c, v}
    A.hom).choose_spec.choose

/-- The existing cochain presentation of scalar extension.
Source: Stacks 06YY (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev ScalarModel (A : Under R) :=
  letI := modulesDerived.{c, v, max c v r} (ring.{c, v, r} R)
  letI := modulesDerived.{c, v, max c v r} (ring.{c, v, r} A.right)
  DerivedChangeOfRingsCochainModel.{c, v, max c v r,
    max (c + 1) (v + 1) (r + 1), max (c + 1) (v + 1) (r + 1)} A.hom

/-- Pure scalar tensors, transported through the prescribed ordinary-object equation.
Source: Stacks 03D7 (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def scalarPure (A : Under R) (e : ScalarModel.{c, v, r} R A)
    (M : Modules.{c, v, r} R) (W : Cᵒᵖ)
    (s : A.right.obj.obj W) (p : M.val.obj W) : (e.E.obj M).val.obj W :=
  (eqToHom (C := Modules.{c, v, r} A.right) (e.obj_eq M).symm).val.app W
    ((CategoryTheory.toSheafify J (changeOfRingsPresheaf A.hom M).presheaf).app W
      (s ⊗ₜ[R.obj.obj W, (A.hom.hom.app W).hom] p))

/-- Evaluation of an actual strict tower at its n+1-st level.
Source: Stacks 05RV (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
abbrev evaluation (n : ℕᵒᵖ) := (CategoryTheory.evaluation ℕᵒᵖ (Modules.{c, v, r} R)).obj n

/-- The canonical normalization comparing tensor evaluation with scalar extension.
Source: Stacks 03D7, 03EK (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def EvaluationOrdinaryNormalized (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (e : ScalarModel.{c, v, r} R (S.obj n))
    (τ : reduction.{c, v, r} R S ⋙ evaluation.{c, v, r} R n ≅
      e.E ⋙ scalars.{c, v, r} R (S.obj n)) : Prop :=
  ∀ (M : Modules.{c, v, r} R) (W : Cᵒᵖ)
    (p : M.val.obj W) (s : (S.obj n).right.obj.obj W),
    (τ.hom.app M).val.app W (pure.{c, v, r} R _ _ W p s) =
      scalarPure.{c, v, r} R (S.obj n) e M W s p

/-- Canonical comparison from evaluated derived tensor to scalar extension followed
by scalar restriction, including its counit equation on every flat-term K-flat model.
Source: Stacks 06YU (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
structure EvaluationModel (m : ReductionModel.{c, v, r} R)
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ) where
  /-- The existing, genuinely coefficient-linear derived extension. -/
  scalar : ScalarModel.{c, v, r} R (S.obj n)
  /-- The canonical ordinary identification of underlying tensor with scalar extension. -/
  ordinary : reduction.{c, v, r} R S ⋙ evaluation.{c, v, r} R n ≅
    scalar.E ⋙ scalars.{c, v, r} R (S.obj n)
  /-- Its pure-tensor formula fixes the ordinary comparison. -/
  ordinary_normalized : EvaluationOrdinaryNormalized.{c, v, r} R S n scalar ordinary
  /-- Evaluation after localization, identified with scalar restriction of extension. -/
  derived : m.F.obj S ⋙ (evaluation.{c, v, r} R n).mapDerivedCategory ≅
    scalar.T ⋙ (scalars.{c, v, r} R (S.obj n)).mapDerivedCategory
  /-- The identification uses the universal computation counits, not a chosen resolution. -/
  normalized : ∀ (P : CochainComplex (Modules.{c, v, r} R) ℤ),
    Resolving.{c, v, r} R P →
    (evaluation.{c, v, r} R n).mapDerivedCategory.map ((m.ε S).app P) ≫
      (evaluation.{c, v, r} R n).mapDerivedCategoryFactors.hom.app
        (((reduction.{c, v, r} R S).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (scalars.{c, v, r} R (S.obj n)).mapDerivedCategory.map (scalar.ε.app P) ≫
      (scalars.{c, v, r} R (S.obj n)).mapDerivedCategoryFactors.hom.app
        ((scalar.E.mapHomologicalComplex (.up ℤ)).obj P)

/-- Exact evaluation commutes with termwise extension, with its canonical localization
comparison. Source: Stacks 015F
(blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def evaluationExtensionDerived (n : ℕᵒᵖ) :
    (towerExtension.{c, v, r} R V).mapDerivedCategory ⋙
      (evaluation.{c, v, r} R n).mapDerivedCategory ≅
    (evaluation.{max c v, v, r} (R.over V) n).mapDerivedCategory ⋙
      (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory :=
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionLimits.{c, v, r} R V
  letI := localizedSystemExtensionColimits.{c, v, r} R V
  (Functor.mapDerivedCategoryCompIso (towerExtension.{c, v, r} R V)
    (evaluation.{c, v, r} R n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl) :
          towerExtension.{c, v, r} R V ⋙ evaluation.{c, v, r} R n ≅
            evaluation.{max c v, v, r} (R.over V) n ⋙
              localizedSystemExtension.{c, v, r} R V) ≪≫
        Functor.mapDerivedCategoryCompIso (evaluation.{max c v, v, r} (R.over V) n)
          (localizedSystemExtension.{c, v, r} R V)

/-- Normalization of scalar restriction through localized extension: the same summand
and section are preserved. Source: Stacks 03DI, 03CY
(blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def ScalarExtensionNormalized (A : Under R)
    (θ : scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} A.right V ⋙ scalars.{c, v, r} R A) : Prop :=
  ∀ (N : Modules.{max c v, v, r} (A.right.over V)) (W : C) (a : W ⟶ V)
    (x : N.val.obj (op (Over.mk a))),
    (θ.hom.app N).val.app (op W)
      (extensionSection.{c, v, r} R V _ W a x) =
      extensionSection.{c, v, r} A.right V N W a x

/-- The canonical derived scalar-restriction/extension comparison.
Source: Stacks 015F (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def scalarExtensionDerived (A : Under R)
    (θ : scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} A.right V ⋙ scalars.{c, v, r} R A) :
    (scalars.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj A)).mapDerivedCategory ⋙
        (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ≅
      (localizedSystemExtension.{c, v, r} A.right V).mapDerivedCategory ⋙
        (scalars.{c, v, r} R A).mapDerivedCategory :=
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionLimits.{c, v, r} R V
  letI := localizedSystemExtensionColimits.{c, v, r} R V
  letI := localizedSystemExtensionAdditive.{c, v, r} A.right V
  letI := localizedSystemExtensionLimits.{c, v, r} A.right V
  letI := localizedSystemExtensionColimits.{c, v, r} A.right V
  (Functor.mapDerivedCategoryCompIso
    (scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A))
    (localizedSystemExtension.{c, v, r} R V)).symm ≪≫
      Functor.mapDerivedCategoryNatIso θ ≪≫
        Functor.mapDerivedCategoryCompIso (localizedSystemExtension.{c, v, r} A.right V)
          (scalars.{c, v, r} R A)

/-- Degreewise scalar-linear comparison with explicit exact-extension additivity.
Source: Stacks 0E8I (blueprint: def-sf-localized-strict-tensor-comparison-data). -/
def scalarComparisonOnComplexes (A : Under R)
    (e : ScalarModel.{c, v, r} R A)
    (eV : ScalarModel.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj A))
    (σ : localizedSystemExtension.{c, v, r} R V ⋙ e.E ≅
      eV.E ⋙ localizedSystemExtension.{c, v, r} A.right V) :=
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionAdditive.{c, v, r} A.right V
  letI := e.additive
  letI := eV.additive
  NatIso.mapHomologicalComplex σ (.up ℤ)

end SheafOfModules.LocalizedStrictTensor
