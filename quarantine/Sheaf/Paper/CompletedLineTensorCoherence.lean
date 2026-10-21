/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.InvertibleTensorScalarExtension
public import Sheaf.Paper.ScalarExtensionBinaryCoherence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Paper.SfScalarExtensionComposition

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

/-! # Completed scalar extension and compatible coefficient lines

Source: Bhatt--Scholze, Definitions 3.4.10 and 3.5.2, Lemma 3.4.12,
Proposition 3.5.1; blueprint sk-def-sp-tate-twist-locally-free, Proof (3).
(blueprint: lem-pur-completed-line-tensor-coherence)

## Main definitions and statements

* `power`, `tensor`, `pairData`: signed lines and normalized ordinary comparisons.
* `beta`, `associator`, `unit`: conjugation by the recorded strict-completion comparison.
* `tower`, `beta_natural_evaluation`, `scalar_coherence`: the integral coherence equations.
* `rational_tower`, `rational_evaluation`, `rational_repeated`: their rationalized forms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

/-- The signed power of a coefficient line, using the recorded ordinary powers and Hom.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def power (L : integralTowerModules l E X) : ℤ → integralTowerModules l E X
  | .ofNat n => SheafOfModules.scalarTensorPower
      (completedIntegralCommRingSheafUnrestricted l E X) L n
  | .negSucc n => SheafOfModules.homObj.{max u (t + 1), t, t + 1, max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      (SheafOfModules.scalarTensorPower
        (completedIntegralCommRingSheafUnrestricted l E X) L (n + 1))
      (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)))

/-- Ordinary tensor with the signed power, before deriving or completing.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
def sheaf (L : integralTowerModules l E X) (m : ℤ) :
    integralTowerModules l E X ⥤ integralTowerModules l E X :=
  SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1), max u (t + 1)}
    (A := completedIntegralCommRingSheafUnrestricted l E X)
    (power l E X L m)

/-- Signed powers are lines, so their ordinary tensor functors are exact and additive.
Source: Stacks 03EK, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: trivialize L on a covering. Every tensor power and its internal dual is the
unit there, including exponent zero. Tensor is thus locally the identity. Exactness
is local, and additivity follows on the sectionwise pure tensors and sheafification. -/
theorem exact (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (sheaf l E X L m).Additive ∧ PreservesFiniteLimits (sheaf l E X L m) ∧
      PreservesFiniteColimits (sheaf l E X L m) := by
  sorry

/-- Additivity of signed line tensor. Source: blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
instance additive (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (sheaf l E X L m).Additive := (exact l E X L m).1

/-- Left exactness of signed line tensor. Source: blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
instance finiteLimits (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) : PreservesFiniteLimits (sheaf l E X L m) := (exact l E X L m).2.1

/-- Right exactness of signed line tensor. Source: blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
instance finiteColimits (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) : PreservesFiniteColimits (sheaf l E X L m) := (exact l E X L m).2.2

/-- Tensor on all unbounded complexes is termwise tensor by the signed line.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def complex (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    CochainComplex (integralTowerModules l E X) ℤ ⥤
      CochainComplex (integralTowerModules l E X) ℤ :=
  (sheaf l E X L m).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exact derived tensor functor T, with its canonical localization comparison.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def tensor (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    DerivedCategory (integralTowerModules l E X) ⥤
      DerivedCategory (integralTowerModules l E X) :=
  (sheaf l E X L m).mapDerivedCategory


/-- Evaluation of signed powers on sections; negative powers are the recorded sheaf Hom.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-tensor-coherence). -/
def pairing (L : integralTowerModules l E X) (m : ℤ) (U : X.ProEtᵒᵖ) :
    (power l E X L m).val.obj U → (power l E X L (-m)).val.obj U →
      (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U :=
  match m with
  | .ofNat 0 => fun a b ↦
      (@id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) a) *
        (@id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) b)
  | .ofNat (_n + 1) => fun a b ↦ b.app (op (Over.mk (𝟙 U.unop))) a
  | .negSucc _n => fun a b ↦ a.app (op (Over.mk (𝟙 U.unop))) b

/-- Pure tensor in the exact signed-line functor, with its source and target explicit.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
def tmul (L : integralTowerModules l E X) (m : ℤ) (M : integralTowerModules l E X)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) (a : (power l E X L m).val.obj U) :
    ((sheaf l E X L m).obj M).val.obj U :=
  SheafOfModules.siteSheafTensorTmul
    (A := completedIntegralCommRingSheafUnrestricted l E X) M (power l E X L m) U x a

/-- The existing module action, with the completed coefficient section type explicit.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
def smul (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
    (x : M.val.obj U) : M.val.obj U :=
  @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x

/-- The specified evaluation isomorphism, characterized before localization.
Source: Stacks 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: sheaf Hom evaluation defines the balanced pairing. In a basis and its dual
it multiplies coefficients, hence is an isomorphism. The resulting local inverse
glues. Associativity followed by evaluation and the unitor gives the displayed
natural isomorphism. Pure tensors generate locally, proving uniqueness. -/
theorem evaluation_existsUnique (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    ∃! e : sheaf l E X L m ⋙ sheaf l E X L (-m) ≅ 𝟭 _,
      ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
        (x : M.val.obj U) (a : (power l E X L m).val.obj U)
        (b : (power l E X L (-m)).val.obj U),
        (e.hom.app M).val.app U
            (tmul l E X L (-m) ((sheaf l E X L m).obj M) U
              (tmul l E X L m M U x a) b) =
          smul l E X M U (pairing l E X L m U a b) x := by
  sorry

/-- The canonical sheaf evaluation; its full section formula determines it uniquely.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-tensor-coherence). -/
def evaluation (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    sheaf l E X L m ⋙ sheaf l E X L (-m) ≅ 𝟭 (integralTowerModules l E X) :=
  (evaluation_existsUnique l E X L m).exists.choose

/-- The evaluation on the unbounded derived category, with the canonical localization units.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def epsilon (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    tensor l E X L m ⋙ tensor l E X L (-m) ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso (sheaf l E X L m) (sheaf l E X L (-m))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (evaluation l E X L m) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- Tensor by a signed line preserves the specified augmented quotient-tower completeness.
Source: Bhatt--Scholze, Definition 3.5.2; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: tensor by the line and its internal dual are inverse exact equivalences.
Their derived equivalences preserve products. Balanced tensor reassociation identifies
the reduction tower of the twist with the twisted reduction tower, respecting every
transition and the augmentation x mapped to 1 tensor x. Apply the equivalence to the
augmented Roos triangle. Its first map is the prescribed quotient map and its second
map is 1 minus the transition shift, proving precisely the recorded completeness. -/
theorem complete (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E X ((tensor l E X L m).obj K) := by
  sorry


variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

/-- The canonical binary tensor comparison; its pure-tensor formula determines it uniquely.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
def binary : SheafOfModules.ScalarExtensionTensorCore.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E X)
    (completedIntegralCommRingSheafUnrestricted l F X) (completedCoefficientMap l E F ι X) :=
  Classical.choice (SheafOfModules.exists_scalarExtensionTensorCore.{t + 1, t, max u (t + 1)}
  (completedIntegralCommRingSheafUnrestricted l E X)
  (completedIntegralCommRingSheafUnrestricted l F X) (completedCoefficientMap l E F ι X))

/-- Canonical exact localization factor for the signed-line functor.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def factors (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    DerivedCategory.Q ⋙ tensor l E X L m ≅ complex l E X L m ⋙ DerivedCategory.Q :=
  (sheaf l E X L m).mapDerivedCategoryFactors

/-- The ordinary sheaf comparison applied termwise, without derived choices.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def comparisonComplex (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1] (m : ℤ)
    (e : sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m) :
    complex l E X L m ⋙ completedOrdinaryScalarComplex l E F ι X ≅
      completedOrdinaryScalarComplex l E F ι X ⋙ complex l F X N m :=
  NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

/-- Ordinary scalar associativity applied termwise, with explicit complex functors.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def scalarAssociatorComplex
    (e : completedOrdinaryScalarExtension l E F ι X ⋙
      completedOrdinaryScalarExtension l F G j X ≅
        completedOrdinaryScalarExtension l E G (j.comp ι) X) :
    completedOrdinaryScalarComplex l E F ι X ⋙ completedOrdinaryScalarComplex l F G j X ≅
      completedOrdinaryScalarComplex l E G (j.comp ι) X :=
  NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)

attribute [local irreducible] binary epsilon sheaf tensor complex pairing
  factors comparisonComplex scalarAssociatorComplex smul tmul
  SheafOfModules.ScalarExtensionTensorCore.power SheafOfModules.scalarExtensionSection
  completedScalarIdentityMultiplication completedScalarIdentityUnit
  completedOrdinaryScalarComplex
  completedScalarChangeData completedScalarChainComparison completedScalarComparison

/-- Signed-power scalar maps and their specified ordinary derived tensor comparisons.
All normalization equations are on actual sheafified tensors and the universal counits.
Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def PairData (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1] :=
  (∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m) ×
  (∀ m : ℤ,
    sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m) ×
  (∀ m : ℤ, tensor l E X L m ⋙ completedDerivedScalarExtension l E F ι X ≅
    completedDerivedScalarExtension l E F ι X ⋙ tensor l F X N m)

variable {l E X F ι}

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def PairData.line {L : integralTowerModules l E X} [L.IsFiniteLocallyFreeOfRank 1]
    {N : integralTowerModules l F X} [N.IsFiniteLocallyFreeOfRank 1]
    (d : PairData l E X F ι L N) :
    ∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m := d.1

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def PairData.ordinarySheaf {L : integralTowerModules l E X} [L.IsFiniteLocallyFreeOfRank 1]
    {N : integralTowerModules l F X} [N.IsFiniteLocallyFreeOfRank 1]
    (d : PairData l E X F ι L N) :
    ∀ m : ℤ,
    sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m := d.2.1

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def PairData.ordinary {L : integralTowerModules l E X} [L.IsFiniteLocallyFreeOfRank 1]
    {N : integralTowerModules l F X} [N.IsFiniteLocallyFreeOfRank 1]
    (d : PairData l E X F ι L N) :
    ∀ m : ℤ, tensor l E X L m ⋙ completedDerivedScalarExtension l E F ι X ≅
    completedDerivedScalarExtension l E F ι X ⋙ tensor l F X N m := d.2.2

variable (l E X F ι)

/-- The complete pure-tensor and K-flat-counit normalization of the ordinary data.
Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def IsPairNormalized (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) : Prop :=
  (∀ n : ℕ,
    (d.line (Int.ofNat n)).hom = ((binary l E X F ι).power L n).hom ≫
      SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingSheafUnrestricted l F X) b.hom n) ∧
  (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (f : (power l E X L (-Int.ofNat (n + 1))).val.obj U)
      (x : (power l E X L (Int.ofNat (n + 1))).val.obj U),
    pairing l F X N (Int.ofNat (n + 1)) U
      ((d.line (Int.ofNat (n + 1))).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U t x))
      ((d.line (-Int.ofNat (n + 1))).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U s f)) =
      s * t * (completedCoefficientMap l E F ι X).hom.app U
        (pairing l E X L (Int.ofNat (n + 1)) U x f)) ∧
  (∀ (m : ℤ) (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (x : M.val.obj U) (a : (power l E X L m).val.obj U),
    ((d.ordinarySheaf m).hom.app M).val.app U
        (completedScalarTensorSection l E F ι X ((sheaf l E X L m).obj M) U s
          (tmul l E X L m M U x a)) =
      tmul l F X N m ((completedOrdinaryScalarExtension l E F ι X).obj M) U
        (completedScalarTensorSection l E F ι X M U s x)
        ((d.line m).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a))) ∧
  (∀ (m : ℤ)
      (P : (integralOperationsGoodComplex l E X).FullSubcategory),
    HEq ((completedDerivedScalarExtension l E F ι X).map
        ((factors l E X L m).hom.app P.obj) ≫
        completedScalarCounit l E F ι X ((complex l E X L m).obj P.obj) ≫
        DerivedCategory.Q.map
          ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app P.obj))
      ((d.ordinary m).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (tensor l F X N m).map (completedScalarCounit l E F ι X P.obj) ≫
        (factors l F X N m).hom.app
          ((completedOrdinaryScalarComplex l E F ι X).obj P.obj)))

/-- Existence and uniqueness of all ordinary signed-line comparisons with their
representative formulas. Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: tensor powers of b use the canonical binary comparison, including its
multiplication unitor at zero. The negative map is uniquely determined by evaluation
and becomes an isomorphism after trivializing the line. Define the ordinary comparison
on pure tensors by ((x tensor a) tensor s) mapped to (x tensor s) tensor b_m(a tensor 1).
Balancedness and sheafification give an isomorphism natural in the module. A line is
flat; tensor with it preserves flat-term K-flat complexes. Apply the K-flat localization
equivalence, using the specified universal counits. The displayed equation fixes the
derived comparison uniquely and proves independence from the representative. -/
theorem pairData_existsUnique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∃! p : PairData l E X F ι L N, IsPairNormalized l E X F ι L N b p := by
  sorry

/-- The unique normalized ordinary signed-line comparison package.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def pairData (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) : PairData l E X F ι L N :=
  (pairData_existsUnique l E X F ι L N b).exists.choose

/-- The specified chi, viewed as an isomorphism only at a derived-complete input.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def chi (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (completedDerivedScalarExtension l E F ι X).obj K ≅
      (integralScalarExtensionOfUniverses l E F ι X).obj K :=
  @asIso _ _ _ _ ((completedScalarComparison l E F ι X).app K)
    ((finiteFreeCompletedScalarComparison l E F ι X).2.1 K hK).1

/-- The completed comparison beta is exactly the specified conjugation by chi.
This construction uses no inverse chain map to completion.
Source: Bhatt--Scholze, Proposition 3.5.1; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def beta (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (integralScalarExtensionOfUniverses l E F ι X).obj ((tensor l E X L m).obj K) ≅
      (tensor l F X N m).obj ((integralScalarExtensionOfUniverses l E F ι X).obj K) :=
  (chi l E X F ι _ (complete l E X L m K hK)).symm ≪≫
    ((pairData l E X F ι L N b).ordinary m).app K ≪≫
      (tensor l F X N m).mapIso (chi l E X F ι K hK)


attribute [local irreducible] beta chi pairData power evaluation

/-- Completed extension preserves completeness on complete inputs.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the finite-free comparison makes ordinary extension complete and identifies
it with the specified strict completion. Transport its augmented Roos triangle through
that isomorphism, with the canonical quotient legs. -/
theorem extension_complete (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l F X
      ((integralScalarExtensionOfUniverses l E F ι X).obj K) := by
  sorry

/-- Ordinary scalar associativity, fixed on sheafified tensors and universal K-flat counits.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData :=
  (completedOrdinaryScalarExtension l E F ι X ⋙
    completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X) ×
  (completedDerivedScalarExtension l E F ι X ⋙
    completedDerivedScalarExtension l F G j X ≅
      completedDerivedScalarExtension l E G (j.comp ι) X)

variable {l E X F ι G j}

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData.sheaf (d : AssociatorData l E X F ι G j) :
    completedOrdinaryScalarExtension l E F ι X ⋙
    completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X := d.1

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData.derived (d : AssociatorData l E X F ι G j) :
    completedDerivedScalarExtension l E F ι X ⋙
    completedDerivedScalarExtension l F G j X ≅
      completedDerivedScalarExtension l E G (j.comp ι) X := d.2

variable (l E X F ι G j)

/-- Balanced-tensor multiplication and the universal-counit normalization.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def IsAssociatorNormalized (d : AssociatorData l E X F ι G j) : Prop :=
  (∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
      (x : M.val.obj U),
    (d.sheaf.hom.app M).val.app U
        (completedScalarTensorSection l F G j X _ U t
          (completedScalarTensorSection l E F ι X M U s x)) =
      completedScalarTensorSection l E G (j.comp ι) X M U
        (t * (completedCoefficientMap l F G j X).hom.app U s) x) ∧
  (∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
    (completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P.obj) ≫
        completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
        DerivedCategory.Q.map
          ((scalarAssociatorComplex l E X F ι G j d.sheaf).hom.app P.obj) =
      d.derived.hom.app (DerivedCategory.Q.obj P.obj) ≫
        completedScalarCounit l E G (j.comp ι) X P.obj)

/-- Ordinary scalar associators with exactly the prescribed balanced normalization.
Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the balanced map t tensor (s tensor x) mapped to t*j(s) tensor x has inverse
u tensor x mapped to u tensor (1 tensor x). The two maps commute with restrictions
and differentials. Sheafification preserves their inverse equations. Ordinary extension
preserves flat-term K-flat complexes, so localization with the specified counits gives
the unique derived comparison. Local generation and the localization equivalence prove
uniqueness of the entire package. -/
theorem associatorData_existsUnique :
    ∃! a : AssociatorData l E X F ι G j, IsAssociatorNormalized l E X F ι G j a := by
  sorry

/-- The normalized ordinary scalar associator, including its representative.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def associatorData : AssociatorData l E X F ι G j :=
  (associatorData_existsUnique l E X F ι G j).exists.choose

/-- The completed associator is ordinary associativity conjugated by the specified chi.
Source: Bhatt--Scholze, Proposition 3.5.1; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def associator (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (integralScalarExtensionOfUniverses l F G j X).obj
        ((integralScalarExtensionOfUniverses l E F ι X).obj K) ≅
      (integralScalarExtensionOfUniverses l E G (j.comp ι) X).obj K :=
  (chi l F X G j _ (extension_complete l E X F ι K hK)).symm ≪≫
    (completedDerivedScalarExtension l F G j X).mapIso (chi l E X F ι K hK).symm ≪≫
    (associatorData l E X F ι G j).derived.app K ≪≫ chi l E X G (j.comp ι) K hK

attribute [local irreducible] associator associatorData

/-- Naturality and compatibility with evaluation for exactly the conjugated beta.
Source: blueprint Proof (3), completed line/scalar coherence
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: every factor defining beta is natural and invertible on complete inputs;
completeness of all intermediate twists follows from complete. To check evaluation,
precompose by chi at T_-m T_m K. Substitute beta*chi_T = T(chi)*bar-beta twice.
Naturality of evaluation moves chi outside. On ordinary pure tensors both paths
are multiplication by the evaluated line scalar, by the negative clause of
IsPairNormalized. Naturality
of chi identifies this with C(epsilon)*chi. Cancel the invertible chi. The proof
includes zero, positive and negative m and never inverts a chain completion map. -/
theorem beta_natural_evaluation (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    (∀ (m : ℤ) (K M : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K)
      (hM : IsDerivedCompleteUnrestricted l E X M) (f : K ⟶ M),
      (integralScalarExtensionOfUniverses l E F ι X).map ((tensor l E X L m).map f) ≫
          (beta l E X F ι L N b m M hM).hom =
        (beta l E X F ι L N b m K hK).hom ≫
          (tensor l F X N m).map ((integralScalarExtensionOfUniverses l E F ι X).map f)) ∧
    (∀ (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (beta l E X F ι L N b (-m) ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).hom ≫
        (tensor l F X N (-m)).map (beta l E X F ι L N b m K hK).hom ≫
        (epsilon l F X N m).hom.app ((integralScalarExtensionOfUniverses l E F ι X).obj K) =
      (integralScalarExtensionOfUniverses l E F ι X).map ((epsilon l E X L m).hom.app K)) := by
  sorry

/-- The ordinary derived multiplication unitor, fixed by the recorded chain unitor.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: multiplication and x mapped to 1 tensor x are inverse on module sheaves.
They commute with differentials and restrictions. Localization with the canonical
K-flat counit gives the unique derived unitor with the displayed normalization. -/
theorem ordinaryUnit_existsUnique :
    ∃! e : completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅ 𝟭 _,
      ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
        e.hom.app (DerivedCategory.Q.obj P.obj) =
          completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P.obj ≫
            DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P.obj) :=
              by
  sorry

/-- The ordinary multiplication unitor with its prescribed representative.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def ordinaryUnit :
    completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅
      𝟭 (DerivedCategory (integralTowerModules l E X)) :=
  (ordinaryUnit_existsUnique l E X).exists.choose

/-- The completed identity comparison is the unitor conjugated by chi.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def unit (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) X).obj K ≅ K :=
  (chi l E X E (AlgHom.id ℚ_[l] E) K hK).symm ≪≫ (ordinaryUnit l E X).app K

attribute [local irreducible] unit ordinaryUnit

/-- The inverse completed unit is exactly the natural completeness map, including
its zero shifted-product component, and is natural on complete inputs.
Source: Bhatt--Scholze, Definition 3.5.2; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the finite-free comparison identifies chi with the chain multiplication
followed by the directly constructed quotient augmentation. Substitute the unitor's
normalization and cancel multiplication. This gives the displayed representative
formula. Naturality follows from the naturality of chi and ordinary multiplication. -/
theorem unit_normalization :
    (∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
      (hP : IsDerivedCompleteUnrestricted l E X (DerivedCategory.Q.obj P.obj)),
      (unit l E X (DerivedCategory.Q.obj P.obj) hP).inv ≫
          (integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E) X).hom.app P =
        DerivedCategory.Q.map ((completedScalarIdentityUnit l E X).app P.obj)) ∧
    (∀ (K M : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K)
      (hM : IsDerivedCompleteUnrestricted l E X M) (f : K ⟶ M),
      (integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) X).map f ≫
          (unit l E X M hM).hom = (unit l E X K hK).hom ≫ f) := by
  sorry

/-- Both unit laws and the scalar associativity pentagon on derived-complete inputs.
Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: ordinary associators multiply the scalar factors. For three transitions both
routes send u tensor (t tensor (s tensor x)) to u*k(t)*k(j(s)) tensor x. Multiplication
units obey both unit laws. These identities descend from pure tensors through
sheafification and K-flat localization. Conjugating by successive chi maps identifies
the completed and ordinary composites. Expand each completed edge, move intermediate
chi maps by naturality and cancel inverse pairs. This reduces the completed pentagon
and both unit equations to the ordinary ones. Repeated fields use the actual unit
isomorphisms, including their natural completeness maps, and no strict equality C_ii=1. -/
theorem scalar_coherence :
    (∀ (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (associator l E X E (AlgHom.id ℚ_[l] E) F ι K hK).hom =
        (integralScalarExtensionOfUniverses l E F ι X).map (unit l E X K hK).hom) ∧
    (∀ (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (associator l E X F ι F (AlgHom.id ℚ_[l] F) K hK).hom =
        (unit l F X ((integralScalarExtensionOfUniverses l E F ι X).obj K)
          (extension_complete l E X F ι K hK)).hom) ∧
    (∀ (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
      (k : G →ₐ[ℚ_[l]] H) (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (integralScalarExtensionOfUniverses l G H k X).map
          (associator l E X F ι G j K hK).hom ≫
        (associator l E X G (j.comp ι) H k K hK).hom =
      (associator l F X G j H k ((integralScalarExtensionOfUniverses l E F ι X).obj K)
          (extension_complete l E X F ι K hK)).hom ≫
        (associator l E X F ι H (k.comp j) K hK).hom) := by
  sorry

/-- The completed line comparison commutes with a compatible three-field tower.
Source: blueprint Proof (3), final sentence
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the signed-power scalar maps are compatible with composition: for positive
powers use the normalized binary associator square, for negative powers evaluate on
positive powers and use the dual formula. On ordinary pure tensors, both tower paths
send ((x tensor a) tensor s) tensor t to (x tensor j(s)t) tensor b_20,m(a tensor 1).
For the completed square precompose by chi_21,C_10 * B_21(chi_10) at T_0,m K.
Substitute the definitions of beta and associator. Naturality moves intermediate chi
maps next to their inverses, which cancel, leaving the ordinary tower equality.
All objects at which chi is inverted are complete. Cancel the initial isomorphism. -/
theorem tower (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (P : integralTowerModules l G X) [P.IsFiniteLocallyFreeOfRank 1]
    (b10 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (b21 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l F G j X) N ≅ P)
    (b20 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E G (j.comp ι) X) L ≅ P)
    (hb : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t
        + 1)}
          (completedCoefficientMap l F G j X) N U t
          (b10.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max
            u (t + 1)}
            (completedCoefficientMap l E F ι X) L U s x))) =
        b20.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u
          (t + 1)}
          (completedCoefficientMap l E G (j.comp ι) X) L U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x))
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (integralScalarExtensionOfUniverses l F G j X).map
        (beta l E X F ι L N b10 m K hK).hom ≫
      (beta l F X G j N P b21 m
        ((integralScalarExtensionOfUniverses l E F ι X).obj K)
        (extension_complete l E X F ι K hK)).hom ≫
      (tensor l G X P m).map (associator l E X F ι G j K hK).hom =
    (associator l E X F ι G j ((tensor l E X L m).obj K)
        (complete l E X L m K hK)).hom ≫
      (beta l E X G (j.comp ι) L P b20 m K hK).hom := by
  sorry


/-- Repeated coefficient fields retain the prescribed line identification. After
transporting the signed line along this ordinary b-induced map the component is identity.
Source: blueprint Proof (3), tensor inverses with scalar conventions
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: substitute beta and the completed unit as conjugations by chi. Naturality
of the ordinary comparison moves the remaining chi through it; inverse pairs cancel.
The right side is the ordinary comparison induced by b and the multiplication unit,
so identifying its target line with its source makes this component the identity.
For the diagonal multiplication b this ordinary component is already identity, by
the pure-tensor unit square. Arbitrary b is not discarded by scalar normalization. -/
theorem repeated (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l E X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) X) L ≅ N)
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (unit l E X ((tensor l E X L m).obj K) (complete l E X L m K hK)).inv ≫
        (beta l E X E (AlgHom.id ℚ_[l] E) L N b m K hK).hom ≫
        (tensor l E X N m).map (unit l E X K hK).hom =
      (ordinaryUnit l E X).inv.app ((tensor l E X L m).obj K) ≫
        ((pairData l E X E (AlgHom.id ℚ_[l] E) L N b).ordinary m).hom.app K ≫
        (tensor l E X N m).map ((ordinaryUnit l E X).hom.app K) := by
  sorry

section Rational

variable (Y : AlgebraicGeometry.Scheme.{u})

/-- Precisely the conditional constructible-preservation hypothesis in the node.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def PreservesConstructible (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1] :
    Prop := ∀ (m : ℤ) (K : DerivedCategory (integralTowerModules l E Y)),
  sfIntegralConstructible l E Y K →
    sfIntegralConstructible l E Y ((tensor l E Y L m).obj K)

/-- Restriction of the actual line tensor to the recorded integral constructible category.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def integralTwist (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfIntegralConstructible l E Y).lift
    ((sfIntegralConstructible l E Y).ι ⋙ tensor l E Y L m)
    (fun K ↦ hL m K.obj K.property)

/-- The restriction is additive and linear for the recorded constant-section scalar action.
Source: Stacks 03EL; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: ordinary tensor maps scalar multiplication to the same scalar on pure tensors.
Sheafification and the exact derived localization preserve this equality. The full
subcategory inherits exactly the ambient Hom actions, so the same identities hold
for integralTwist. Additivity follows in the same way from tensor additivity. -/
theorem integralTwist_linear (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (integralTwist l E Y L hL m).Additive ∧
      (integralTwist l E Y L hL m).Linear (Padic.coefficientExtensionIntegers l E) := by
  sorry

/-- Additivity inherited by integral line tensor.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
instance integralTwistAdditive (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (integralTwist l E Y L hL m).Additive := (integralTwist_linear l E Y L hL m).1

/-- The constant-section coefficient action is preserved by integral line tensor.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
instance integralTwistLinear (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (integralTwist l E Y L hL m).Linear (Padic.coefficientExtensionIntegers l E) :=
  (integralTwist_linear l E Y L hL m).2

/-- The actual raw scalar-localized line tensor, with unchanged objects and tensor Hom maps.
Source: blueprint Proof (3); rationalization definition
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def rationalTwist (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    sfRationalConstructibleCategory l E Y ⥤ sfRationalConstructibleCategory l E Y :=
  ScalarLocalization.map (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E Y) (Padic.coefficientExtensionUniformizer l E)
    (integralTwist l E Y L hL m)

/-- Intrinsic integral objects satisfy the recorded augmented quotient-tower completeness.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the intrinsic predicate contains its canonical augmented reduction triangle.
The standard derived restriction and K-flat counits identify its legs with those of
the unrestricted reduction tower. This transports the same distinguished triangle;
the auxiliary finite-field presentation in the old predicate is immaterial. -/
theorem intrinsic_complete (K : sfIntegralConstructibleCategory l E Y) :
    IsDerivedCompleteUnrestricted l E Y K.obj := by
  sorry

/-- Restriction of evaluation, fixed on every integral object by the ambient evaluation.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: preservation by both signed tensors puts both endpoints in the full subcategory.
Full faithfulness restricts the evaluation and its inverse uniquely. Its naturality
and inverse identities are inherited from epsilon. -/
theorem integralEpsilon_existsUnique (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    ∃! e : integralTwist l E Y L hL m ⋙ integralTwist l E Y L hL (-m) ≅ 𝟭 _,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        (e.hom.app K).hom = (epsilon l E Y L m).hom.app K.obj := by
  sorry

/-- The restricted evaluation is uniquely fixed by the ambient sheaf evaluation.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def integralEpsilon (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    integralTwist l E Y L hL m ⋙ integralTwist l E Y L hL (-m) ≅ 𝟭 _ :=
  (integralEpsilon_existsUnique l E Y L hL m).exists.choose

/-- Rationalized evaluation, with components equal to the localization of the integral ones.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: apply localization to both integral evaluation components. Naturality on a pure
Hom tensor is integral naturality multiplied by its scalar; extend over sums. The
integral inverse equations remain inverse equations after localization. Every raw
rational object is an integral representative, proving uniqueness. -/
theorem rationalEpsilon_existsUnique (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    ∃! e : rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m) ≅ 𝟭 _,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        e.hom.app ((sfRationalConstructibleLocalization l E Y).obj K) =
          (sfRationalConstructibleLocalization l E Y).map
            ((integralEpsilon l E Y L hL m).hom.app K) := by
  sorry

/-- The actual scalar-localized evaluation.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def rationalEpsilon (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m) ≅ 𝟭 _ :=
  (rationalEpsilon_existsUnique l E Y L hL m).exists.choose


variable (p : ℕ) (hl : l ≠ p)

/-- Restricting the completed beta to the full constructible subcategories.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: both line twists preserve the subcategories by hypothesis and completed scalar
extension preserves them by its constructibility theorem. Full faithfulness restricts
beta and its inverse uniquely, with their inherited naturality equations. -/
theorem integralBeta_existsUnique (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N) (m : ℤ) :
    ∃! e : integralTwist l E Y L hL m ⋙
        sfConstructibleIntegralScalarExtension p l hl E F ι Y ≅
      sfConstructibleIntegralScalarExtension p l hl E F ι Y ⋙ integralTwist l F Y N hN m,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        HEq (e.hom.app K).hom (beta l E Y F ι L N b m K.obj
          (intrinsic_complete l E Y K)).hom := by
  sorry

/-- The unique restriction of beta, retaining its ambient components.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def integralBeta (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N) (m : ℤ) :
    integralTwist l E Y L hL m ⋙
      sfConstructibleIntegralScalarExtension p l hl E F ι Y ≅
    sfConstructibleIntegralScalarExtension p l hl E F ι Y ⋙ integralTwist l F Y N hN m :=
  (integralBeta_existsUnique l E F ι Y p hl L hL N hN b m).exists.choose

/-- The rational beta on the recorded scalar extensions, fixed by integral localization.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: localize each restricted component and its inverse. On every pure tensor in
Hom, naturality is the integral naturality equation tensored with the image scalar;
additivity extends it to all morphisms. Localization preserves inverse equations.
Objects of the raw rationalization are precisely integral representatives. HEq only
transports the object equalities in the recorded scalar functor's specification. -/
theorem rationalBeta_existsUnique (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N) (m : ℤ) :
    ∃! e : rationalTwist l E Y L hL m ⋙ sfRationalScalarExtension l E Y p hl F ι ≅
        sfRationalScalarExtension l E Y p hl F ι ⋙ rationalTwist l F Y N hN m,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        HEq (e.hom.app ((sfRationalConstructibleLocalization l E Y).obj K))
          ((sfRationalConstructibleLocalization l F Y).map
            ((integralBeta l E F ι Y p hl L hL N hN b m).hom.app K)) := by
  sorry

/-- The normalized rational scalar/line comparison.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def rationalBeta (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N) (m : ℤ) :
    rationalTwist l E Y L hL m ⋙ sfRationalScalarExtension l E Y p hl F ι ≅
      sfRationalScalarExtension l E Y p hl F ι ⋙ rationalTwist l F Y N hN m :=
  (rationalBeta_existsUnique l E F ι Y p hl L hL N hN b m).exists.choose

/-- The associator and unit restrict to the recorded canonical integral comparisons;
the recorded rational comparisons are their localizations.
Source: blueprint Proof (3); scalar-extension composition construction
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: both ordinary constructions are fixed by balanced scalar multiplication on
K-flat representatives, so their unique counit-compatible comparisons identify them.
Their normalized chi maps are fixed by the same quotient-cone maps with zero shifted
component. The conjugated associator and unitor therefore agree on all complete inputs.
Full faithfulness gives the integral equalities. The specification of the recorded
rational associator and unit says exactly that they localize those integral components. -/
theorem canonical_restriction :
    (∀ K : sfIntegralConstructibleCategory l E Y,
      HEq ((sfIntegralScalarComp l E F ι Y p hl G j).hom.app K).hom
        (associator l E Y F ι G j K.obj (intrinsic_complete l E Y K)).hom) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y,
      HEq ((sfIntegralScalarUnit l E Y p hl).hom.app K).hom
        (unit l E Y K.obj (intrinsic_complete l E Y K)).hom) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y,
      HEq ((sfRationalScalarComp l E F ι Y p hl G j).hom.app
        ((sfRationalConstructibleLocalization l E Y).obj K))
        ((sfRationalConstructibleLocalization l G Y).map
          ((sfIntegralScalarComp l E F ι Y p hl G j).hom.app K))) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y,
      HEq ((sfRationalScalarUnit l E Y p hl).hom.app
        ((sfRationalConstructibleLocalization l E Y).obj K))
        ((sfRationalConstructibleLocalization l E Y).map
          ((sfIntegralScalarUnit l E Y p hl).hom.app K))) := by
  sorry

/-- Evaluation compatibility after rationalization, with exactly the integral components.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: restrict the ambient evaluation square by full faithfulness. Rationalization
sends both integral composites to the corresponding composites. The normalized
component equations for rationalBeta and rationalEpsilon identify these images
with the displayed square, including all morphisms tensored with arbitrary scalars. -/
theorem rational_evaluation (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N)
    (m : ℤ) (K : sfRationalConstructibleCategory l E Y) :
    (rationalBeta l E F ι Y p hl L hL N hN b (-m)).hom.app
        ((rationalTwist l E Y L hL m).obj K) ≫
      (rationalTwist l F Y N hN (-m)).map
        ((rationalBeta l E F ι Y p hl L hL N hN b m).hom.app K) ≫
      (rationalEpsilon l F Y N hN m).hom.app
        ((sfRationalScalarExtension l E Y p hl F ι).obj K) =
    (sfRationalScalarExtension l E Y p hl F ι).map
      ((rationalEpsilon l E Y L hL m).hom.app K) := by
  sorry


/-- The rationalized tower square uses the recorded canonical scalar associator.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: restriction preserves the completed tower equation, since the integral
subcategories are full. Localize the equation, using the normalized component
specifications for rationalBeta. canonical_restriction identifies the scalar
associator with sfRationalScalarComp, so the localized equality is precisely this
square. The same argument applies when any coefficient transition is the identity. -/
theorem rational_tower (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (P : integralTowerModules l G Y) [P.IsFiniteLocallyFreeOfRank 1]
    (hP : PreservesConstructible l G Y P)
    (b10 : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N)
    (b21 : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l F G j Y) N ≅ P)
    (b20 : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E G (j.comp ι) Y) L ≅ P)
    (hb : ∀ (U : Y.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F Y).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G Y).obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (completedCoefficientMap l F G j Y) N U t
          (b10.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (completedCoefficientMap l E F ι Y) L U s x))) =
        b20.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (completedCoefficientMap l E G (j.comp ι) Y) L U
          (t * (completedCoefficientMap l F G j Y).hom.app U s) x))
    (m : ℤ) (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l F Y p hl G j).map
        ((rationalBeta l E F ι Y p hl L hL N hN b10 m).hom.app K) ≫
      (rationalBeta l F G j Y p hl N hN P hP b21 m).hom.app
        ((sfRationalScalarExtension l E Y p hl F ι).obj K) ≫
      (rationalTwist l G Y P hP m).map
        ((sfRationalScalarComp l E F ι Y p hl G j).hom.app K) =
    (sfRationalScalarComp l E F ι Y p hl G j).hom.app
        ((rationalTwist l E Y L hL m).obj K) ≫
      (rationalBeta l E G (j.comp ι) Y p hl L hL P hP b20 m).hom.app K := by
  sorry

/-- After scalar-unit normalization the repeated-field comparison is still exactly
the prescribed signed-power line map. Identifying along that map makes it identity.
Source: blueprint Proof (3), final sentence, with the actual line identifications retained
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the ambient repeated-field equality identifies the scalar-normalized beta
with the ordinary b-induced map. Restrict that equality to integral objects. The
rational scalar unit is the localization of the integral unit by canonical_restriction;
rationalBeta has the localized integral components. Hence the normalized rational
component equals the localization of the same ordinary signed-line map, as displayed.
The scalar pentagon and both unit laws ensure the normalized associators with an
identity adjacent transition are identities. Tower and evaluation remain the images
of their earlier equations under these line identifications. -/
theorem rational_repeated (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l E Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l E Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) Y) L ≅ N)
    (m : ℤ) (K : sfIntegralConstructibleCategory l E Y) :
    HEq
      ((sfRationalScalarUnit l E Y p hl).inv.app
          ((rationalTwist l E Y L hL m).obj
            ((sfRationalConstructibleLocalization l E Y).obj K)) ≫
        (rationalBeta l E E (AlgHom.id ℚ_[l] E) Y p hl L hL N hN b m).hom.app
          ((sfRationalConstructibleLocalization l E Y).obj K) ≫
        (rationalTwist l E Y N hN m).map
          ((sfRationalScalarUnit l E Y p hl).hom.app
            ((sfRationalConstructibleLocalization l E Y).obj K)))
      ((sfRationalConstructibleLocalization l E Y).map
        (ObjectProperty.homMk
          ((ordinaryUnit l E Y).inv.app ((tensor l E Y L m).obj K.obj) ≫
            ((pairData l E Y E (AlgHom.id ℚ_[l] E) L N b).ordinary m).hom.app K.obj ≫
            (tensor l E Y N m).map ((ordinaryUnit l E Y).hom.app K.obj)) :
          (integralTwist l E Y L hL m).obj K ⟶ (integralTwist l E Y N hN m).obj K)) := by
  sorry

/-- Diagonal line data are multiplication, so unit-normalized rational beta is identity.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the signed-power extensions of multiplication are the normalized multiplication
maps, including zero and negative powers. The ordinary pure-tensor unit square is
therefore identity. Apply rational_repeated, which identifies the normalized completed
component with its localized ordinary component. No equality C_ii=1 is used. -/
theorem rational_diagonal (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) Y) L ≅ L)
    (hb : ∀ (U : Y.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) (x : L.val.obj U),
      b.hom.val.app U (SheafOfModules.scalarExtensionSection
        (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) Y) L U s x) =
        smul l E Y L U s x)
    (m : ℤ) (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarUnit l E Y p hl).inv.app ((rationalTwist l E Y L hL m).obj K) ≫
        (rationalBeta l E E (AlgHom.id ℚ_[l] E) Y p hl L hL L hL b m).hom.app K ≫
        (rationalTwist l E Y L hL m).map ((sfRationalScalarUnit l E Y p hl).hom.app K) =
      𝟙 ((rationalTwist l E Y L hL m).obj K) := by
  sorry

end Rational
end CompletedLineTensor
end WeilConjectures
