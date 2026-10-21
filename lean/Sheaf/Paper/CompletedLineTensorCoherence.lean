/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
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
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.SfDerivedCompleteLegacyComparison

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
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
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

/-- Signed powers are lines, so their ordinary tensor functors are exact and additive.
Source: Stacks 03EK, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: trivialize L on a covering. Every tensor power and its internal dual is the
unit there, including exponent zero. Tensor is thus locally the identity. Exactness
is local, and additivity follows on the sectionwise pure tensors and sheafification. -/
theorem exact (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (sheaf l E X L m).Additive ∧ PreservesFiniteLimits (sheaf l E X L m) ∧
      PreservesFiniteColimits (sheaf l E X L m) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let T := sheaf l E X L m
    let S := sheaf l E X L (-m)
    let e : T ⋙ S ≅ 𝟭 _ := evaluation l E X L m
    let f : S ⋙ T ≅ 𝟭 _ := by
      simpa only [neg_neg] using evaluation l E X L (-m)
    let equiv : integralTowerModules l E X ≌ integralTowerModules l E X :=
      CategoryTheory.Equivalence.mk T S e.symm f
    let : T.IsEquivalence := equiv.isEquivalence_functor
    refine ⟨?_, inferInstance, inferInstance⟩
    exact (CategoryTheory.rightExactFunctor_le_additiveFunctor _ _) _
      (inferInstanceAs (PreservesFiniteColimits T))

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

attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

private theorem complete_of_iso
    {K M : DerivedCategory (integralTowerModules l E X)} (e : K ≅ M)
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E X M := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨D, hlD, P, G, q, hq, a, hprod, δ, hδ⟩ := hK
    let := hprod
    refine ⟨D, hlD, P, G, q, hq, a ≪≫ e, hprod,
      δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
    apply Pretriangulated.isomorphic_distinguished _ hδ _
    refine Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · apply Pi.hom_ext
      intro n
      simp [Category.assoc]
    · simp
    · simp [Category.assoc, ← Functor.map_comp]

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
  exact complete_of_iso l F X (chi l E X F ι K hK)
    ((finiteFreeCompletedScalarComparison l E F ι X).2.1 K hK).2

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

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

attribute [local semireducible] unit ordinaryUnit chi

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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    constructor
    · intro P hP
      have hχ := (finiteFreeCompletedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).2.2 P
      have hμ := (ordinaryUnit_existsUnique l E X).exists.choose_spec P
      change (ordinaryUnit l E X).hom.app _ = _ at hμ
      change ((ordinaryUnit l E X).inv.app _ ≫
        (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).app _) ≫ _ = _
      rw [Category.assoc]
      have hχ' :
          (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).app
              (DerivedCategory.Q.obj P.obj) ≫
              (integralScalarExtensionComparisonOfUniverses l E E
                (AlgHom.id ℚ_[l] E) X).hom.app P =
            (ordinaryUnit l E X).hom.app (DerivedCategory.Q.obj P.obj) ≫
              DerivedCategory.Q.map ((completedScalarIdentityUnit l E X).app P.obj) := by
        rw [hμ, Category.assoc]
        exact hχ
      erw [hχ']
      simp
    · intro K M hK hM f
      apply (cancel_epi (chi l E X E (AlgHom.id ℚ_[l] E) K hK).hom).1
      change (chi l E X E (AlgHom.id ℚ_[l] E) K hK).hom ≫
          ((integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) X).map f ≫
            (chi l E X E (AlgHom.id ℚ_[l] E) M hM).inv ≫
              (ordinaryUnit l E X).hom.app M) =
        (chi l E X E (AlgHom.id ℚ_[l] E) K hK).hom ≫
          ((chi l E X E (AlgHom.id ℚ_[l] E) K hK).inv ≫
            (ordinaryUnit l E X).hom.app K) ≫ f
      have hχ := (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).naturality f
      change (completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X).map f ≫
          (chi l E X E (AlgHom.id ℚ_[l] E) M hM).hom =
        (chi l E X E (AlgHom.id ℚ_[l] E) K hK).hom ≫
          (integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) X).map f at hχ
      rw [← Category.assoc, ← hχ]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact (ordinaryUnit l E X).hom.naturality f

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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    unfold unit beta
    try dsimp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
    simp only [Iso.app_hom, Iso.app_inv]
    rw [(tensor l E X N m).map_id]
    simp only [Category.id_comp]

private theorem line_map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem line_localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
      eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
        (eqToIso (hG K)).symm
    have hc (K) : HEq (c K).hom
        ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
      simp [c]
    have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
        F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
      obtain ⟨K⟩ := K
      obtain ⟨K'⟩ := K'
      induction f using TensorProduct.induction_on with
      | zero => simp
      | add f g hf hg =>
        rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
      | tmul a f =>
        rw [(conj_eqToHom_iff_heq _ _ (hF ⟨K⟩) (hF ⟨K'⟩)).mpr (mF K K' f a),
          (conj_eqToHom_iff_heq _ _ (hG ⟨K⟩) (hG ⟨K'⟩)).mpr (mG K K' f a)]
        dsimp [c]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        have he : ScalarLocalization.composition S D v _ _ _
              ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
            ScalarLocalization.composition S D v _ _ _
              (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
          simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
          rw [e.hom.naturality f]
        have he' :
            @CategoryStruct.comp (ScalarLocalization S D v) _
              ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
              (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
            @CategoryStruct.comp (ScalarLocalization S D v) _
              ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
              ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
        simpa only [ScalarLocalization.localization, Category.assoc] using
          congrArg (fun z :
            (⟨F₀.obj K⟩ : ScalarLocalization S D v) ⟶ ⟨G₀.obj K'⟩ ↦
              eqToHom (hF ⟨K⟩) ≫ z ≫ eqToHom (hG ⟨K'⟩).symm) he'
    let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
    refine ⟨a, hc, ?_⟩
    intro a' ha'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact eq_of_heq ((ha' K).trans (hc K).symm)


private theorem line_app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X X' : C} (h : X = X') :
    HEq (α.app X) (α.app X') := by
  cases h
  rfl

private theorem line_iso_inv_heq {C : Type*} [Category C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {e : X ≅ Y} {e' : X' ≅ Y'} (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hX
  cases hY
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

private theorem line_comp_heq {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hX
  cases hY
  cases hZ
  cases hf
  cases hg
  rfl

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

private instance rationalTwist_additive (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (rationalTwist l E Y L hL m).Additive :=
  inferInstanceAs (ScalarLocalization.map _ _ _ (integralTwist l E Y L hL m)).Additive

/-- Intrinsic integral objects satisfy the recorded augmented quotient-tower completeness.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the intrinsic predicate contains its canonical augmented reduction triangle.
The standard derived restriction and K-flat counits identify its legs with those of
the unrestricted reduction tower. This transports the same distinguished triangle;
the auxiliary finite-field presentation in the old predicate is immaterial. -/
theorem intrinsic_complete (K : sfIntegralConstructibleCategory l E Y) :
    IsDerivedCompleteUnrestricted l E Y K.obj := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact q.Prime := ⟨hprime⟩
    let D : FiniteFieldDatum.{0} :=
      { p := q
        a := 1
        q := q
        prime := hprime
        exponent_pos := le_refl 1
        cardinality_eq := (pow_one q).symm
        k₀ := ZMod q
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod q) }
    have hlD : l ≠ D.p := by
      change l ≠ q
      omega
    exact ⟨D, hlD, (sfDerivedComplete_iff_legacy l E Y D hlD K.obj).mp K.property.1⟩

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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let e : integralTwist l E Y L hL m ⋙ integralTwist l E Y L hL (-m) ≅ 𝟭 _ :=
      NatIso.ofComponents
        (fun K ↦ (sfIntegralConstructible l E Y).isoMk ((epsilon l E Y L m).app K.obj))
        (by
          intro K M f
          apply (sfIntegralConstructible l E Y).ι.map_injective
          exact (epsilon l E Y L m).hom.naturality f.hom)
    refine ⟨e, fun _ ↦ rfl, ?_⟩
    intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (sfIntegralConstructible l E Y).ι.map_injective
    exact he' K

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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let R := Padic.coefficientExtensionIntegers l E
    let C := sfIntegralConstructibleCategory l E Y
    let π := Padic.coefficientExtensionUniformizer l E
    let T := integralTwist l E Y L hL m
    let S := integralTwist l E Y L hL (-m)
    have h := line_localizedIso π π id (T ⋙ S) (𝟭 _)
      (integralEpsilon l E Y L hL m)
      (rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m)) (𝟭 _)
      (fun _ ↦ rfl) (fun _ ↦ rfl)
      (by
        intro K M f a
        apply heq_of_eq
        change ScalarLocalization.mapHom R C π S _ _
          (ScalarLocalization.mapHom R C π T _ _ (a ⊗ₜ[R] f)) =
          a ⊗ₜ[R] S.map (T.map f)
        simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul]
        rfl)
      (by intros; rfl)
    obtain ⟨e, he, hu⟩ := h
    refine ⟨e, fun K ↦ eq_of_heq (he ⟨K⟩), ?_⟩
    intro e' he'
    exact hu e' (fun K ↦ heq_of_eq (he' K.obj))

/-- The actual scalar-localized evaluation.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def rationalEpsilon (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m) ≅ 𝟭 _ :=
  (rationalEpsilon_existsUnique l E Y L hL m).exists.choose


variable (p : ℕ) (hl : l ≠ p)

private theorem rational_scalar_map_localization
    (K M : sfIntegralConstructibleCategory l E Y) (f : K ⟶ M) :
    HEq ((sfRationalScalarExtension l E Y p hl F ι).map
      ((sfRationalConstructibleLocalization l E Y).map f))
      ((sfRationalConstructibleLocalization l F Y).map
        ((sfConstructibleIntegralScalarExtension p l hl E F ι Y).map f)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simpa only [sfRationalScalarExtension, sfRationalConstructibleLocalization,
      ScalarLocalization.localization, map_one] using
      (sfRationalScalarExtension_existsUnique l E Y p hl F ι).exists.choose_spec.2.2 K M f 1

attribute [local semireducible] integralScalarExtensionOfUniverses

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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let e : integralTwist l E Y L hL m ⋙
        sfConstructibleIntegralScalarExtension p l hl E F ι Y ≅
        sfConstructibleIntegralScalarExtension p l hl E F ι Y ⋙ integralTwist l F Y N hN m :=
      NatIso.ofComponents
        (fun K ↦ (sfIntegralConstructible l F Y).isoMk
          (beta l E Y F ι L N b m K.obj (intrinsic_complete l E Y K)))
        (by
          intro K M f
          apply (sfIntegralConstructible l F Y).ι.map_injective
          exact (beta_natural_evaluation l E Y F ι L N b).1 m K.obj M.obj
            (intrinsic_complete l E Y K) (intrinsic_complete l E Y M) f.hom)
    refine ⟨e, fun _ ↦ HEq.rfl, ?_⟩
    intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (sfIntegralConstructible l F Y).ι.map_injective
    exact eq_of_heq (he' K)

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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let T := integralTwist l E Y L hL m
    let S := integralTwist l F Y N hN m
    let C := sfConstructibleIntegralScalarExtension p l hl E F ι Y
    let D := sfRationalScalarExtension l E Y p hl F ι
    let T' := rationalTwist l E Y L hL m
    let S' := rationalTwist l F Y N hN m
    have hD := (sfRationalScalarExtension_existsUnique l E Y p hl F ι).exists.choose_spec
    let ψ a := (sfRationalCoefficientEquiv l F).symm (ι (sfRationalCoefficientEquiv l E a))
    have hloc : ∃! e : T' ⋙ D ≅ D ⋙ S',
        ∀ K : sfRationalConstructibleCategory l E Y,
          HEq (e.hom.app K) ((sfRationalConstructibleLocalization l F Y).map
            ((integralBeta l E F ι Y p hl L hL N hN b m).hom.app K.obj)) := by
      apply line_localizedIso
        (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l F)
        ψ (T ⋙ C) (C ⋙ S) (integralBeta l E F ι Y p hl L hL N hN b m)
        (T' ⋙ D) (D ⋙ S')
      · intro K
        exact hD.2.1 (T'.obj K)
      · intro K
        exact congrArg S'.obj (hD.2.1 K)
      · intro K K' f a
        have ht : T'.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) K ⟶ ⟨K'⟩) =
            a ⊗ₜ[Padic.coefficientExtensionIntegers l E] T.map f :=
          LinearMap.baseChange_tmul _ _ _
        dsimp only [Functor.comp_map]
        rw [ht]
        exact hD.2.2 (T.obj K) (T.obj K') (T.map f) a
      · intro K K' f a
        have hm := line_map_heq S' (hD.2.1 ⟨K⟩) (hD.2.1 ⟨K'⟩) (hD.2.2 K K' f a)
        exact hm.trans (heq_of_eq (LinearMap.baseChange_tmul _ _ _))
    obtain ⟨e, he, hu⟩ := hloc
    refine ⟨e, fun K ↦ he ⟨K⟩, ?_⟩
    intro e' he'
    exact hu e' (fun K ↦ he' K.obj)

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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let C := sfConstructibleIntegralScalarExtension p l hl E F ι Y
    let D := sfRationalScalarExtension l E Y p hl F ι
    let Q := sfRationalConstructibleLocalization l F Y
    let T := integralTwist l E Y L hL m
    let S := integralTwist l F Y N hN m
    let Sm := integralTwist l F Y N hN (-m)
    let Smq := rationalTwist l F Y N hN (-m)
    let bp := integralBeta l E F ι Y p hl L hL N hN b m
    let bm := integralBeta l E F ι Y p hl L hL N hN b (-m)
    let eE := integralEpsilon l E Y L hL m
    let eF := integralEpsilon l F Y N hN m
    have hi : bm.hom.app (T.obj K.obj) ≫ Sm.map (bp.hom.app K.obj) ≫
          eF.hom.app (C.obj K.obj) = C.map (eE.hom.app K.obj) := by
      apply (sfIntegralConstructible l F Y).ι.map_injective
      have hbp := eq_of_heq
        ((integralBeta_existsUnique l E F ι Y p hl L hL N hN b m).exists.choose_spec K.obj)
      have hbm := eq_of_heq
        ((integralBeta_existsUnique l E F ι Y p hl L hL N hN b (-m)).exists.choose_spec
          (T.obj K.obj))
      simp only [ObjectProperty.ι_map]
      change (bp.hom.app K.obj).hom = _ at hbp
      change (bm.hom.app (T.obj K.obj)).hom = _ at hbm
      have heE := (integralEpsilon_existsUnique l E Y L hL m).exists.choose_spec K.obj
      have heF := (integralEpsilon_existsUnique l F Y N hN m).exists.choose_spec (C.obj K.obj)
      change (bm.hom.app (T.obj K.obj)).hom ≫
          (tensor l F Y N (-m)).map (bp.hom.app K.obj).hom ≫
          (eF.hom.app (C.obj K.obj)).hom =
        (integralScalarExtensionOfUniverses l E F ι Y).map (eE.hom.app K.obj).hom
      change (eE.hom.app K.obj).hom = _ at heE
      change (eF.hom.app (C.obj K.obj)).hom = _ at heF
      erw [hbm, hbp, heE, heF]
      exact (beta_natural_evaluation l E Y F ι L N b).2 m K.obj.obj
        (intrinsic_complete l E Y K.obj)
    have hD := (sfRationalScalarExtension_existsUnique l E Y p hl F ι).exists.choose_spec
    have hobj := hD.2.1 K
    have hbp := (rationalBeta_existsUnique l E F ι Y p hl L hL N hN b m).exists.choose_spec
      K.obj
    have hbm := (rationalBeta_existsUnique l E F ι Y p hl L hL N hN b (-m)).exists.choose_spec
      (T.obj K.obj)
    have hm := line_map_heq Smq (hD.2.1 ((rationalTwist l E Y L hL m).obj K))
      (congrArg (rationalTwist l F Y N hN m).obj hobj) hbp
    have hm' : HEq
        (Smq.map ((rationalBeta l E F ι Y p hl L hL N hN b m).hom.app K))
        (Q.map (Sm.map (bp.hom.app K.obj))) :=
      hm.trans (heq_of_eq (LinearMap.baseChange_tmul _ _ _))
    have heF := (line_app_heq (rationalEpsilon l F Y N hN m).hom hobj).trans
      (heq_of_eq ((rationalEpsilon_existsUnique l F Y N hN m).exists.choose_spec
        (C.obj K.obj)))
    have hleft := line_comp_heq (hD.2.1
        ((rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m)).obj K))
      (congrArg Smq.obj (hD.2.1 ((rationalTwist l E Y L hL m).obj K))) hobj hbm
      (line_comp_heq (congrArg Smq.obj (hD.2.1
          ((rationalTwist l E Y L hL m).obj K)))
        (congrArg Smq.obj (congrArg (rationalTwist l F Y N hN m).obj hobj)) hobj hm' heF)
    have heE := (rationalEpsilon_existsUnique l E Y L hL m).exists.choose_spec K.obj
    have hright := line_map_heq D rfl rfl (heq_of_eq heE)
    have hmap : HEq (D.map
        ((sfRationalConstructibleLocalization l E Y).map (eE.hom.app K.obj)))
        (Q.map (C.map (eE.hom.app K.obj))) := by
      simpa only [D, C, Q, sfRationalScalarExtension, sfRationalConstructibleLocalization,
        ScalarLocalization.localization, map_one] using hD.2.2 _ _ (eE.hom.app K.obj) 1
    exact eq_of_heq (hleft.trans ((heq_of_eq (by
      simpa only [Functor.map_comp, Functor.mapIso_inv, Iso.app_inv,
        Functor.mapLinearMap] using congrArg Q.map hi)).trans
        (hright.trans hmap).symm))


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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let C₁ := sfConstructibleIntegralScalarExtension p l hl E F ι Y
    let C₂ := sfConstructibleIntegralScalarExtension p l hl F G j Y
    let C₃ := sfConstructibleIntegralScalarExtension p l hl E G (j.comp ι) Y
    let D₁ := sfRationalScalarExtension l E Y p hl F ι
    let D₂ := sfRationalScalarExtension l F Y p hl G j
    let D₃ := sfRationalScalarExtension l E Y p hl G (j.comp ι)
    let Q := sfRationalConstructibleLocalization l G Y
    let T := integralTwist l E Y L hL m
    let S := integralTwist l F Y N hN m
    let V := integralTwist l G Y P hP m
    let Tq := rationalTwist l E Y L hL m
    let Sq := rationalTwist l F Y N hN m
    let Vq := rationalTwist l G Y P hP m
    let B₁ := integralBeta l E F ι Y p hl L hL N hN b10 m
    let B₂ := integralBeta l F G j Y p hl N hN P hP b21 m
    let B₃ := integralBeta l E G (j.comp ι) Y p hl L hL P hP b20 m
    let A := sfIntegralScalarComp l E F ι Y p hl G j
    have hi : C₂.map (B₁.hom.app K.obj) ≫ B₂.hom.app (C₁.obj K.obj) ≫
        V.map (A.hom.app K.obj) = A.hom.app (T.obj K.obj) ≫ B₃.hom.app K.obj := by
      apply (sfIntegralConstructible l G Y).ι.map_injective
      have hb₁ := eq_of_heq ((integralBeta_existsUnique l E F ι Y p hl
        L hL N hN b10 m).exists.choose_spec K.obj)
      have hb₂ := eq_of_heq ((integralBeta_existsUnique l F G j Y p hl
        N hN P hP b21 m).exists.choose_spec (C₁.obj K.obj))
      have hb₃ := eq_of_heq ((integralBeta_existsUnique l E G (j.comp ι) Y p hl
        L hL P hP b20 m).exists.choose_spec K.obj)
      have ha := (canonical_restriction l E F ι G j Y p hl).1
      have ha₁ := eq_of_heq (ha K.obj)
      have ha₂ := eq_of_heq (ha (T.obj K.obj))
      change (integralScalarExtension l F G j Y).map _ ≫ _ ≫
        (tensor l G Y P m).map _ = _ ≫ _
      simp only [ObjectProperty.ι_map]
      change (B₁.hom.app K.obj).hom = _ at hb₁
      change (B₂.hom.app (C₁.obj K.obj)).hom = _ at hb₂
      change (B₃.hom.app K.obj).hom = _ at hb₃
      change (A.hom.app K.obj).hom = _ at ha₁
      change (A.hom.app (T.obj K.obj)).hom = _ at ha₂
      erw [hb₁, hb₂, hb₃, ha₁, ha₂]
      exact tower l E Y F ι G j L N P b10 b21 b20 hb m K.obj.obj
        (intrinsic_complete l E Y K.obj)
    have h₁ := (sfRationalScalarExtension_existsUnique l E Y p hl F ι).exists.choose_spec.2.1
    have h₂ := (sfRationalScalarExtension_existsUnique l F Y p hl G j).exists.choose_spec.2.1
    have h₃ := (sfRationalScalarExtension_existsUnique l E Y p hl G
      (j.comp ι)).exists.choose_spec.2.1
    let O (J : sfRationalConstructibleCategory l F Y) := Q.obj (C₂.obj J.obj)
    have hcomp (J : sfRationalConstructibleCategory l E Y) :
        D₂.obj (D₁.obj J) = Q.obj (C₂.obj (C₁.obj J.obj)) :=
      (h₂ (D₁.obj J)).trans (congrArg O (h₁ J))
    have hb₁ := (rationalBeta_existsUnique l E F ι Y p hl L hL N hN b10 m).exists.choose_spec K.obj
    have hb₂ := (line_app_heq
        (rationalBeta l F G j Y p hl N hN P hP b21 m).hom (h₁ K)).trans
      ((rationalBeta_existsUnique l F G j Y p hl N hN P hP b21 m).exists.choose_spec (C₁.obj K.obj))
    have hb₃ := (rationalBeta_existsUnique l E G (j.comp ι) Y p hl
      L hL P hP b20 m).exists.choose_spec K.obj
    have hfirst := (line_map_heq D₂ (h₁ (Tq.obj K))
      (congrArg Sq.obj (h₁ K)) hb₁).trans
      (rational_scalar_map_localization l F G j Y p hl _ _ (B₁.hom.app K.obj))
    have ha := (sfRationalScalarComp_existsUnique l E F ι Y p hl G j).exists.choose_spec K
    have hlast : HEq
        (Vq.map ((sfRationalScalarComp l E F ι Y p hl G j).hom.app K))
        (Q.map (V.map (A.hom.app K.obj))) :=
      (line_map_heq Vq (hcomp K) (h₃ K) ha).trans
        (heq_of_eq (LinearMap.baseChange_tmul _ _ _))
    have hmiddle : D₂.obj (Sq.obj (D₁.obj K)) = Q.obj (C₂.obj (S.obj (C₁.obj K.obj))) :=
      (h₂ (Sq.obj (D₁.obj K))).trans (congrArg O (congrArg Sq.obj (h₁ K)))
    have hleft := line_comp_heq (hcomp (Tq.obj K)) hmiddle
      (congrArg Vq.obj (h₃ K)) hfirst
      (line_comp_heq hmiddle (congrArg Vq.obj (hcomp K))
        (congrArg Vq.obj (h₃ K)) hb₂ hlast)
    have hright := line_comp_heq (hcomp (Tq.obj K)) (h₃ (Tq.obj K))
      (congrArg Vq.obj (h₃ K))
      ((sfRationalScalarComp_existsUnique l E F ι Y p hl G j).exists.choose_spec
        (Tq.obj K)) hb₃
    have hqi : Q.map (C₂.map (B₁.hom.app K.obj)) ≫
        Q.map (B₂.hom.app (C₁.obj K.obj)) ≫ Q.map (V.map (A.hom.app K.obj)) =
        Q.map (A.hom.app (T.obj K.obj)) ≫ Q.map (B₃.hom.app K.obj) := by
      rw [← Q.map_comp, ← Q.map_comp, hi, Q.map_comp]
    exact eq_of_heq (hleft.trans ((heq_of_eq hqi).trans hright.symm))

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
          (integralTwist l E Y L hL m).obj K ⟶ (integralTwist l E Y N hN m).obj K))  := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let C := sfConstructibleIntegralScalarExtension p l hl E E (AlgHom.id ℚ_[l] E) Y
    let D := sfRationalScalarExtension l E Y p hl E (AlgHom.id ℚ_[l] E)
    let Q := sfRationalConstructibleLocalization l E Y
    let T := integralTwist l E Y L hL m
    let S := integralTwist l E Y N hN m
    let Sq := rationalTwist l E Y N hN m
    let V := sfIntegralScalarUnit l E Y p hl
    let U := sfRationalScalarUnit l E Y p hl
    let B := integralBeta l E E (AlgHom.id ℚ_[l] E) Y p hl L hL N hN b m
    have hV (J : sfIntegralConstructibleCategory l E Y) :
        (sfIntegralConstructible l E Y).ι.mapIso (V.app J) =
          unit l E Y J.obj (intrinsic_complete l E Y J) := by
      apply Iso.ext
      exact eq_of_heq ((canonical_restriction l E E (AlgHom.id ℚ_[l] E)
        E (AlgHom.id ℚ_[l] E) Y p hl).2.1 J)
    have hi : V.inv.app (T.obj K) ≫ B.hom.app K ≫ S.map (V.hom.app K) =
        (ObjectProperty.homMk
          ((ordinaryUnit l E Y).inv.app ((tensor l E Y L m).obj K.obj) ≫
            ((pairData l E Y E (AlgHom.id ℚ_[l] E) L N b).ordinary m).hom.app K.obj ≫
            (tensor l E Y N m).map ((ordinaryUnit l E Y).hom.app K.obj)) :
          T.obj K ⟶ S.obj K) := by
      apply (sfIntegralConstructible l E Y).ι.map_injective
      have hb := eq_of_heq ((integralBeta_existsUnique l E E (AlgHom.id ℚ_[l] E)
        Y p hl L hL N hN b m).exists.choose_spec K)
      have hu := congrArg Iso.hom (hV K)
      have hui := congrArg Iso.inv (hV (T.obj K))
      change _ ≫ _ ≫ (tensor l E Y N m).map _ = _
      simp only [ObjectProperty.ι_map]
      change (B.hom.app K).hom = _ at hb
      simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
        Iso.app_inv, ObjectProperty.ι_map] at hu hui
      erw [hui, hb, hu]
      exact repeated l E Y L N b m K.obj (intrinsic_complete l E Y K)
    have hobj := (sfRationalScalarExtension_existsUnique l E Y p hl E
      (AlgHom.id ℚ_[l] E)).exists.choose_spec.2.1
    have hU := (sfRationalScalarUnit_existsUnique l E Y p hl).exists.choose_spec
    have hui := line_iso_inv_heq (hobj (Q.obj (T.obj K))) rfl
      (e := U.app (Q.obj (T.obj K))) (e' := Q.mapIso (V.app (T.obj K)))
      (hU (Q.obj (T.obj K)))
    have hb := (rationalBeta_existsUnique l E E (AlgHom.id ℚ_[l] E)
      Y p hl L hL N hN b m).exists.choose_spec K
    have hu := line_map_heq Sq (hobj (Q.obj K)) rfl (hU (Q.obj K))
    have hu' : HEq (Sq.map (U.hom.app (Q.obj K)))
        (Q.map (S.map (V.hom.app K))) :=
      hu.trans (heq_of_eq (LinearMap.baseChange_tmul _ _ _))
    have hleft := line_comp_heq rfl (hobj (Q.obj (T.obj K))) rfl hui
      (line_comp_heq (hobj (Q.obj (T.obj K)))
        (congrArg Sq.obj (hobj (Q.obj K))) rfl hb hu')
    exact hleft.trans (heq_of_eq (by
      simpa only [Functor.map_comp, Functor.mapIso_inv, Iso.app_inv,
        Functor.mapLinearMap] using congrArg Q.map hi))

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
