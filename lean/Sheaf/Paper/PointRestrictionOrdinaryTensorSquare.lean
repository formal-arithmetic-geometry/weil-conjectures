/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.PointFiniteFreeSectionsTensor
public import Sheaf.Paper.PointDerivedSectionsTensorDescent
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Sheaf.Paper.IsomorphismScalarTensorKFlatModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.Paper.PointProEtaleSectionsExact

/-! # Ordinary sections-tensor square for a point automorphism

Source: blueprint, sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/
def-weil-global-geometric-frobenius.md, returned proof steps 1--2;
Stacks Tags 03EK and 06YS (the explicit restriction calculation is agent-written)
(blueprint: lem-weil-point-restriction-ordinary-tensor-square).

The sectionwise coordinates of inverse image identify the distinguished coprojection
with the identity. Sections use the unlifted integral scalar action of the recorded
finite-free comparison; the restriction maps below have exactly the recorded raw values.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u wE wL
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
open WeilConjectures.PointDerivedSectionsTensor
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] completedScalarChangeData completedOrdinaryScalarExtension
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  completedIntegralCoefficientSheafUnrestricted inverseImageCompletedCoefficientMap
  integralOperationsGoodComplex

variable {k : Type t} [Field k] {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L}
  (d : PointFiniteFreeSectionsTensorData k l E L ι)
  (g : Spec (.of k) ⟶ Spec (.of k)) [IsIso g]

/-- The left chain composite: sigma tensor one, then theta, then sections of b.
Source: returned Frobenius proof steps 1--2; Stacks 03EK
(blueprint: lem-weil-point-restriction-ordinary-tensor-square). -/
abbrev pointRestrictionTensorLeft
    [(sectionsE d).Additive] [(sectionsL d).Additive]
    (σE : sectionsE d ⟶ inverseImageIntegralModules l E g ⋙ sectionsE d)
    (b : (integralOperationsGoodComplex l E (Spec (.of k))).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E (Spec (.of k))).ι ⋙ rightComplex l E L ι g)
    (P : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory) :=
  (NatTrans.mapHomologicalComplex
      (Functor.whiskerRight σE (pointFiniteFreeModuleTensor.{t, u} l E L ι)) (.up ℤ)).app
      P.obj ≫
    d.complexes.hom.app ((inverseComplex l E g).obj P.obj) ≫
    ((sectionsL d).mapHomologicalComplex (.up ℤ)).map (b.hom.app P)

/-- The right chain composite: theta, then sigma on the extended complex.
Source: returned Frobenius proof steps 1--2; Stacks 03EK
(blueprint: lem-weil-point-restriction-ordinary-tensor-square). -/
abbrev pointRestrictionTensorRight
    [(sectionsE d).Additive] [(sectionsL d).Additive]
    (σL : sectionsL d ⟶ inverseImageIntegralModules l L g ⋙ sectionsL d)
    (P : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) :=
  d.complexes.hom.app P ≫
    (NatTrans.mapHomologicalComplex
      (Functor.whiskerLeft (completedOrdinaryScalarExtension l E L ι (Spec (.of k))) σL)
        (.up ℤ)).app P

variable [HasDerivedCategory.{wE}
    (ModuleCat.{max u (t + 1)} (Padic.coefficientExtensionIntegers l E))]
  [HasDerivedCategory.{wL}
    (ModuleCat.{max u (t + 1)} (Padic.coefficientExtensionIntegers l L))]

/-- The square together with its normalized chain representatives. The parameter dd is the
existing derived-descent assertion, so its theta is the specified ordinary map.
The raw equations specify sigma in unlifted scalar coordinates; they do not introduce
arbitrary transport maps. The derived equations specify localization of those maps.
Source: returned Frobenius proof steps 1--2; Stacks 03EK, 06YS and 04VG
(blueprint: lem-weil-point-restriction-ordinary-tensor-square). -/
def pointRestrictionOrdinaryTensorSquare
    (dd : PointDerivedSectionsTensorData d)
    (b : (integralOperationsGoodComplex l E (Spec (.of k))).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E (Spec (.of k))).ι ⋙ rightComplex l E L ι g)
    (β : inverseImageIntegralDerived l E g ⋙
        completedDerivedScalarExtension l E L ι (Spec (.of k)) ≅
      completedDerivedScalarExtension l E L ι (Spec (.of k)) ⋙
        inverseImageIntegralDerived l L g) : Prop :=
  letI := dd.sectionsE_additive
  letI := dd.sectionsL_additive
  letI := dd.sectionsE_limits
  letI := dd.sectionsE_colimits
  letI := dd.sectionsL_limits
  letI := dd.sectionsL_colimits
  letI := dd.sheaf_limits
  letI := dd.sheaf_colimits
  letI := dd.module_limits
  letI := dd.module_colimits
  ∃ sigmaE : sectionsE d ⟶ inverseImageIntegralModules l E g ⋙ sectionsE d,
  ∃ sigmaL : sectionsL d ⟶ inverseImageIntegralModules l L g ⋙ sectionsL d,
  (∀ (M : integralTowerModules l E (Spec (.of k)))
      (x : M.val.obj (pointFiniteFreeFinal k)),
    sigmaE.app M x = pointRestrictionRaw l E g none M x) ∧
  (∀ (M : integralTowerModules l L (Spec (.of k)))
      (x : M.val.obj (pointFiniteFreeFinal k)),
    sigmaL.app M x = pointRestrictionRaw l L g none M x) ∧
  ∃ tauE : (sectionsE d).mapDerivedCategory ⟶
    inverseImageIntegralDerived l E g ⋙ (sectionsE d).mapDerivedCategory,
  ∃ tauL : (sectionsL d).mapDerivedCategory ⟶
    inverseImageIntegralDerived l L g ⋙ (sectionsL d).mapDerivedCategory,
  (∀ P : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
    tauE.app (DerivedCategory.Q.obj P) ≫
        (sectionsE d).mapDerivedCategory.map
          ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P) ≫
        (sectionsE d).mapDerivedCategoryFactors.hom.app ((inverseComplex l E g).obj P) =
      (sectionsE d).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex sigmaE (.up ℤ)).app P)) ∧
  (∀ P : CochainComplex (integralTowerModules l L (Spec (.of k))) ℤ,
    tauL.app (DerivedCategory.Q.obj P) ≫
        (sectionsL d).mapDerivedCategory.map
          ((inverseImageIntegralModules l L g).mapDerivedCategoryFactors.hom.app P) ≫
        (sectionsL d).mapDerivedCategoryFactors.hom.app ((inverseComplex l L g).obj P) =
      (sectionsL d).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex sigmaL (.up ℤ)).app P)) ∧
  (∀ H : DerivedCategory (integralTowerModules l E (Spec (.of k))),
    (pointFiniteFreeModuleTensor.{t, u} l E L ι).mapDerivedCategory.map (tauE.app H) ≫
        dd.theta.hom.app ((inverseImageIntegralDerived l E g).obj H) ≫
        (sectionsL d).mapDerivedCategory.map (β.hom.app H) =
      dd.theta.hom.app H ≫
        tauL.app ((completedDerivedScalarExtension l E L ι (Spec (.of k))).obj H)) ∧
  (∀ P : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory,
    pointRestrictionTensorLeft d g sigmaE b P = pointRestrictionTensorRight d g sigmaL P.obj) ∧
  (∀ (P : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory)
      (n : ℤ) (x : (P.obj.X n).val.obj (pointFiniteFreeFinal k))
      (a : Padic.coefficientExtensionIntegers l L),
    ((pointRestrictionTensorLeft d g sigmaE b P).f n)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E, integralScalarIntegerInclusion l E L ι]
          (@id ((sectionsE d).obj (P.obj.X n)) x)) =
      completedScalarTensorSection l E L ι (Spec (.of k)) (P.obj.X n)
        (op ((Scheme.proEtaleIsoPostcompose g).obj (Scheme.ProEt.mk (𝟙 _))))
        ((completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k))).obj.map
          (pointRestrictionArrow g).op (d.coefficientL a))
        (pointRestrictionRaw l E g none (P.obj.X n) x)) ∧
  (∀ a : Padic.coefficientExtensionIntegers l L,
    (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k))).obj.map
        (pointRestrictionArrow g).op (d.coefficientL a) =
      (inv (inverseImageCompletedCoefficientMap l L g)).hom.app
        (pointFiniteFreeFinal k) (d.coefficientL a))

/-- The ordinary sections-tensor square for every ambient derived object and every
flat-term K-flat representative, with its common value after tensor sheafification.

Source: blueprint sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/
def-weil-global-geometric-frobenius.md, returned proof steps 1--2; Stacks 03EK and 06YS
(blueprint: lem-weil-point-restriction-ordinary-tensor-square).

Proof:
1. Choose P to H by lem-pc-kflat-resolution. The specified K-flat model of
lem-weil-isomorphism-scalar-tensor-kflat-model represents b on P and preserves
flat-term K-flatness under inverse image. Use lem-weil-point-derived-sections-tensor-descent
for both theta representatives and lem-weil-point-automorphism-restriction-natural
for the termwise sigma maps.
2. For x and a in degree n, sigmaE sends x to restriction to V. The coefficient
normalization of lem-weil-point-automorphism-restriction-natural identifies the
restricted a_s with c_L inverse(a_s). Substitute this into the local formula for b_P:
both inputs then give the sheafification image of restricted x tensor restricted a_s.
3. On the right, lem-weil-point-finite-free-sections-tensor first gives x tensor a_s.
Restriction of the presheaf tensor and naturality of its sheafification unit
(def-pur-sheaf-tensor-product and def-weil-pbc-sheafification) give the same value.
Pure tensors generate the source module tensor, proving equality degree by degree;
no generation assertion about sections of the target sheaf tensor is used.
4. All maps commute with differentials, so this is equality of chain maps. Localize
using lem-weil-point-proetale-sections-exact. The canonical counit comparisons of
the K-flat model and derived descent identify the resulting equality with square
for H. Their normalization and derived naturality of sigma make it independent of
the resolution. No boundedness, constructibility or completeness assumption is used. -/
theorem point_restriction_ordinary_tensor_square
    (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E L : IntermediateField ℚ_[l] Ω)
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (h : E ≤ L)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    [HasDerivedCategory.{wE}
      (ModuleCat.{max u (t + 1)} (Padic.coefficientExtensionIntegers l E))]
    [HasDerivedCategory.{wL}
      (ModuleCat.{max u (t + 1)} (Padic.coefficientExtensionIntegers l L))]
    (d : PointFiniteFreeSectionsTensorData D.k l E L (IntermediateField.inclusion h))
    (b : (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        leftComplex l E L (IntermediateField.inclusion h) g ≅
      (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        rightComplex l E L (IntermediateField.inclusion h) g)
    (β : inverseImageIntegralDerived l E g ⋙
        completedDerivedScalarExtension l E L (IntermediateField.inclusion h) (Spec (.of D.k)) ≅
      completedDerivedScalarExtension l E L (IntermediateField.inclusion h) (Spec (.of D.k)) ⋙
        inverseImageIntegralDerived l L g)
    (_hb : CompletedFormula l E L (IntermediateField.inclusion h) g b)
    (_hβ : DerivedModel l E L (IntermediateField.inclusion h) g b β) :
    ∃ dd : PointDerivedSectionsTensorData d, pointRestrictionOrdinaryTensorSquare d g dd b β := by
  sorry

end WeilConjectures
