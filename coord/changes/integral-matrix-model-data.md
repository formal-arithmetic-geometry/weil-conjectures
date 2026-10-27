# AlgebraicGeometry.ProEtale.IntegralMatrix.SimultaneousModels

## Reason

Separate the existing concrete data from the theorem so that two strictly smaller
proof obligations can import those definitions without an import cycle. This is an
interface relocation, not a definition repair. Every moved declaration keeps its
name, normalized signature, body and attribute. The original module publicly
imports the data module, preserving its public API. No target statement changes.

## Old

The following existing module prefix held the data and remains the exact old text:

```lean
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Paper.SectionwiseFiniteConstantLocalModel
public import Sheaf.Paper.CompletedIntegralOnSmallSite
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.Algebra.Homology.FiniteFreeResolutionTensor
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Simultaneous finite matrix models for integral local reductions

Source: Stacks 093J, 093M, 0AUW, 06YQ, 0E8K, 06YY and 07A6; blueprint
sk-def-sp-normalized-towers, constructibility paragraph
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction).

All natural-number indices represent the positive exponent n+1. We use the fixed small
site in a common containing universe; the scheme's universe remains independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe r t w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
namespace IntegralMatrix

variable (l : ℕ) [Fact l.Prime] (E : Type r) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Integers in the common value universe. Source: coefficient convention, Stacks 093M
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev Scalars := ULift.{r} (Padic.coefficientExtensionIntegers l E)

/-- The ell-power residue ring; n denotes exponent n+1, also in ramified extensions.
Source: coefficient convention (blueprint: lem-sp-integral-local-model-finite-matrix-reduction).
-/
abbrev Residues (n : ℕ) := ULift.{r}
  (WeilConjectures.CompletedSite.residue (Padic.coefficientExtensionIntegers l E)
    (l : Padic.coefficientExtensionIntegers l E) n)

/-- The scalar quotient induced by the identity on the integer ring. Source: Stacks 093M
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def scalarQuotient (n : ℕ) : Scalars l E →+* Residues l E n :=
  (Ideal.Quotient.mk (Ideal.span
    ({(l : Padic.coefficientExtensionIntegers l E)} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ (n + 1))).ulift

variable {C : Type r} [SmallCategory C] (J : GrothendieckTopology C)

/-- The existing constant quotient coefficient sheaf on the chosen small site.
Source: coefficient convention (blueprint: lem-sp-integral-local-model-finite-matrix-reduction).
-/
def coefficient (n : ℕ) : Sheaf J CommRingCat.{r} :=
  WeilConjectures.CompletedSite.constant.{r, r, 0} J
    (WeilConjectures.CompletedSite.residue (Padic.coefficientExtensionIntegers l E)
      (l : Padic.coefficientExtensionIntegers l E) n)

/-- The actual inverse limit of the constant ell-power quotient sheaves. Source: Stacks 093M
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def completion : Sheaf J CommRingCat.{r} :=
  WeilConjectures.CompletedSite.ring.{r, r, 0} J
    (Padic.coefficientExtensionIntegers l E) (l : Padic.coefficientExtensionIntegers l E)

/-- The canonical constant-scalar map into that limit. Source: Stacks 093M
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev scalarMap : realizationRing J (Scalars l E) ⟶ completion l E J :=
  WeilConjectures.CompletedSite.constantMap.{r, r, 0} J
    (Padic.coefficientExtensionIntegers l E) (l : Padic.coefficientExtensionIntegers l E)

/-- Its canonical projection to each positive level. Source: Stacks 093M
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def projection (n : ℕ) : completion l E J ⟶ coefficient l E J n :=
  limit.π (WeilConjectures.CompletedSite.tower.{r, r, 0} J
    (Padic.coefficientExtensionIntegers l E) (l : Padic.coefficientExtensionIntegers l E))
      (op n)

/-- Any actual quotient transition, including identities. Source: coefficient convention
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def quotient (m n : ℕ) (h : m ≤ n) : coefficient l E J n ⟶ coefficient l E J m :=
  (WeilConjectures.CompletedSite.tower.{r, r, 0} J
    (Padic.coefficientExtensionIntegers l E) (l : Padic.coefficientExtensionIntegers l E)).map
      (homOfLE h).op

/-- Entrywise reduction of a single scalar matrix. Source: the two-term DVR model
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def reduced {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :=
  d.map (scalarQuotient l E n)

/-- The cone of the map between degree-zero free modules: [R^a -> R^b] in degrees -1,0.
Source: Stacks 06YQ (blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
@[irreducible]
def matrixComplex {R : Type r} [CommRing R] {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) R) : CochainComplex (ModuleCat.{r} R) ℤ :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor _ 0).map
    (ModuleCat.ofHom (Matrix.toLin' d)))

/-- Module sheaves over the recorded coefficient ring. Source: Stacks 03DA
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

/-- Constant realization with its codomain expressed by the actual level coefficient.
Source: Stacks 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def constantAtLevel (n : ℕ) :
    ModuleCat.{r} (Residues l E n) ⥤ Modules J (coefficient l E J n) :=
  commutativeSiteConstantModuleFunctor J (Residues l E n)

/-- Additivity of the existing constant realization in the level presentation.
Source: Stacks 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
instance constantAtLevelAdditive (n : ℕ) : (constantAtLevel l E J n).Additive :=
  inferInstanceAs (commutativeSiteConstantModuleFunctor J (Residues l E n)).Additive

/-- Constant sheafification of the single reduced scalar complex.
Source: Stacks 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
@[irreducible]
def reducedComplex {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :
    CochainComplex (Modules J (coefficient l E J n)) ℤ :=
  ((constantAtLevel l E J n).mapHomologicalComplex (.up ℤ)).obj
    (matrixComplex (reduced l E d n))

variable [hD : ∀ (D : Type (r + 1)) [Category.{r} D] [Abelian D],
  HasDerivedCategory.{w} D]

/-- The existing universal derived coefficient presentations, not arbitrary functors.
Source: Stacks 06YY, 07A6 (blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def presentations : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    SheafOfModules.SuccessiveDerivedQuotient.Presentation.{r, r, r, w}
      (J := J) (hD := fun R : Sheaf J CommRingCat.{r} ↦
        hD (Modules J R)) a :=
  (SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization
    (J := J) (hD := fun R : Sheaf J CommRingCat.{r} ↦
        hD (Modules J R))).choose

/-- The existing pure-tensor and unit normalization of those universal pairs.
Source: Stacks 07A6 (blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
@[irreducible]
def normalization : SheafOfModules.SuccessiveDerivedQuotient.Normalization.{r, r, r, w}
    (J := J) (hD := fun R : Sheaf J CommRingCat.{r} ↦
        hD (Modules J R))
    (presentations J) :=
  Classical.choice
    (SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization
      (J := J) (hD := fun R : Sheaf J CommRingCat.{r} ↦
        hD (Modules J R))).choose_spec

/-- Ordinary completed scalar realization of a module, with the canonical tensor action.
Source: Stacks 03EK, 093M (blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
@[irreducible]
def model : ModuleCat.{r} (Scalars l E) ⥤ Modules J (completion l E J) :=
  commutativeSiteConstantModuleFunctor J (Scalars l E) ⋙
    (presentations J (scalarMap l E J)).ordinary

/-- The actual positive-level derived reduction of L[0].
Source: Stacks 06YY (blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def reduction (L : Modules J (completion l E J)) (n : ℕ) :=
  (presentations J (projection l E J n)).derived.obj
    ((DerivedCategory.singleFunctor _ 0).obj L)

/-- The quotient-induced derived transition, built from the normalized extension unit
and its coefficient associator. Source: Stacks 07A6
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
@[irreducible]
def transition (L : Modules J (completion l E J)) (m n : ℕ) (h : m ≤ n) :
    reduction l E J L n ⟶
      ((normalization J).right (quotient l E J m n h)).obj (reduction l E J L m) :=
  ((normalization J).adjunction (quotient l E J m n h)).unit.app
      ((presentations J (projection l E J n)).derived.obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≫
    ((normalization J).right (quotient l E J m n h)).map
      (((normalization J).derived (projection l E J n) (quotient l E J m n h)).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≫
    ((normalization J).right (quotient l E J m n h)).map
      (eqToHom (congrArg
        (fun a ↦ (presentations J a).derived.obj ((DerivedCategory.singleFunctor _ 0).obj L))
        (limit.w (WeilConjectures.CompletedSite.tower.{r, r, 0} J
          (Padic.coefficientExtensionIntegers l E)
          (l : Padic.coefficientExtensionIntegers l E)) (homOfLE h).op)))

/-- Canonical additivity of slice restriction. Source: Stacks 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
instance overAdditive (R : Sheaf J RingCat.{r}) (U : C) :
    (SheafOfModules.overFunctor.{r} R U).Additive :=
  (ringedOverFunctor_exactGeneral.{r, r, r, r} R U).1

/-- Canonical left exactness of slice restriction. Source: Stacks 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
instance overLimits (R : Sheaf J RingCat.{r}) (U : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{r} R U) :=
  (ringedOverFunctor_exactGeneral.{r, r, r, r} R U).2.1

/-- Canonical right exactness of slice restriction. Source: Stacks 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
instance overColimits (R : Sheaf J RingCat.{r}) (U : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{r} R U) :=
  (ringedOverFunctor_exactGeneral.{r, r, r, r} R U).2.2

/-- Exact slice restriction on complexes, in the original restricted coefficient ring.
Source: Stacks 03DH (blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev overComplex (R : Sheaf J CommRingCat.{r}) (U : C) :=
  (SheafOfModules.overFunctor.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U).mapHomologicalComplex
      (.up ℤ)

/-- Constant vectors as sections of the actual sheafification, used to specify matrices
and their quotient maps without choosing arbitrary sheaf morphisms. Source: Stacks 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def vector {R : Type r} [CommRing R] (a : ℕ) (V : Cᵒᵖ) (x : Fin a → R) :
    ((commutativeSiteConstantModuleFunctor J R).obj
      (ModuleCat.of R (Fin a → R))).val.obj V :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (Fin a → R)))).app V x

/-- Constant vectors with the codomain given by the actual coefficient presentation.
Source: Stacks 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def vectorAtLevel (n a : ℕ) (V : Cᵒᵖ) (x : Fin a → Residues l E n) :
    ((constantAtLevel l E J n).obj
      (ModuleCat.of (Residues l E n) (Fin a → Residues l E n))).val.obj V :=
  vector J a V x

/-- Scalar reduction between any two positive quotient rings. Source: coefficient tower
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def scalarReduction (m n : ℕ) (h : m ≤ n) : Residues l E n →+* Residues l E m :=
  (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).ulift

/-- The concrete reduced kernel as a scalar module. Source: Stacks 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev scalarKernel {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :=
  LinearMap.ker (Matrix.toLin' (reduced l E d n))

/-- The concrete reduced cokernel as a scalar module. Source: Stacks 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev scalarCokernel {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :=
  (Fin b → Residues l E n) ⧸ LinearMap.range (Matrix.toLin' (reduced l E d n))


/-- The actual restricted quotient. Source: Stacks 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def overQuotient (U : C) (m n : ℕ) (h : m ≤ n) :=
  (J.overPullback CommRingCat.{r} U).map (quotient l E J m n h)

/-- Exact derived restriction to the slice, without replacing the completed ring.
Source: Stacks 0E8K (blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev overDerived (R : Sheaf J CommRingCat.{r}) (U : C) :
    DerivedCategory (Modules J R) ⥤
      DerivedCategory (SheafOfModules.{r}
        ((SheafOfModules.derivedChangeRingIndependentCoefficients J R).over U)) :=
  Functor.mapDerivedCategory.{w, w}
    (SheafOfModules.overFunctor.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U)

/-- The canonical factorization for slice restriction on homotopy representatives.
Source: Stacks 08JB (blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def overFactors (R : Sheaf J CommRingCat.{r}) (U : C) :=
  Functor.mapDerivedCategoryFactorsh.{w, w}
    (SheafOfModules.overFunctor.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U)

/-- Scalar restriction on the slice with the specified original coefficient rings.
Source: Stacks 03DA, 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def sliceScalars {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    SheafOfModules.{r}
        ((SheafOfModules.derivedChangeRingIndependentCoefficients J T).over U) ⥤
      SheafOfModules.{r}
        ((SheafOfModules.derivedChangeRingIndependentCoefficients J R).over U) :=
  SheafOfModules.restrictedTensorScalars.{r, r, r}
    ((J.overPullback CommRingCat.{r} U).map q)

/-- Additivity of scalar restriction on a slice. Source: Stacks 03DA
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
instance sliceScalarsAdditive {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    (sliceScalars J q U).Additive :=
  inferInstanceAs (SheafOfModules.restrictedTensorScalars.{r, r, r}
    ((J.overPullback CommRingCat.{r} U).map q)).Additive

/-- Left exactness of scalar restriction on a slice. Source: Stacks 03DA
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
instance sliceScalarsLimits {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    PreservesFiniteLimits (sliceScalars J q U) :=
  SheafOfModules.restrictedTensorScalars_preservesFiniteLimits.{r, r, r} _

/-- Right exactness of scalar restriction on a slice. Source: Stacks 03DA
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
instance sliceScalarsColimits {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    PreservesFiniteColimits (sliceScalars J q U) :=
  SheafOfModules.restrictedTensorScalars_preservesFiniteColimits.{r, r, r} _

/-- Canonical exact derived scalar restriction on a slice. Source: Stacks 03DA, 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev sliceDerived {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    DerivedCategory (SheafOfModules.{r}
      ((SheafOfModules.derivedChangeRingIndependentCoefficients J T).over U)) ⥤
    DerivedCategory (SheafOfModules.{r}
      ((SheafOfModules.derivedChangeRingIndependentCoefficients J R).over U)) :=
  Functor.mapDerivedCategory.{w, w} (sliceScalars J q U)

/-- The canonical homotopy localization factorization of slice scalar restriction.
Source: Stacks 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev sliceFactorsh {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :=
  Functor.mapDerivedCategoryFactorsh.{w, w} (sliceScalars J q U)

/-- The canonical interchange of scalar and slice restriction. Its component maps
are identities on the underlying sections. Source: Stacks 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def restrictionOverIso {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    SheafOfModules.SuccessiveDerivedQuotient.restriction.{r, r, r} q ⋙
        SheafOfModules.overFunctor.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U ≅
      SheafOfModules.overFunctor.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J T) U ⋙
        sliceScalars J q U :=
  NatIso.ofComponents fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ Iso.refl _))

/-- Compose two specified homotopy localization factorizations.
Source: Stacks 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def composeFactors {D₀ D₁ D₂ : Type (r + 1)}
    [Category.{r} D₀] [Category.{r} D₁] [Category.{r} D₂]
    [Abelian D₀] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory.{w} D₀] [HasDerivedCategory.{w} D₁] [HasDerivedCategory.{w} D₂]
    (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂) [F.Additive] [G.Additive]
    (DF : DerivedCategory D₀ ⥤ DerivedCategory D₁)
    (DG : DerivedCategory D₁ ⥤ DerivedCategory D₂)
    (eF : DerivedCategory.Qh ⋙ DF ≅ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (eG : DerivedCategory.Qh ⋙ DG ≅ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Qh ⋙ (DF ⋙ DG) ≅
      (F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ)) ⋙
        DerivedCategory.Qh :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eF DG ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eG ≪≫
      (Functor.associator _ _ _).symm

/-- Localize a commuting square of additive functors equipped with their canonical
homotopy factorizations. Source: Stacks 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def localizeSquare {D₀ D₁ D₂ D₃ : Type (r + 1)}
    [Category.{r} D₀] [Category.{r} D₁] [Category.{r} D₂] [Category.{r} D₃]
    [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
    [HasDerivedCategory.{w} D₀] [HasDerivedCategory.{w} D₁]
    [HasDerivedCategory.{w} D₂] [HasDerivedCategory.{w} D₃]
    (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₃) (H : D₀ ⥤ D₂) (K : D₂ ⥤ D₃)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    (DF : DerivedCategory D₀ ⥤ DerivedCategory D₁)
    (DG : DerivedCategory D₁ ⥤ DerivedCategory D₃)
    (DH : DerivedCategory D₀ ⥤ DerivedCategory D₂)
    (DK : DerivedCategory D₂ ⥤ DerivedCategory D₃)
    (eF : DerivedCategory.Qh ⋙ DF ≅ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (eG : DerivedCategory.Qh ⋙ DG ≅ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (eH : DerivedCategory.Qh ⋙ DH ≅ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (eK : DerivedCategory.Qh ⋙ DK ≅ K.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : F ⋙ G ≅ H ⋙ K) : DF ⋙ DG ≅ DH ⋙ DK :=
  let eh : F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ≅
      H.mapHomotopyCategory (.up ℤ) ⋙ K.mapHomotopyCategory (.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso (F := F) (G := G) (H := H ⋙ K) e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (F := H) (G := K) (H := H ⋙ K)
        (Iso.refl _) (.up ℤ)).symm
  Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso D₀ (.up ℤ))
    (DerivedCategory.Qh ⋙ (DF ⋙ DG)) (DerivedCategory.Qh ⋙ (DH ⋙ DK))
    (DF ⋙ DG) (DH ⋙ DK)
    (composeFactors F G DF DG eF eG ≪≫ Functor.isoWhiskerRight eh DerivedCategory.Qh ≪≫
      (composeFactors H K DH DK eH eK).symm)

/-- Canonical derived interchange of scalar restriction and slice restriction.
Source: Stacks 03DA, 03DH, 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def derivedRestrictionOverGeneral {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    (normalization J).right q ⋙ overDerived J R U ≅
      overDerived J T U ⋙ sliceDerived J q U :=
  localizeSquare (SheafOfModules.SuccessiveDerivedQuotient.restriction.{r, r, r} q)
    (SheafOfModules.overFunctor.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U)
    (SheafOfModules.overFunctor.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J T) U)
    (sliceScalars J q U)
    ((normalization J).right q) (overDerived J R U) (overDerived J T U)
    (sliceDerived J q U) ((normalization J).right_factors q)
    (overFactors J R U) (overFactors J T U) (sliceFactorsh J q U)
    (restrictionOverIso J q U)

/-- Actual quotient scalar restriction on the slice. Source: Stacks 03DA
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev quotientRestriction (U : C) (m n : ℕ) (h : m ≤ n) :=
  sliceScalars J (quotient l E J m n h) U

/-- Actual quotient scalar restriction on derived slice categories. Source: Stacks 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev quotientDerived (U : C) (m n : ℕ) (h : m ≤ n) :=
  sliceDerived J (quotient l E J m n h) U

/-- Complex localization comparison for quotient restriction. Source: Stacks 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def quotientFactors (U : C) (m n : ℕ) (h : m ≤ n) :=
  Functor.mapDerivedCategoryFactors.{w, w} (quotientRestriction l E J U m n h)

/-- Homotopy localization comparison for quotient restriction. Source: Stacks 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def quotientFactorsh (U : C) (m n : ℕ) (h : m ≤ n) :=
  Functor.mapDerivedCategoryFactorsh.{w, w} (quotientRestriction l E J U m n h)

/-- The canonical interchange for the actual quotient map. Source: Stacks 03DH, 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def derivedRestrictionOverIso (U : C) (m n : ℕ) (h : m ≤ n) :=
  derivedRestrictionOverGeneral J (quotient l E J m n h) U

/-- The actual quotient-induced transition after slice restriction, with its target
identified by the canonical restriction interchange. Source: Stacks 07A6, 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def restrictedTransition (L : Modules J (completion l E J)) (U : C)
    (m n : ℕ) (h : m ≤ n) :
    (overDerived J (coefficient l E J n) U).obj (reduction l E J L n) ⟶
      (quotientDerived l E J U m n h).obj
        ((overDerived J (coefficient l E J m) U).obj (reduction l E J L m)) :=
  (overDerived J (coefficient l E J n) U).map (transition l E J L m n h) ≫
    (derivedRestrictionOverIso l E J U m n h).hom.app (reduction l E J L m)

/-- The original restricted module category. Source: Stacks 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
abbrev SliceModules (R : Sheaf J CommRingCat.{r}) (U : C) :=
  SheafOfModules.{r} ((SheafOfModules.derivedChangeRingIndependentCoefficients J R).over U)

/-- The derived reduction restricted to the specified covering object.
Source: Stacks 06YY, 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def localReduction (L : Modules J (completion l E J)) (U : C) (n : ℕ) :
    DerivedCategory (SliceModules J (coefficient l E J n) U) :=
  (overDerived J (coefficient l E J n) U).obj (reduction l E J L n)

/-- The single reduced matrix complex on the specified covering object.
Source: Stacks 093J, 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def localMatrix (U : C) {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :
    CochainComplex (SliceModules J (coefficient l E J n) U) ℤ :=
  (overComplex J (coefficient l E J n) U).obj (reducedComplex l E J d n)

/-- Localization of that very matrix complex. Source: Stacks 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def localMatrixObject (U : C) {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :
    DerivedCategory (SliceModules J (coefficient l E J n) U) :=
  DerivedCategory.Q.obj (localMatrix l E J U d n)

/-- The finite free constant module with its explicit level coefficient type.
Source: Stacks 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def freeAtLevel (n a : ℕ) : Modules J (coefficient l E J n) :=
  (constantAtLevel l E J n).obj
    (ModuleCat.of (Residues l E n) (Fin a → Residues l E n))

/-- A basis identification for one term of the specified matrix complex.
Source: Stacks 093J, 06YQ
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def TermBasis {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (n : ℕ) (i : ℤ) (rank : ℕ) :=
  @Iso (Modules J (coefficient l E J n)) _
    ((reducedComplex l E J d n).X i) (freeAtLevel l E J n rank)

/-- The differential is the entrywise reduction of the integral scalar matrix.
Source: Stacks 093J, 06YQ
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def MatrixDifferential {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (left : ∀ n : ℕ, TermBasis l E J d n (-1) a)
    (right : ∀ n : ℕ, TermBasis l E J d n 0 b) : Prop :=
  ∀ (n : ℕ) (V : Cᵒᵖ) (x : Fin a → Residues l E n),
    ((left n).inv ≫ (reducedComplex l E J d n).d (-1) 0 ≫ (right n).hom).val.app V
      (vectorAtLevel l E J n a V x) =
        vectorAtLevel l E J n b V (Matrix.toLin' (reduced l E d n) x)

/-- Only the two stated free degrees occur. Source: Stacks 06YQ
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def MatrixSupport {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) : Prop :=
  ∀ (n : ℕ) (i : ℤ), i ≠ -1 → i ≠ 0 →
    @IsZero (Modules J (coefficient l E J n)) _ ((reducedComplex l E J d n).X i)

/-- Type of the actual termwise quotient chain map. Source: Stacks 07A6, 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def MatrixQuotient (U : C) {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (m n : ℕ) (h : m ≤ n) :=
  @Quiver.Hom (CochainComplex (SliceModules J (coefficient l E J n) U) ℤ) _
    (localMatrix l E J U d n)
    (((quotientRestriction l E J U m n h).mapHomologicalComplex (.up ℤ)).obj
      (localMatrix l E J U d m))

/-- Scalar restriction on a slice leaves the underlying sections unchanged.
Source: Stacks 03DA, 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def scalarRestrictionSection {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C)
    (M : SheafOfModules.{r}
      ((SheafOfModules.derivedChangeRingIndependentCoefficients J T).over U))
    (V : (Over U)ᵒᵖ) :
    ((sliceScalars J q U).obj M).val.obj V → M.val.obj V :=
  id

/-- The underlying section map of the quotient chain map in a specified degree.
Source: Stacks 03DA, 03DH
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def matrixQuotientApply (U : C) {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) (Scalars l E)) (m n : ℕ) (h : m ≤ n)
    (f : MatrixQuotient l E J U d m n h) (i : ℤ) (V : (Over U)ᵒᵖ) :
    ((localMatrix l E J U d n).X i).val.obj V →
      ((localMatrix l E J U d m).X i).val.obj V :=
  fun x ↦ scalarRestrictionSection J (quotient l E J m n h) U
    ((localMatrix l E J U d m).X i) V ((f.f i).val.app V x)

/-- The quotient in a specified free degree is entrywise scalar reduction.
Source: Stacks 07A6, 093J
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def MatrixQuotientDegree (U : C) {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) (Scalars l E)) (i : ℤ) (rank : ℕ)
    (basis : ∀ n : ℕ, TermBasis l E J d n i rank)
    (termwise : ∀ (m n : ℕ) (h : m ≤ n), MatrixQuotient l E J U d m n h) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n) (V : (Over U)ᵒᵖ) (x : Fin rank → Residues l E n),
    (basis m).hom.val.app (op V.unop.left)
      (matrixQuotientApply l E J U d m n h (termwise m n h) i V
        ((basis n).inv.val.app (op V.unop.left)
          (vectorAtLevel l E J n rank (op V.unop.left) x))) =
      vectorAtLevel l E J m rank (op V.unop.left)
        (fun j ↦ scalarReduction l E m n h (x j))

/-- The actual derived quotient transition is the localization of the termwise quotient.
Source: Stacks 07A6, 08JB
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
def MatrixTransitionSquare (L : Modules J (completion l E J)) (U : C) {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (comparison : ∀ n : ℕ, localReduction l E J L U n ≅ localMatrixObject l E J U d n)
    (termwise : ∀ (m n : ℕ) (h : m ≤ n), MatrixQuotient l E J U d m n h) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n),
    restrictedTransition l E J L U m n h ≫
      (quotientDerived l E J U m n h).map (comparison m).hom ≫
      (quotientFactors l E J U m n h).hom.app (localMatrix l E J U d m) =
    (comparison n).hom ≫ DerivedCategory.Q.map (termwise m n h)

/-- The simultaneous model and its quotient squares. Each comparison is an isomorphism
in the localized coefficient derived category. The derived interchange is the localization of the
identity on sections, so the quotient square uses the actual exact restrictions.
The termwise quotient is fixed on all constant vector generators in both free degrees.
Source: Stacks 06YY, 07A6, 093J; the node proof, steps 1--4
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction). -/
structure SimultaneousModels (L : Modules J (completion l E J)) (U : C)
    {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) where
  comparison : ∀ n : ℕ,
    localReduction l E J L U n ≅
      localMatrixObject l E J U d n
  left : ∀ n : ℕ, TermBasis l E J d n (-1) a
  right : ∀ n : ℕ, TermBasis l E J d n 0 b
  differential : MatrixDifferential l E J d left right
  support : MatrixSupport l E J d
  termwise : ∀ (m n : ℕ) (h : m ≤ n), MatrixQuotient l E J U d m n h
  quotient_left : MatrixQuotientDegree l E J U d (-1) a left termwise
  quotient_right : MatrixQuotientDegree l E J U d 0 b right termwise
  transition_square : MatrixTransitionSquare l E J L U d comparison termwise


```

## New

The concrete declarations live in `Sheaf.Paper.IntegralMatrixModelData`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Paper.SectionwiseFiniteConstantLocalModel
public import Sheaf.Paper.CompletedIntegralOnSmallSite
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Simultaneous finite matrix models for integral local reductions

Source: Stacks 093J, 093M, 0AUW, 06YQ, 0E8K, 06YY and 07A6; blueprint
sk-def-sp-normalized-towers, constructibility paragraph
(blueprint: def-sp-integral-matrix-model-data).

All natural-number indices represent the positive exponent n+1. We use the fixed small
site in a common containing universe; the scheme's universe remains independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe r t w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
namespace IntegralMatrix

variable (l : ℕ) [Fact l.Prime] (E : Type r) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Integers in the common value universe. Source: coefficient convention, Stacks 093M
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev Scalars := ULift.{r} (Padic.coefficientExtensionIntegers l E)

/-- The ell-power residue ring; n denotes exponent n+1, also in ramified extensions.
Source: coefficient convention (blueprint: def-sp-integral-matrix-model-data).
-/
abbrev Residues (n : ℕ) := ULift.{r}
  (WeilConjectures.CompletedSite.residue (Padic.coefficientExtensionIntegers l E)
    (l : Padic.coefficientExtensionIntegers l E) n)

/-- The scalar quotient induced by the identity on the integer ring. Source: Stacks 093M
(blueprint: def-sp-integral-matrix-model-data). -/
def scalarQuotient (n : ℕ) : Scalars l E →+* Residues l E n :=
  (Ideal.Quotient.mk (Ideal.span
    ({(l : Padic.coefficientExtensionIntegers l E)} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ (n + 1))).ulift

variable {C : Type r} [SmallCategory C] (J : GrothendieckTopology C)

/-- The existing constant quotient coefficient sheaf on the chosen small site.
Source: coefficient convention (blueprint: def-sp-integral-matrix-model-data).
-/
def coefficient (n : ℕ) : Sheaf J CommRingCat.{r} :=
  WeilConjectures.CompletedSite.constant.{r, r, 0} J
    (WeilConjectures.CompletedSite.residue (Padic.coefficientExtensionIntegers l E)
      (l : Padic.coefficientExtensionIntegers l E) n)

/-- The actual inverse limit of the constant ell-power quotient sheaves. Source: Stacks 093M
(blueprint: def-sp-integral-matrix-model-data). -/
def completion : Sheaf J CommRingCat.{r} :=
  WeilConjectures.CompletedSite.ring.{r, r, 0} J
    (Padic.coefficientExtensionIntegers l E) (l : Padic.coefficientExtensionIntegers l E)

/-- The canonical constant-scalar map into that limit. Source: Stacks 093M
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev scalarMap : realizationRing J (Scalars l E) ⟶ completion l E J :=
  WeilConjectures.CompletedSite.constantMap.{r, r, 0} J
    (Padic.coefficientExtensionIntegers l E) (l : Padic.coefficientExtensionIntegers l E)

/-- Its canonical projection to each positive level. Source: Stacks 093M
(blueprint: def-sp-integral-matrix-model-data). -/
def projection (n : ℕ) : completion l E J ⟶ coefficient l E J n :=
  limit.π (WeilConjectures.CompletedSite.tower.{r, r, 0} J
    (Padic.coefficientExtensionIntegers l E) (l : Padic.coefficientExtensionIntegers l E))
      (op n)

/-- Any actual quotient transition, including identities. Source: coefficient convention
(blueprint: def-sp-integral-matrix-model-data). -/
def quotient (m n : ℕ) (h : m ≤ n) : coefficient l E J n ⟶ coefficient l E J m :=
  (WeilConjectures.CompletedSite.tower.{r, r, 0} J
    (Padic.coefficientExtensionIntegers l E) (l : Padic.coefficientExtensionIntegers l E)).map
      (homOfLE h).op

/-- Entrywise reduction of a single scalar matrix. Source: the two-term DVR model
(blueprint: def-sp-integral-matrix-model-data). -/
def reduced {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :=
  d.map (scalarQuotient l E n)

/-- The cone of the map between degree-zero free modules: [R^a -> R^b] in degrees -1,0.
Source: Stacks 06YQ (blueprint: def-sp-integral-matrix-model-data). -/
@[irreducible]
def matrixComplex {R : Type r} [CommRing R] {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) R) : CochainComplex (ModuleCat.{r} R) ℤ :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor _ 0).map
    (ModuleCat.ofHom (Matrix.toLin' d)))

/-- Module sheaves over the recorded coefficient ring. Source: Stacks 03DA
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

/-- Constant realization with its codomain expressed by the actual level coefficient.
Source: Stacks 093J
(blueprint: def-sp-integral-matrix-model-data). -/
def constantAtLevel (n : ℕ) :
    ModuleCat.{r} (Residues l E n) ⥤ Modules J (coefficient l E J n) :=
  commutativeSiteConstantModuleFunctor J (Residues l E n)

/-- Additivity of the existing constant realization in the level presentation.
Source: Stacks 093J
(blueprint: def-sp-integral-matrix-model-data). -/
instance constantAtLevelAdditive (n : ℕ) : (constantAtLevel l E J n).Additive :=
  inferInstanceAs (commutativeSiteConstantModuleFunctor J (Residues l E n)).Additive

/-- Constant sheafification of the single reduced scalar complex.
Source: Stacks 093J
(blueprint: def-sp-integral-matrix-model-data). -/
@[irreducible]
def reducedComplex {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :
    CochainComplex (Modules J (coefficient l E J n)) ℤ :=
  ((constantAtLevel l E J n).mapHomologicalComplex (.up ℤ)).obj
    (matrixComplex (reduced l E d n))

variable [hD : ∀ (D : Type (r + 1)) [Category.{r} D] [Abelian D],
  HasDerivedCategory.{w} D]

/-- The existing universal derived coefficient presentations, not arbitrary functors.
Source: Stacks 06YY, 07A6 (blueprint: def-sp-integral-matrix-model-data). -/
def presentations : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    SheafOfModules.SuccessiveDerivedQuotient.Presentation.{r, r, r, w}
      (J := J) (hD := fun R : Sheaf J CommRingCat.{r} ↦
        hD (Modules J R)) a :=
  (SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization
    (J := J) (hD := fun R : Sheaf J CommRingCat.{r} ↦
        hD (Modules J R))).choose

/-- The existing pure-tensor and unit normalization of those universal pairs.
Source: Stacks 07A6 (blueprint: def-sp-integral-matrix-model-data). -/
@[irreducible]
def normalization : SheafOfModules.SuccessiveDerivedQuotient.Normalization.{r, r, r, w}
    (J := J) (hD := fun R : Sheaf J CommRingCat.{r} ↦
        hD (Modules J R))
    (presentations J) :=
  Classical.choice
    (SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization
      (J := J) (hD := fun R : Sheaf J CommRingCat.{r} ↦
        hD (Modules J R))).choose_spec

/-- Ordinary completed scalar realization of a module, with the canonical tensor action.
Source: Stacks 03EK, 093M (blueprint: def-sp-integral-matrix-model-data). -/
@[irreducible]
def model : ModuleCat.{r} (Scalars l E) ⥤ Modules J (completion l E J) :=
  commutativeSiteConstantModuleFunctor J (Scalars l E) ⋙
    (presentations J (scalarMap l E J)).ordinary

/-- The actual positive-level derived reduction of L[0].
Source: Stacks 06YY (blueprint: def-sp-integral-matrix-model-data). -/
def reduction (L : Modules J (completion l E J)) (n : ℕ) :=
  (presentations J (projection l E J n)).derived.obj
    ((DerivedCategory.singleFunctor _ 0).obj L)

/-- The quotient-induced derived transition, built from the normalized extension unit
and its coefficient associator. Source: Stacks 07A6
(blueprint: def-sp-integral-matrix-model-data). -/
@[irreducible]
def transition (L : Modules J (completion l E J)) (m n : ℕ) (h : m ≤ n) :
    reduction l E J L n ⟶
      ((normalization J).right (quotient l E J m n h)).obj (reduction l E J L m) :=
  ((normalization J).adjunction (quotient l E J m n h)).unit.app
      ((presentations J (projection l E J n)).derived.obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≫
    ((normalization J).right (quotient l E J m n h)).map
      (((normalization J).derived (projection l E J n) (quotient l E J m n h)).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≫
    ((normalization J).right (quotient l E J m n h)).map
      (eqToHom (congrArg
        (fun a ↦ (presentations J a).derived.obj ((DerivedCategory.singleFunctor _ 0).obj L))
        (limit.w (WeilConjectures.CompletedSite.tower.{r, r, 0} J
          (Padic.coefficientExtensionIntegers l E)
          (l : Padic.coefficientExtensionIntegers l E)) (homOfLE h).op)))

/-- Canonical additivity of slice restriction. Source: Stacks 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
instance overAdditive (R : Sheaf J RingCat.{r}) (U : C) :
    (SheafOfModules.overFunctor.{r} R U).Additive :=
  (ringedOverFunctor_exactGeneral.{r, r, r, r} R U).1

/-- Canonical left exactness of slice restriction. Source: Stacks 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
instance overLimits (R : Sheaf J RingCat.{r}) (U : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{r} R U) :=
  (ringedOverFunctor_exactGeneral.{r, r, r, r} R U).2.1

/-- Canonical right exactness of slice restriction. Source: Stacks 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
instance overColimits (R : Sheaf J RingCat.{r}) (U : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{r} R U) :=
  (ringedOverFunctor_exactGeneral.{r, r, r, r} R U).2.2

/-- Exact slice restriction on complexes, in the original restricted coefficient ring.
Source: Stacks 03DH (blueprint: def-sp-integral-matrix-model-data). -/
abbrev overComplex (R : Sheaf J CommRingCat.{r}) (U : C) :=
  (SheafOfModules.overFunctor.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U).mapHomologicalComplex
      (.up ℤ)

/-- Constant vectors as sections of the actual sheafification, used to specify matrices
and their quotient maps without choosing arbitrary sheaf morphisms. Source: Stacks 093J
(blueprint: def-sp-integral-matrix-model-data). -/
def vector {R : Type r} [CommRing R] (a : ℕ) (V : Cᵒᵖ) (x : Fin a → R) :
    ((commutativeSiteConstantModuleFunctor J R).obj
      (ModuleCat.of R (Fin a → R))).val.obj V :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (Fin a → R)))).app V x

/-- Constant vectors with the codomain given by the actual coefficient presentation.
Source: Stacks 093J
(blueprint: def-sp-integral-matrix-model-data). -/
def vectorAtLevel (n a : ℕ) (V : Cᵒᵖ) (x : Fin a → Residues l E n) :
    ((constantAtLevel l E J n).obj
      (ModuleCat.of (Residues l E n) (Fin a → Residues l E n))).val.obj V :=
  vector J a V x

/-- Scalar reduction between any two positive quotient rings. Source: coefficient tower
(blueprint: def-sp-integral-matrix-model-data). -/
def scalarReduction (m n : ℕ) (h : m ≤ n) : Residues l E n →+* Residues l E m :=
  (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).ulift

/-- The concrete reduced kernel as a scalar module. Source: Stacks 093J
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev scalarKernel {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :=
  LinearMap.ker (Matrix.toLin' (reduced l E d n))

/-- The concrete reduced cokernel as a scalar module. Source: Stacks 093J
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev scalarCokernel {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :=
  (Fin b → Residues l E n) ⧸ LinearMap.range (Matrix.toLin' (reduced l E d n))


/-- The actual restricted quotient. Source: Stacks 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
def overQuotient (U : C) (m n : ℕ) (h : m ≤ n) :=
  (J.overPullback CommRingCat.{r} U).map (quotient l E J m n h)

/-- Exact derived restriction to the slice, without replacing the completed ring.
Source: Stacks 0E8K (blueprint: def-sp-integral-matrix-model-data). -/
abbrev overDerived (R : Sheaf J CommRingCat.{r}) (U : C) :
    DerivedCategory (Modules J R) ⥤
      DerivedCategory (SheafOfModules.{r}
        ((SheafOfModules.derivedChangeRingIndependentCoefficients J R).over U)) :=
  Functor.mapDerivedCategory.{w, w}
    (SheafOfModules.overFunctor.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U)

/-- The canonical factorization for slice restriction on homotopy representatives.
Source: Stacks 08JB (blueprint: def-sp-integral-matrix-model-data). -/
def overFactors (R : Sheaf J CommRingCat.{r}) (U : C) :=
  Functor.mapDerivedCategoryFactorsh.{w, w}
    (SheafOfModules.overFunctor.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U)

/-- Scalar restriction on the slice with the specified original coefficient rings.
Source: Stacks 03DA, 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
def sliceScalars {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    SheafOfModules.{r}
        ((SheafOfModules.derivedChangeRingIndependentCoefficients J T).over U) ⥤
      SheafOfModules.{r}
        ((SheafOfModules.derivedChangeRingIndependentCoefficients J R).over U) :=
  SheafOfModules.restrictedTensorScalars.{r, r, r}
    ((J.overPullback CommRingCat.{r} U).map q)

/-- Additivity of scalar restriction on a slice. Source: Stacks 03DA
(blueprint: def-sp-integral-matrix-model-data). -/
instance sliceScalarsAdditive {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    (sliceScalars J q U).Additive :=
  inferInstanceAs (SheafOfModules.restrictedTensorScalars.{r, r, r}
    ((J.overPullback CommRingCat.{r} U).map q)).Additive

/-- Left exactness of scalar restriction on a slice. Source: Stacks 03DA
(blueprint: def-sp-integral-matrix-model-data). -/
instance sliceScalarsLimits {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    PreservesFiniteLimits (sliceScalars J q U) :=
  SheafOfModules.restrictedTensorScalars_preservesFiniteLimits.{r, r, r} _

/-- Right exactness of scalar restriction on a slice. Source: Stacks 03DA
(blueprint: def-sp-integral-matrix-model-data). -/
instance sliceScalarsColimits {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    PreservesFiniteColimits (sliceScalars J q U) :=
  SheafOfModules.restrictedTensorScalars_preservesFiniteColimits.{r, r, r} _

/-- Canonical exact derived scalar restriction on a slice. Source: Stacks 03DA, 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev sliceDerived {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    DerivedCategory (SheafOfModules.{r}
      ((SheafOfModules.derivedChangeRingIndependentCoefficients J T).over U)) ⥤
    DerivedCategory (SheafOfModules.{r}
      ((SheafOfModules.derivedChangeRingIndependentCoefficients J R).over U)) :=
  Functor.mapDerivedCategory.{w, w} (sliceScalars J q U)

/-- The canonical homotopy localization factorization of slice scalar restriction.
Source: Stacks 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev sliceFactorsh {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :=
  Functor.mapDerivedCategoryFactorsh.{w, w} (sliceScalars J q U)

/-- The canonical interchange of scalar and slice restriction. Its component maps
are identities on the underlying sections. Source: Stacks 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
def restrictionOverIso {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    SheafOfModules.SuccessiveDerivedQuotient.restriction.{r, r, r} q ⋙
        SheafOfModules.overFunctor.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U ≅
      SheafOfModules.overFunctor.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J T) U ⋙
        sliceScalars J q U :=
  NatIso.ofComponents fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ Iso.refl _))

/-- Compose two specified homotopy localization factorizations.
Source: Stacks 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
def composeFactors {D₀ D₁ D₂ : Type (r + 1)}
    [Category.{r} D₀] [Category.{r} D₁] [Category.{r} D₂]
    [Abelian D₀] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory.{w} D₀] [HasDerivedCategory.{w} D₁] [HasDerivedCategory.{w} D₂]
    (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂) [F.Additive] [G.Additive]
    (DF : DerivedCategory D₀ ⥤ DerivedCategory D₁)
    (DG : DerivedCategory D₁ ⥤ DerivedCategory D₂)
    (eF : DerivedCategory.Qh ⋙ DF ≅ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (eG : DerivedCategory.Qh ⋙ DG ≅ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Qh ⋙ (DF ⋙ DG) ≅
      (F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ)) ⋙
        DerivedCategory.Qh :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eF DG ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eG ≪≫
      (Functor.associator _ _ _).symm

/-- Localize a commuting square of additive functors equipped with their canonical
homotopy factorizations. Source: Stacks 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
def localizeSquare {D₀ D₁ D₂ D₃ : Type (r + 1)}
    [Category.{r} D₀] [Category.{r} D₁] [Category.{r} D₂] [Category.{r} D₃]
    [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
    [HasDerivedCategory.{w} D₀] [HasDerivedCategory.{w} D₁]
    [HasDerivedCategory.{w} D₂] [HasDerivedCategory.{w} D₃]
    (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₃) (H : D₀ ⥤ D₂) (K : D₂ ⥤ D₃)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    (DF : DerivedCategory D₀ ⥤ DerivedCategory D₁)
    (DG : DerivedCategory D₁ ⥤ DerivedCategory D₃)
    (DH : DerivedCategory D₀ ⥤ DerivedCategory D₂)
    (DK : DerivedCategory D₂ ⥤ DerivedCategory D₃)
    (eF : DerivedCategory.Qh ⋙ DF ≅ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (eG : DerivedCategory.Qh ⋙ DG ≅ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (eH : DerivedCategory.Qh ⋙ DH ≅ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (eK : DerivedCategory.Qh ⋙ DK ≅ K.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : F ⋙ G ≅ H ⋙ K) : DF ⋙ DG ≅ DH ⋙ DK :=
  let eh : F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ≅
      H.mapHomotopyCategory (.up ℤ) ⋙ K.mapHomotopyCategory (.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso (F := F) (G := G) (H := H ⋙ K) e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (F := H) (G := K) (H := H ⋙ K)
        (Iso.refl _) (.up ℤ)).symm
  Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso D₀ (.up ℤ))
    (DerivedCategory.Qh ⋙ (DF ⋙ DG)) (DerivedCategory.Qh ⋙ (DH ⋙ DK))
    (DF ⋙ DG) (DH ⋙ DK)
    (composeFactors F G DF DG eF eG ≪≫ Functor.isoWhiskerRight eh DerivedCategory.Qh ≪≫
      (composeFactors H K DH DK eH eK).symm)

/-- Canonical derived interchange of scalar restriction and slice restriction.
Source: Stacks 03DA, 03DH, 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
def derivedRestrictionOverGeneral {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C) :
    (normalization J).right q ⋙ overDerived J R U ≅
      overDerived J T U ⋙ sliceDerived J q U :=
  localizeSquare (SheafOfModules.SuccessiveDerivedQuotient.restriction.{r, r, r} q)
    (SheafOfModules.overFunctor.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) U)
    (SheafOfModules.overFunctor.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J T) U)
    (sliceScalars J q U)
    ((normalization J).right q) (overDerived J R U) (overDerived J T U)
    (sliceDerived J q U) ((normalization J).right_factors q)
    (overFactors J R U) (overFactors J T U) (sliceFactorsh J q U)
    (restrictionOverIso J q U)

/-- Actual quotient scalar restriction on the slice. Source: Stacks 03DA
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev quotientRestriction (U : C) (m n : ℕ) (h : m ≤ n) :=
  sliceScalars J (quotient l E J m n h) U

/-- Actual quotient scalar restriction on derived slice categories. Source: Stacks 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev quotientDerived (U : C) (m n : ℕ) (h : m ≤ n) :=
  sliceDerived J (quotient l E J m n h) U

/-- Complex localization comparison for quotient restriction. Source: Stacks 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
def quotientFactors (U : C) (m n : ℕ) (h : m ≤ n) :=
  Functor.mapDerivedCategoryFactors.{w, w} (quotientRestriction l E J U m n h)

/-- Homotopy localization comparison for quotient restriction. Source: Stacks 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
def quotientFactorsh (U : C) (m n : ℕ) (h : m ≤ n) :=
  Functor.mapDerivedCategoryFactorsh.{w, w} (quotientRestriction l E J U m n h)

/-- The canonical interchange for the actual quotient map. Source: Stacks 03DH, 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
def derivedRestrictionOverIso (U : C) (m n : ℕ) (h : m ≤ n) :=
  derivedRestrictionOverGeneral J (quotient l E J m n h) U

/-- The actual quotient-induced transition after slice restriction, with its target
identified by the canonical restriction interchange. Source: Stacks 07A6, 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
def restrictedTransition (L : Modules J (completion l E J)) (U : C)
    (m n : ℕ) (h : m ≤ n) :
    (overDerived J (coefficient l E J n) U).obj (reduction l E J L n) ⟶
      (quotientDerived l E J U m n h).obj
        ((overDerived J (coefficient l E J m) U).obj (reduction l E J L m)) :=
  (overDerived J (coefficient l E J n) U).map (transition l E J L m n h) ≫
    (derivedRestrictionOverIso l E J U m n h).hom.app (reduction l E J L m)

/-- The original restricted module category. Source: Stacks 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
abbrev SliceModules (R : Sheaf J CommRingCat.{r}) (U : C) :=
  SheafOfModules.{r} ((SheafOfModules.derivedChangeRingIndependentCoefficients J R).over U)

/-- The derived reduction restricted to the specified covering object.
Source: Stacks 06YY, 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
def localReduction (L : Modules J (completion l E J)) (U : C) (n : ℕ) :
    DerivedCategory (SliceModules J (coefficient l E J n) U) :=
  (overDerived J (coefficient l E J n) U).obj (reduction l E J L n)

/-- The single reduced matrix complex on the specified covering object.
Source: Stacks 093J, 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
def localMatrix (U : C) {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :
    CochainComplex (SliceModules J (coefficient l E J n) U) ℤ :=
  (overComplex J (coefficient l E J n) U).obj (reducedComplex l E J d n)

/-- Localization of that very matrix complex. Source: Stacks 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
def localMatrixObject (U : C) {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :
    DerivedCategory (SliceModules J (coefficient l E J n) U) :=
  DerivedCategory.Q.obj (localMatrix l E J U d n)

/-- The finite free constant module with its explicit level coefficient type.
Source: Stacks 093J
(blueprint: def-sp-integral-matrix-model-data). -/
def freeAtLevel (n a : ℕ) : Modules J (coefficient l E J n) :=
  (constantAtLevel l E J n).obj
    (ModuleCat.of (Residues l E n) (Fin a → Residues l E n))

/-- A basis identification for one term of the specified matrix complex.
Source: Stacks 093J, 06YQ
(blueprint: def-sp-integral-matrix-model-data). -/
def TermBasis {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (n : ℕ) (i : ℤ) (rank : ℕ) :=
  @Iso (Modules J (coefficient l E J n)) _
    ((reducedComplex l E J d n).X i) (freeAtLevel l E J n rank)

/-- The differential is the entrywise reduction of the integral scalar matrix.
Source: Stacks 093J, 06YQ
(blueprint: def-sp-integral-matrix-model-data). -/
def MatrixDifferential {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (left : ∀ n : ℕ, TermBasis l E J d n (-1) a)
    (right : ∀ n : ℕ, TermBasis l E J d n 0 b) : Prop :=
  ∀ (n : ℕ) (V : Cᵒᵖ) (x : Fin a → Residues l E n),
    ((left n).inv ≫ (reducedComplex l E J d n).d (-1) 0 ≫ (right n).hom).val.app V
      (vectorAtLevel l E J n a V x) =
        vectorAtLevel l E J n b V (Matrix.toLin' (reduced l E d n) x)

/-- Only the two stated free degrees occur. Source: Stacks 06YQ
(blueprint: def-sp-integral-matrix-model-data). -/
def MatrixSupport {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) : Prop :=
  ∀ (n : ℕ) (i : ℤ), i ≠ -1 → i ≠ 0 →
    @IsZero (Modules J (coefficient l E J n)) _ ((reducedComplex l E J d n).X i)

/-- Type of the actual termwise quotient chain map. Source: Stacks 07A6, 093J
(blueprint: def-sp-integral-matrix-model-data). -/
def MatrixQuotient (U : C) {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (m n : ℕ) (h : m ≤ n) :=
  @Quiver.Hom (CochainComplex (SliceModules J (coefficient l E J n) U) ℤ) _
    (localMatrix l E J U d n)
    (((quotientRestriction l E J U m n h).mapHomologicalComplex (.up ℤ)).obj
      (localMatrix l E J U d m))

/-- Scalar restriction on a slice leaves the underlying sections unchanged.
Source: Stacks 03DA, 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
def scalarRestrictionSection {R T : Sheaf J CommRingCat.{r}} (q : R ⟶ T) (U : C)
    (M : SheafOfModules.{r}
      ((SheafOfModules.derivedChangeRingIndependentCoefficients J T).over U))
    (V : (Over U)ᵒᵖ) :
    ((sliceScalars J q U).obj M).val.obj V → M.val.obj V :=
  id

/-- The underlying section map of the quotient chain map in a specified degree.
Source: Stacks 03DA, 03DH
(blueprint: def-sp-integral-matrix-model-data). -/
def matrixQuotientApply (U : C) {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) (Scalars l E)) (m n : ℕ) (h : m ≤ n)
    (f : MatrixQuotient l E J U d m n h) (i : ℤ) (V : (Over U)ᵒᵖ) :
    ((localMatrix l E J U d n).X i).val.obj V →
      ((localMatrix l E J U d m).X i).val.obj V :=
  fun x ↦ scalarRestrictionSection J (quotient l E J m n h) U
    ((localMatrix l E J U d m).X i) V ((f.f i).val.app V x)

/-- The quotient in a specified free degree is entrywise scalar reduction.
Source: Stacks 07A6, 093J
(blueprint: def-sp-integral-matrix-model-data). -/
def MatrixQuotientDegree (U : C) {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) (Scalars l E)) (i : ℤ) (rank : ℕ)
    (basis : ∀ n : ℕ, TermBasis l E J d n i rank)
    (termwise : ∀ (m n : ℕ) (h : m ≤ n), MatrixQuotient l E J U d m n h) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n) (V : (Over U)ᵒᵖ) (x : Fin rank → Residues l E n),
    (basis m).hom.val.app (op V.unop.left)
      (matrixQuotientApply l E J U d m n h (termwise m n h) i V
        ((basis n).inv.val.app (op V.unop.left)
          (vectorAtLevel l E J n rank (op V.unop.left) x))) =
      vectorAtLevel l E J m rank (op V.unop.left)
        (fun j ↦ scalarReduction l E m n h (x j))

/-- The actual derived quotient transition is the localization of the termwise quotient.
Source: Stacks 07A6, 08JB
(blueprint: def-sp-integral-matrix-model-data). -/
def MatrixTransitionSquare (L : Modules J (completion l E J)) (U : C) {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) (Scalars l E))
    (comparison : ∀ n : ℕ, localReduction l E J L U n ≅ localMatrixObject l E J U d n)
    (termwise : ∀ (m n : ℕ) (h : m ≤ n), MatrixQuotient l E J U d m n h) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n),
    restrictedTransition l E J L U m n h ≫
      (quotientDerived l E J U m n h).map (comparison m).hom ≫
      (quotientFactors l E J U m n h).hom.app (localMatrix l E J U d m) =
    (comparison n).hom ≫ DerivedCategory.Q.map (termwise m n h)

/-- The simultaneous model and its quotient squares. Each comparison is an isomorphism
in the localized coefficient derived category. The derived interchange is the localization of the
identity on sections, so the quotient square uses the actual exact restrictions.
The termwise quotient is fixed on all constant vector generators in both free degrees.
Source: Stacks 06YY, 07A6, 093J; the node proof, steps 1--4
(blueprint: def-sp-integral-matrix-model-data). -/
structure SimultaneousModels (L : Modules J (completion l E J)) (U : C)
    {a b : ℕ} (d : Matrix (Fin b) (Fin a) (Scalars l E)) where
  comparison : ∀ n : ℕ,
    localReduction l E J L U n ≅
      localMatrixObject l E J U d n
  left : ∀ n : ℕ, TermBasis l E J d n (-1) a
  right : ∀ n : ℕ, TermBasis l E J d n 0 b
  differential : MatrixDifferential l E J d left right
  support : MatrixSupport l E J d
  termwise : ∀ (m n : ℕ) (h : m ≤ n), MatrixQuotient l E J U d m n h
  quotient_left : MatrixQuotientDegree l E J U d (-1) a left termwise
  quotient_right : MatrixQuotientDegree l E J U d 0 b right termwise
  transition_square : MatrixTransitionSquare l E J L U d comparison termwise


end IntegralMatrix
end AlgebraicGeometry.ProEtale
```

The original module now begins with `public import Sheaf.Paper.IntegralMatrixModelData`.
All its previous public imports are available transitively from the data module.
The moved declarations have their blueprint tags attached to the new data node.
Proof imports unused by the data definitions are removed; the two proof obligations
carry their mathematical dependencies in their nodes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralLocalModelFiniteMatrixReduction | M9 | Publicly reexports unchanged data; proves theorem from two independent steps. |
| Sheaf.Paper.IntegralMatrixLocalResolution | M9, new | Imports the data and states the supplied-resolution comparison. |
| Sheaf.Paper.IntegralMatrixCohomology | M9, new | Imports the data and states the matrix homology calculation. |

`tools/downstream.py Sheaf.Paper.IntegralLocalModelFiniteMatrixReduction` reports zero
Lean downstream modules. An independent scan of both source roots confirms that no
other current Lean file imports the item. DAG parents
`lem-sp-stratified-reduction-postnikov-comparison` and
`det-sp-reduction-tower-normalized` still need the theorem and are retained.
No consumer adaptation is required. The five Challenge declarations are untouched;
the definitions they transitively use are mathematically unchanged.

## Status

landed 20261025T163916-L-898532 2026-10-25 (merge of deliver/M9/Sheaf.Paper.IntegralLocalModelFiniteMatrixReduction)
