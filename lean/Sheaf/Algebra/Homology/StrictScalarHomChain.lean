/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.LinearAlgebra.TensorProduct.Defs

/-! # Strict scalar identification of unbounded product Hom complexes

Source: Stacks Project, sites-modules.tex, Tags 03CZ, 03CY and 03EL;
sites-cohomology.tex, Tag 0A8X. The extension to the strict chain square and
coefficient compatibility is the agent argument recorded in the DAG.
(blueprint: lem-sfb-hom-scalar-chain-identification).

The structures below package the normalized maps and their equations. The only
postponed assertion is their simultaneous existence. All section evaluations
use the chosen product projections and the identity object of the slice.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace SheafOfModules.StrictScalarHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}]

/-- Transparent notation for the existing unbounded module complexes.
Source: Stacks 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
abbrev Complex (R : Sheaf J CommRingCat.{max c v u}) :=
  CochainComplex (ringedSiteModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ

/-- Termwise Mathlib restriction of scalars.
Source: Stacks 03CZ (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def restriction {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Complex.{c, v, u} S ⥤ Complex.{c, v, u} R :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
    (.up ℤ)

/-- The fixed R-module S, obtained by restricting the unit S-module.
Source: Stacks 03CZ (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def scalarModule {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))

/-- The ordinary R-linear tensor S tensor A, applied termwise, using the existing tensor.
Source: Stacks 03EK (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def tensor {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Complex.{c, v, u} R ⥤ Complex.{c, v, u} R :=
  (tensorLeft (scalarModule.{c, v, u} φ)).mapHomologicalComplex (.up ℤ)

/-- The sheafification-unit image of s tensor x in the R-linear tensor.
Source: Stacks 03CY, 03EK (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def tensorSection {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V) (x : (A.X n).val.obj V) :
    (((tensor.{c, v, u} φ).obj A).X n).val.obj V :=
  (tensorObjIsoSheafification (scalarModule.{c, v, u} φ) (A.X n)).inv.val.app V
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      ((scalarModule.{c, v, u} φ).val ⊗ (A.X n).val)).app V (s ⊗ₜ[R.obj.obj V] x))

/-- Actual local evaluation, using the chosen product projection and slice identity.
Source: Stacks 0A8X; the convention of def-coef-hom-representative-evaluation
(blueprint: lem-sfb-hom-scalar-chain-identification). -/
def evaluate {R : Sheaf J CommRingCat.{max c v u}} (P N : Complex.{c, v, u} R)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (g : ((homComplex (R := R) P N).X n).val.obj V)
    (x : (P.X i).val.obj V) : (N.X k).val.obj V :=
  (((homComplexπ (R := R) P N n i k h).val.app V g).app
    (op (Over.mk (𝟙 V.unop)))).hom x

/-- The existing componentwise action of the actual product Hom bifunctor.
Source: Stacks 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def homMap {R : Sheaf J CommRingCat.{max c v u}}
    {P P' N N' : Complex.{c, v, u} R} (a : P' ⟶ P) (b : N ⟶ N') :
    homComplex (R := R) P N ⟶ homComplex (R := R) P' N' :=
  (homComplexFunctor.map a.op).app N ≫ (homComplexFunctor.obj (op P')).map b

/-- Ordinary scalar extension with its object and map functions pinned to the existing
sheafification construction. Additivity permits termwise application.
Source: Stacks 03CZ, 03CY (blueprint: lem-sfb-hom-scalar-chain-identification). -/
structure Extension {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) where
  /-- The ordinary module functor. -/
  functor : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  /-- Exactly the sheafified ordinary scalar extension on objects. -/
  obj_eq : ∀ M, functor.obj M = changeOfRingsOfUniverses φ M
  /-- Exactly the sheafified map id tensor f on morphisms. -/
  map_eq : ∀ {M N} (f : M ⟶ N), functor.map f =
    eqToHom (obj_eq M) ≫ changeOfRingsHomOfUniverses φ M f ≫ eqToHom (obj_eq N).symm
  /-- Ordinary extension is additive. -/
  [additive : functor.Additive]

attribute [instance] Extension.additive

/-- The termwise functor associated to ordinary extension.
Source: Stacks 03CZ, 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def Extension.complex {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : Complex.{c, v, u} R ⥤ Complex.{c, v, u} S :=
  E.functor.mapHomologicalComplex (.up ℤ)

/-- Pure sections transported by the explicit object equality, with no arbitrary map.
Source: Stacks 03CY (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def Extension.section {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V) :
    ((E.complex.obj A).X n).val.obj V :=
  (eqToHom (E.obj_eq (A.X n)).symm).val.app V
    (scalarExtensionSection φ (A.X n) V s x)

/-- The normalization predicate for the S-linear evaluation map.
Source: Stacks 03CZ, 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def SigmaFormula {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : E.complex.obj A ⟶ N)
    (σ : E.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (E.complex.obj P) N) : Prop :=
  ∀ (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ) (s t : S.obj.obj V)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V),
    evaluate.{c, v, u} (E.complex.obj P) N n i k h V
        ((σ.f n).val.app V (E.section (homComplex (R := R) P A) n V s f))
        (E.section P i V t x) =
      (s * t) • (q.f k).val.app V (E.section A k V 1 (evaluate.{c, v, u} P A n i k h V f x))

/-- All normalized chain maps for one coefficient morphism, with their strict square
and input naturality. No boundedness, flatness, or resolution is part of this data.
Source: Stacks 03CZ, 03CY and 0A8X
(blueprint: lem-sfb-hom-scalar-chain-identification). -/
structure Data {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) where
  /-- The actual ordinary extension. -/
  extension : Extension.{c, v, u} φ
  /-- The identity-on-generators natural chain isomorphism. -/
  nu : tensor.{c, v, u} φ ≅ extension.complex ⋙ restriction.{c, v, u} φ
  /-- Its generator normalization in every degree and over every object. -/
  nu_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((nu.app A).hom.f n).val.app V) (tensorSection.{c, v, u} φ A n V s x) =
      extension.section A n V s x
  /-- The actual product-Hom chain isomorphism. -/
  theta : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    (restriction.{c, v, u} φ).obj (homComplex (R := S) (extension.complex.obj P) N) ≅
      homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)
  /-- Its formula uses the actual local product projection. -/
  theta_evaluate : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (g : ((homComplex (R := S) (extension.complex.obj P) N).X n).val.obj V)
    (x : (P.X i).val.obj V),
    evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n i k h V
        ((((theta P N).hom.f n).val.app V) g) x =
      evaluate.{c, v, u} (extension.complex.obj P) N n i k h V g (extension.section P i V 1 x)
  /-- The R-linear scalar-Hom comparison, with no product-preservation assertion. -/
  alpha : ∀ (P A : Complex.{c, v, u} R),
    (tensor.{c, v, u} φ).obj (homComplex (R := R) P A) ⟶
      homComplex (R := R) P ((tensor.{c, v, u} φ).obj A)
  /-- Alpha is s tensor f evaluated at x equals s tensor f(x). -/
  alpha_evaluate : ∀ (P A : Complex.{c, v, u} R) (n i k : ℤ) (h : i + n = k)
    (V : Cᵒᵖ) (s : S.obj.obj V)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V),
    evaluate.{c, v, u} P ((tensor.{c, v, u} φ).obj A) n i k h V
        (((alpha P A).f n).val.app V
          (tensorSection.{c, v, u} φ (homComplex (R := R) P A) n V s f)) x =
      tensorSection.{c, v, u} φ A k V s (evaluate.{c, v, u} P A n i k h V f x)
  /-- The S-linear scalar evaluation chain map for every q. -/
  sigma : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (_q : extension.complex.obj A ⟶ N),
    extension.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (extension.complex.obj P) N
  /-- The normalized formula on both sets of local generators. -/
  sigma_formula : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : extension.complex.obj A ⟶ N),
    SigmaFormula.{c, v, u} extension P A N q (sigma P A N q)
  /-- Uniqueness among all S-linear chain maps with that formula. -/
  sigma_unique : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : extension.complex.obj A ⟶ N)
    (s : extension.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (extension.complex.obj P) N),
    SigmaFormula.{c, v, u} extension P A N q s → s = sigma P A N q
  /-- The asserted equality holds in the category of complexes before localization. -/
  square : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : extension.complex.obj A ⟶ N),
    (nu.app (homComplex (R := R) P A)).hom ≫
        (restriction.{c, v, u} φ).map (sigma P A N q) ≫ (theta P N).hom =
      alpha P A ≫ homMap.{c, v, u} (𝟙 P) (nu.app A).hom ≫
        homMap.{c, v, u} (𝟙 P) ((restriction.{c, v, u} φ).map q)
  /-- Theta is contravariant in P and covariant in N. -/
  theta_natural : ∀ (P P' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (a : P' ⟶ P) (w : N ⟶ N'),
    (restriction.{c, v, u} φ).map (homMap.{c, v, u} (extension.complex.map a) w) ≫
        (theta P' N').hom =
      (theta P N).hom ≫ homMap.{c, v, u} a ((restriction.{c, v, u} φ).map w)
  /-- Alpha commutes with chain maps of both inputs. -/
  alpha_natural : ∀ (P P' A A' : Complex.{c, v, u} R) (a : P' ⟶ P) (b : A ⟶ A'),
    (tensor.{c, v, u} φ).map (homMap.{c, v, u} a b) ≫ alpha P' A' =
      alpha P A ≫ homMap.{c, v, u} a ((tensor.{c, v, u} φ).map b)
  /-- Sigma commutes with compatible changes of P, A, N and q. -/
  sigma_natural : ∀ (P P' A A' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (q : extension.complex.obj A ⟶ N) (q' : extension.complex.obj A' ⟶ N')
    (a : P' ⟶ P) (b : A ⟶ A') (w : N ⟶ N'),
    extension.complex.map b ≫ q' = q ≫ w →
      extension.complex.map (homMap.{c, v, u} a b) ≫ sigma P' A' N' q' =
        sigma P A N q ≫ homMap.{c, v, u} (extension.complex.map a) w

/-- The canonical Hom comparison for a coefficient change is sigma with q the identity.
Source: Stacks 03CZ, 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def Data.homComparison {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : Data.{c, v, u} φ) (P A : Complex.{c, v, u} R) :
    D.extension.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (D.extension.complex.obj P) (D.extension.complex.obj A) :=
  D.sigma P A (D.extension.complex.obj A) (𝟙 _)

/-- The canonical extension identification and restriction mate for a commuting
square of coefficient sheaves, both pinned by local tensor generators.
Source: Stacks 03CZ, 03CY (blueprint: lem-sfb-hom-scalar-chain-identification). -/
structure CoefficientSquare
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    (D : Data.{c, v, u} φ) (Da : Data.{c, v, u} a) (Db : Data.{c, v, u} b)
    (D' : Data.{c, v, u} φ') where
  /-- Identify the two iterated ordinary extensions. -/
  extensionIso : D.extension.complex ⋙ Db.extension.complex ≅
    Da.extension.complex ⋙ D'.extension.complex
  /-- The identification multiplies the scalars in the common S'-extension. -/
  extensionIso_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (t : S'.obj.obj V) (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((extensionIso.app A).hom.f n).val.app V)
        (Db.extension.section (D.extension.complex.obj A) n V t
          (D.extension.section A n V s x)) =
      D'.extension.section (Da.extension.complex.obj A) n V (t * b.hom.app V s)
        (Da.extension.section A n V 1 x)
  /-- Extension of an R-restricted S-complex maps to the R'-restricted S'-extension. -/
  restrictionMate : restriction.{c, v, u} φ ⋙ Da.extension.complex ⟶
    Db.extension.complex ⋙ restriction.{c, v, u} φ'
  /-- The mate sends r' tensor z to phi'(r') tensor z. -/
  restrictionMate_pure : ∀ (N : Complex.{c, v, u} S) (n : ℤ) (V : Cᵒᵖ)
    (r : R'.obj.obj V) (z : (N.X n).val.obj V),
    (((restrictionMate.app N).f n).val.app V)
        (Da.extension.section ((restriction.{c, v, u} φ).obj N) n V r z) =
      Db.extension.section N n V (φ'.hom.app V r) z

/-- The canonical coefficient map on S tensor A, transported through the normalized
nu maps and the generator-normalized mate. It need not be an isomorphism.
Source: Stacks 03CZ, 03EK (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def CoefficientSquare.tensorComparison
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : Data.{c, v, u} φ} {Da : Data.{c, v, u} a} {Db : Data.{c, v, u} b} {D' : Data.{c, v, u} φ'}
    (Q : CoefficientSquare.{c, v, u} D Da Db D') (A : Complex.{c, v, u} R) :
    Da.extension.complex.obj ((tensor.{c, v, u} φ).obj A) ⟶
      (tensor.{c, v, u} φ').obj (Da.extension.complex.obj A) :=
  Da.extension.complex.map (D.nu.app A).hom ≫
    Q.restrictionMate.app (D.extension.complex.obj A) ≫
    (restriction.{c, v, u} φ').map (Q.extensionIso.app A).hom ≫
    (D'.nu.app (Da.extension.complex.obj A)).inv

/-- Coefficient compatibility of all four normalized chain maps. These are equations
of actual chain maps for a general commuting square, without a flatness assumption.
Source: Stacks 03CZ and 0A8X, the DAG's generator calculation
(blueprint: lem-sfb-hom-scalar-chain-identification). -/
structure CoefficientCompatibility
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : Data.{c, v, u} φ} {Da : Data.{c, v, u} a} {Db : Data.{c, v, u} b} {D' : Data.{c, v, u} φ'}
    (Q : CoefficientSquare.{c, v, u} D Da Db D') : Prop where
  /-- The tensor coefficient map is the expected map on all local generators. -/
  tensor_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R'.obj.obj V) (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((Q.tensorComparison A).f n).val.app V)
        (Da.extension.section ((tensor.{c, v, u} φ).obj A) n V r
          (tensorSection.{c, v, u} φ A n V s x)) =
      tensorSection.{c, v, u} φ' (Da.extension.complex.obj A) n V
        (φ'.hom.app V r * b.hom.app V s) (Da.extension.section A n V 1 x)
  /-- Nu commutes with the canonical coefficient maps. -/
  nu : ∀ (A : Complex.{c, v, u} R),
    Q.tensorComparison A ≫ (D'.nu.app (Da.extension.complex.obj A)).hom =
      Da.extension.complex.map (D.nu.app A).hom ≫
        Q.restrictionMate.app (D.extension.complex.obj A) ≫
        (restriction.{c, v, u} φ').map (Q.extensionIso.app A).hom
  /-- Theta commutes with the canonical Hom comparisons and the restriction mate. -/
  theta : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    Da.extension.complex.map (D.theta P N).hom ≫
        Da.homComparison P ((restriction.{c, v, u} φ).obj N) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.restrictionMate.app N) =
      Q.restrictionMate.app (homComplex (R := S) (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (Db.homComparison (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (homMap.{c, v, u} (Q.extensionIso.app P).inv
          (𝟙 (Db.extension.complex.obj N))) ≫
        (D'.theta (Da.extension.complex.obj P) (Db.extension.complex.obj N)).hom
  /-- Alpha commutes with coefficient extension and its canonical Hom comparison. -/
  alpha : ∀ (P A : Complex.{c, v, u} R),
    Da.extension.complex.map (D.alpha P A) ≫ Da.homComparison P ((tensor.{c, v, u} φ).obj A) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.tensorComparison A) =
      Q.tensorComparison (homComplex (R := R) P A) ≫
        (tensor.{c, v, u} φ').map (Da.homComparison P A) ≫
        D'.alpha (Da.extension.complex.obj P) (Da.extension.complex.obj A)
  /-- Sigma commutes with coefficient extension for every compatible q', including
  arbitrary targets and compatible semilinear target maps, not only Eb(N). -/
  sigma : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S) (N' : Complex.{c, v, u} S')
    (q : D.extension.complex.obj A ⟶ N)
    (w : Db.extension.complex.obj N ⟶ N')
    (q' : D'.extension.complex.obj (Da.extension.complex.obj A) ⟶ N'),
    (Q.extensionIso.app A).hom ≫ q' = Db.extension.complex.map q ≫ w →
      Db.extension.complex.map (D.sigma P A N q) ≫
          Db.homComparison (D.extension.complex.obj P) N ≫
          homMap.{c, v, u} (Q.extensionIso.app P).inv w =
        (Q.extensionIso.app (homComplex (R := R) P A)).hom ≫
          D'.extension.complex.map (Da.homComparison P A) ≫
          D'.sigma (Da.extension.complex.obj P) (Da.extension.complex.obj A) N' q'

/-- Strict scalar-Hom identifications, the uniquely normalized evaluation square,
and compatibility with all input and coefficient changes.
Source: Stacks Project, sites-modules.tex, Tags 03CZ, 03CY, 03EL; sites-cohomology.tex,
Tag 0A8X. The unbounded chain and coefficient assertions are the explicit agent
extension recorded in the node (blueprint: lem-sfb-hom-scalar-chain-identification).

Proof: (1) Restrict scalar actions sectionwise on every slice. Localized tensor
restriction (lem-sfb-localized-site-tensor-restriction) preserves the images of
presheaf tensor generators. (2) Apply the ordinary scalar-Hom bijection
(lem-weil-pbc-scalar-extension-hom) on every slice: g maps to x ↦ g(1 tensor x),
and h maps to s tensor x ↦ s h(x). These formulas commute with restrictions;
module sheafification (def-weil-presheaf-modules-sheafification) extends them
uniquely. (3) The identity on the tensor presheaf identifies the two R-module
sheafifications, giving nu, naturally and termwise. (4) Apply the slice bijections
to every factor of the actual product Hom in each degree, giving theta and its
inverse, without commuting extension with products. (5) The differential is
d_N g - (-1)^n g d_P (def-pur-hom-complex); evaluation on 1 tensor x commutes with
both terms, so theta is a chain isomorphism for arbitrary unbounded complexes.
(6) The balanced rule (s,f,x) ↦ s tensor f(x), product projections, and
sheafification give alpha. Its differential is s tensor (df)(x).
(7) Apply the slice adjunction first to x ↦ q(1 tensor f(x)), then to the
Hom section f. This gives sigma(s tensor f)(t tensor x) = st q(1 tensor f(x)).
(8) The chain equation for q and the same signed differential prove that sigma
is a chain map. Uniqueness follows first in every Hom coordinate from the tensor
universal property in EP, then from sheafification in E Hom(P,A).
(9) Evaluate both sides of the strict square on s tensor f, then in coordinate i
at x: both are s q(1 tensor f(x)), using S-linearity of q. The two tensor
universal properties and sheafification prove equality of chain maps, with the
actual product projections and identity-of-slice evaluation convention of
def-coef-hom-representative-evaluation. No localization occurs.
(10) Substitute chain maps contravariantly in P and covariantly in A,N; the
compatibility E(b);q' = q;w gives sigma naturality. The nu, theta and alpha
naturality formulas follow by the same substitution and uniqueness.
(11) For a commuting coefficient square, identify the iterated extensions by
multiplying scalars and inserting 1 in the inverse. The restriction mate sends
r' tensor z to phi'(r') tensor z. The tensor comparison and its pure formula
follow through nu. The coefficient theta equation evaluates to the same image
of g(1 tensor x), the alpha equation to the same extended tensor f(x), and the
sigma equation to b(s)b(t) tensor q(1 tensor f(x)), followed by w when present.
Linearity and the two sheafification universal properties prove the displayed
chain equations. These equations hold for every coefficient square and every
compatible q'; applying them successively includes towers and identity changes.
There is no flatness, boundedness, or K-injectivity hypothesis. -/
theorem exists_scalarHomChainIdentification :
    ∃ D : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S), Data.{c, v, u} φ,
      ∀ (R S R' S' : Sheaf J CommRingCat.{max c v u})
        (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S'),
        φ ≫ b = a ≫ φ' →
          ∃ Q : CoefficientSquare.{c, v, u} (D R S φ) (D R R' a) (D S S' b) (D R' S' φ'),
            CoefficientCompatibility.{c, v, u} Q := by
  sorry

end SheafOfModules.StrictScalarHom
