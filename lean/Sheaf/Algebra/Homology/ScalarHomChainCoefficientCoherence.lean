/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction
public import Sheaf.Algebra.Homology.ScalarHomChainEvaluation
import all Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction
import all Sheaf.Algebra.Homology.StrictScalarHomChain
import Sheaf.Paper.ScalarExtensionBinaryCoherence
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Coefficient coherence of normalized scalar Hom chain maps

Source: Stacks Project, sites-modules.tex, Tags 03CY and 03CZ;
sites-cohomology.tex, Tag 0A8X. The explicit coefficient calculations are recorded
in the node's proof (blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence).

The input contains only the normalized maps of the two dependency statements.
The structures below specify the coefficient maps, their four equations, and
identity and composition coherence, on the actual unbounded product Hom complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace SheafOfModules.StrictScalarHom

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection tensorSection evaluate homMap
  homComplex homComplexπ tensorObj homComplexFunctor Extension.complex

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}]

/-- Packaging of the supplied normalized maps, without any coefficient equations.
Source: Stacks 03CY, 03CZ and 0A8X
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure NormalizedCoefficientMaps {R S : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) where
  /-- The already defined sheafified ordinary extension. -/
  extension : Extension.{c, v, u} φ
  /-- Exactly the dependency's normalized nu and theta chain isomorphisms. -/
  chains : ScalarHomAdjunctionChains.{c, v, u} extension
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

/-- The canonical Hom comparison for a coefficient change is sigma with q the identity.
Source: Stacks 03CZ, 0A8X (blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientMaps.homComparison {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedCoefficientMaps.{c, v, u} φ) (P A : Complex.{c, v, u} R) :
    D.extension.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (D.extension.complex.obj P) (D.extension.complex.obj A) :=
  D.sigma P A (D.extension.complex.obj A) (𝟙 _)

attribute [local irreducible] NormalizedCoefficientMaps.homComparison

/-- The canonical extension identification and restriction mate for a commuting
square of coefficient sheaves, both pinned by local tensor generators.
Source: Stacks 03CZ, 03CY (blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure NormalizedCoefficientSquare
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    (D : NormalizedCoefficientMaps.{c, v, u} φ)
    (Da : NormalizedCoefficientMaps.{c, v, u} a)
    (Db : NormalizedCoefficientMaps.{c, v, u} b)
    (D' : NormalizedCoefficientMaps.{c, v, u} φ') where
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
  /-- The inverse multiplies the R'-scalar through phi' and inserts a unit. -/
  extensionIso_inv_pure : ∀ (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S'.obj.obj V) (r : R'.obj.obj V) (x : (X.X n).val.obj V),
    (((extensionIso.app X).inv.f n).val.app V)
        (D'.extension.section (Da.extension.complex.obj X) n V s
          (Da.extension.section X n V r x)) =
      Db.extension.section (D.extension.complex.obj X) n V (s * φ'.hom.app V r)
        (D.extension.section X n V 1 x)
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
Source: Stacks 03CZ, 03EK (blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientSquare.tensorComparison
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') (A : Complex.{c, v, u} R) :
    Da.extension.complex.obj ((tensor.{c, v, u} φ).obj A) ⟶
      (tensor.{c, v, u} φ').obj (Da.extension.complex.obj A) :=
  Da.extension.complex.map (D.chains.nu.app A).hom ≫
    Q.restrictionMate.app (D.extension.complex.obj A) ≫
    (restriction.{c, v, u} φ').map (Q.extensionIso.app A).hom ≫
    (D'.chains.nu.app (Da.extension.complex.obj A)).inv

attribute [local irreducible] NormalizedCoefficientSquare.tensorComparison

/-- The tensor coefficient map is the expected map on all local generators.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.tensor_pure_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R'.obj.obj V) (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((Q.tensorComparison A).f n).val.app V)
        (Da.extension.section ((tensor.{c, v, u} φ).obj A) n V r
          (tensorSection.{c, v, u} φ A n V s x)) =
      tensorSection.{c, v, u} φ' (Da.extension.complex.obj A) n V
        (φ'.hom.app V r * b.hom.app V s) (Da.extension.section A n V 1 x)

/-- Nu commutes with the canonical coefficient maps.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.nu_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (A : Complex.{c, v, u} R),
    Q.tensorComparison A ≫ (D'.chains.nu.app (Da.extension.complex.obj A)).hom =
      Da.extension.complex.map (D.chains.nu.app A).hom ≫
        Q.restrictionMate.app (D.extension.complex.obj A) ≫
        (restriction.{c, v, u} φ').map (Q.extensionIso.app A).hom

/-- Theta commutes with the canonical Hom comparisons and the restriction mate.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.theta_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    Da.extension.complex.map (D.chains.theta P N).hom ≫
        Da.homComparison P ((restriction.{c, v, u} φ).obj N) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.restrictionMate.app N) =
      Q.restrictionMate.app (homComplex (R := S) (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (Db.homComparison (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (homMap.{c, v, u} (Q.extensionIso.app P).inv
          (𝟙 (Db.extension.complex.obj N))) ≫
        (D'.chains.theta (Da.extension.complex.obj P) (Db.extension.complex.obj N)).hom

/-- Alpha commutes with coefficient extension and its canonical Hom comparison.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.alpha_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (P A : Complex.{c, v, u} R),
    Da.extension.complex.map (D.alpha P A) ≫ Da.homComparison P ((tensor.{c, v, u} φ).obj A) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.tensorComparison A) =
      Q.tensorComparison (homComplex (R := R) P A) ≫
        (tensor.{c, v, u} φ').map (Da.homComparison P A) ≫
        D'.alpha (Da.extension.complex.obj P) (Da.extension.complex.obj A)

/-- Sigma commutes with coefficient extension for every compatible q', including
  arbitrary targets and compatible semilinear target maps, not only Eb(N).
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.sigma_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S) (N' : Complex.{c, v, u} S')
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

/-- Coefficient compatibility of all four normalized chain maps. These are equations
of actual chain maps for a general commuting square, without a flatness assumption.
Source: Stacks 03CZ and 0A8X, the DAG's generator calculation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure NormalizedCoefficientCompatibility
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop where
  /-- The tensor coefficient map is the expected map on all local generators. -/
  tensor_pure : NormalizedCoefficientCompatibility.tensor_pure_law Q
  /-- Nu commutes with the canonical coefficient maps. -/
  nu : NormalizedCoefficientCompatibility.nu_law Q
  /-- Theta commutes with the canonical Hom comparisons and the restriction mate. -/
  theta : NormalizedCoefficientCompatibility.theta_law Q
  /-- Alpha commutes with coefficient extension and its canonical Hom comparison. -/
  alpha : NormalizedCoefficientCompatibility.alpha_law Q
  /-- Sigma commutes with coefficient extension for every compatible q', including
  arbitrary targets and compatible semilinear target maps, not only Eb(N). -/
  sigma : NormalizedCoefficientCompatibility.sigma_law Q

/-- Naturality of the tensor comparison defined through nu, kappa and mu.
Source: Stacks 03CY and 03CZ
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientSquare.TensorNatural
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (X Y : Complex.{c, v, u} R) (f : X ⟶ Y),
    Da.extension.complex.map ((tensor.{c, v, u} φ).map f) ≫ Q.tensorComparison Y =
      Q.tensorComparison X ≫ (tensor.{c, v, u} φ').map (Da.extension.complex.map f)

/-- A family of normalized iterated-extension associators and unit identifications.
Source: Stacks 03CY and 03CZ, node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientExtensionAssociators
    (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ) where
  /-- Extension along an identity ring map is canonically the identity. -/
  unit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    (F R R (𝟙 R)).extension.complex ≅ 𝟭 (Complex.{c, v, u} R)
  /-- Multiplication gives the forward unit formula. -/
  unit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (X.X n).val.obj V),
    ((((unit R).app X).hom.f n).val.app V)
        ((F R R (𝟙 R)).extension.section X n V r x) = r • x
  /-- Restriction along the identity is the identity functor. -/
  resUnit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    restriction.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R)
  /-- The restriction unit leaves every section unchanged. -/
  resUnit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((resUnit R).app X).hom.f n).val.app V) x = x
  /-- The ordinary R-linear tensor unit identification. -/
  tensorUnit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    tensor.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R)
  /-- The tensor unit contracts r tensor x to rx. -/
  tensorUnit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (X.X n).val.obj V),
    ((((tensorUnit R).app X).hom.f n).val.app V)
        (tensorSection.{c, v, u} (𝟙 R) X n V r x) = r • x
  /-- Contract two successive ordinary extensions. -/
  comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S) (ψ : S ⟶ T),
    (F R S φ).extension.complex ⋙ (F S T ψ).extension.complex ≅
      (F R T (φ ≫ ψ)).extension.complex
  /-- The contraction is multiplication of coefficients. -/
  comp_pure : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : T.obj.obj V) (s : S.obj.obj V) (x : (X.X n).val.obj V),
    ((((comp R S T φ ψ).app X).hom.f n).val.app V)
        ((F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
          ((F R S φ).extension.section X n V s x)) =
      (F R T (φ ≫ ψ)).extension.section X n V (t * ψ.hom.app V s) x
  /-- Restriction along a composite agrees with successive restriction. -/
  resComp : ∀ (R S T : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S) (ψ : S ⟶ T),
    restriction.{c, v, u} ψ ⋙ restriction.{c, v, u} φ ≅ restriction.{c, v, u} (φ ≫ ψ)
  /-- This restriction identification is the identity on sections. -/
  resComp_pure : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (N : Complex.{c, v, u} T)
    (n : ℤ) (V : Cᵒᵖ) (x : (N.X n).val.obj V),
    ((((resComp R S T φ ψ).app N).hom.f n).val.app V) x = x

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.unit_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((L.unit R).app X).inv.f n).val.app V) x =
      (F R R (𝟙 R)).extension.section X n V 1 x := by
  have hf := L.unit_pure R X n V 1 x
  simp only [one_smul] at hf
  have hi := congrArg (fun z ↦ (((L.unit R).app X).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V ((F R R (𝟙 R)).extension.section X n V 1 x))
    ((L.unit R).app X).hom_inv_id
  exact hi.symm.trans hh

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.resUnit_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((L.resUnit R).app X).inv.f n).val.app V) x = x := by
  have hf := L.resUnit_pure R X n V x
  have hi := congrArg (fun z ↦ (((L.resUnit R).app X).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V (x))
    ((L.resUnit R).app X).hom_inv_id
  exact hi.symm.trans hh

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.tensorUnit_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((L.tensorUnit R).app X).inv.f n).val.app V) x =
      tensorSection.{c, v, u} (𝟙 R) X n V 1 x := by
  have hf := L.tensorUnit_pure R X n V 1 x
  simp only [one_smul] at hf
  have hi := congrArg (fun z ↦ (((L.tensorUnit R).app X).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V (tensorSection.{c, v, u} (𝟙 R) X n V 1 x))
    ((L.tensorUnit R).app X).hom_inv_id
  exact hi.symm.trans hh

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.comp_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : T.obj.obj V) (x : (X.X n).val.obj V) :
    ((((L.comp R S T φ ψ).app X).inv.f n).val.app V)
        ((F R T (φ ≫ ψ)).extension.section X n V t x) =
      (F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
        ((F R S φ).extension.section X n V 1 x) := by
  have hf := L.comp_pure R S T φ ψ X n V t 1 x
  simp only [map_one, mul_one] at hf
  have hi := congrArg (fun z ↦ (((L.comp R S T φ ψ).app X).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V
    ((F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
      ((F R S φ).extension.section X n V 1 x)))
    ((L.comp R S T φ ψ).app X).hom_inv_id
  exact hi.symm.trans hh

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.resComp_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (N : Complex.{c, v, u} T)
    (n : ℤ) (V : Cᵒᵖ) (x : (N.X n).val.obj V) :
    ((((L.resComp R S T φ ψ).app N).inv.f n).val.app V) x = x := by
  have hf := L.resComp_pure R S T φ ψ N n V x
  have hi := congrArg (fun z ↦ (((L.resComp R S T φ ψ).app N).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V (x))
    ((L.resComp R S T φ ψ).app N).hom_inv_id
  exact hi.symm.trans hh

/-- The four coefficient equations for every square, with normalized natural comparisons.
Source: Stacks 03CY, 03CZ and 0A8X, node proof steps 1--7
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientChainSquares
    (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ) where
  /-- Kappa and mu on each commuting coefficient square. -/
  square : ∀ (R S R' S' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S'),
    φ ≫ b = a ≫ φ' →
      NormalizedCoefficientSquare.{c, v, u} (F R S φ) (F R R' a) (F S S' b) (F R' S' φ')
  /-- All four chain equations; sigma includes every compatible target w. -/
  compatible : ∀ (R S R' S' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (h : φ ≫ b = a ≫ φ'),
    NormalizedCoefficientCompatibility.{c, v, u} (square R S R' S' φ a b φ' h)
  /-- The underlying tensor comparison is natural as a chain map. -/
  tensor_natural : ∀ (R S R' S' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (h : φ ≫ b = a ≫ φ'),
    (square R S R' S' φ a b φ' h).TensorNatural

/-- Kappa is the identity after the unit identifications.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.kappa_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (X : Complex.{c, v, u} R),
    ((Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).extensionIso.app X).hom ≫
        (F R S φ).extension.complex.map (((L.unit R).app X).hom) =
      ((L.unit S).app ((F R S φ).extension.complex.obj X)).hom

/-- Mu is the identity after the unit identifications.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.mu_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (N : Complex.{c, v, u} S),
    (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).restrictionMate.app N ≫
        (restriction.{c, v, u} φ).map (((L.unit S).app N).hom) =
      ((L.unit R).app ((restriction.{c, v, u} φ).obj N)).hom

/-- Tau is the identity after the unit identifications.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.tau_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (X : Complex.{c, v, u} R),
    (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).tensorComparison X ≫
        (tensor.{c, v, u} φ).map (((L.unit R).app X).hom) =
      ((L.unit R).app ((tensor.{c, v, u} φ).obj X)).hom

/-- Kappa for a pasted square is successive kappa, transported by associators.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.kappa_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (X : Complex.{c, v, u} R),
    (F S' S'' d).extension.complex.map
        (((Q.square R S R' S' φ a b φ' h).extensionIso.app X).hom) ≫
        ((Q.square R' S' R'' S'' φ' c' d φ'' h').extensionIso.app
          ((F R R' a).extension.complex.obj X)).hom =
      ((L.comp S S' S'' b d).app ((F R S φ).extension.complex.obj X)).hom ≫
        ((Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).extensionIso.app X).hom ≫
        (F R'' S'' φ'').extension.complex.map (((L.comp R R' R'' a c').app X).inv)

/-- Mu for a pasted square is successive mu, with restriction of the associator.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.mu_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (N : Complex.{c, v, u} S),
    (F R' R'' c').extension.complex.map
        ((Q.square R S R' S' φ a b φ' h).restrictionMate.app N) ≫
        (Q.square R' S' R'' S'' φ' c' d φ'' h').restrictionMate.app
          ((F S S' b).extension.complex.obj N) =
      ((L.comp R R' R'' a c').app ((restriction.{c, v, u} φ).obj N)).hom ≫
        (Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).restrictionMate.app N ≫
        (restriction.{c, v, u} φ'').map (((L.comp S S' S'' b d).app N).inv)

/-- Tau for a pasted square is successive tau, transported by associators.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.tau_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (X : Complex.{c, v, u} R),
    (F R' R'' c').extension.complex.map
        ((Q.square R S R' S' φ a b φ' h).tensorComparison X) ≫
        (Q.square R' S' R'' S'' φ' c' d φ'' h').tensorComparison
          ((F R R' a).extension.complex.obj X) =
      ((L.comp R R' R'' a c').app ((tensor.{c, v, u} φ).obj X)).hom ≫
        (Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).tensorComparison X ≫
        (tensor.{c, v, u} φ'').map (((L.comp R R' R'' a c').app X).inv)

/-- Identity coefficient squares and pasted coefficient squares give the same maps.
Source: Stacks 03CY, 03CZ and 0A8X, node proof steps 8--11
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientChainPasting
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop where
  /-- Kappa is the identity after the unit identifications. -/
  kappa_id : CoefficientChainPasting.kappa_id_law L Q
  /-- Mu is the identity after the unit identifications. -/
  mu_id : CoefficientChainPasting.mu_id_law L Q
  /-- Tau is the identity after the unit identifications. -/
  tau_id : CoefficientChainPasting.tau_id_law L Q
  /-- Kappa for a pasted square is successive kappa, transported by associators. -/
  kappa_comp : CoefficientChainPasting.kappa_comp_law L Q
  /-- Mu for a pasted square is successive mu, with restriction of the associator. -/
  mu_comp : CoefficientChainPasting.mu_comp_law L Q
  /-- Tau for a pasted square is successive tau, transported by associators. -/
  tau_comp : CoefficientChainPasting.tau_comp_law L Q

/-- The underlying R-linear identification for an iterated scalar tensor.
Source: Stacks 03CY and 03CZ, node proof steps 8 and 10
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientExtensionAssociators.underlyingComp
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    {R S T : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) (ψ : S ⟶ T)
    (X : Complex.{c, v, u} R) :
    (tensor.{c, v, u} (φ ≫ ψ)).obj X ⟶
      (restriction.{c, v, u} φ).obj
        ((tensor.{c, v, u} ψ).obj ((F R S φ).extension.complex.obj X)) :=
  ((F R T (φ ≫ ψ)).chains.nu.app X).hom ≫
    ((L.resComp R S T φ ψ).app ((F R T (φ ≫ ψ)).extension.complex.obj X)).inv ≫
    (restriction.{c, v, u} φ).map
      ((restriction.{c, v, u} ψ).map (((L.comp R S T φ ψ).app X).inv)) ≫
    (restriction.{c, v, u} φ).map
      (((F S T ψ).chains.nu.app ((F R S φ).extension.complex.obj X)).inv)

attribute [local irreducible] CoefficientExtensionAssociators.underlyingComp

/-- Both contractions of three scalar extensions agree.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.associativity_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T V : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (ξ : T ⟶ V) (X : Complex.{c, v, u} R),
    (F T V ξ).extension.complex.map (((L.comp R S T φ ψ).app X).hom) ≫
        ((L.comp R T V (φ ≫ ψ) ξ).app X).hom =
      ((L.comp S T V ψ ξ).app ((F R S φ).extension.complex.obj X)).hom ≫
        ((L.comp R S V φ (ψ ≫ ξ)).app X).hom ≫
        eqToHom (congrArg
          (fun f : R ⟶ V ↦ (F R V f).extension.complex.obj X)
          (Category.assoc φ ψ ξ).symm)

/-- Inserting an identity extension before extension gives the same contraction.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.left_unit_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (X : Complex.{c, v, u} R),
    ((L.comp R R S (𝟙 R) φ).app X).hom ≫
        eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X)
          (Category.id_comp φ)) =
      (F R S φ).extension.complex.map (((L.unit R).app X).hom)

/-- Inserting an identity extension after extension gives the same contraction.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.right_unit_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (X : Complex.{c, v, u} R),
    ((L.comp R S S φ (𝟙 S)).app X).hom ≫
        eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X)
          (Category.comp_id φ)) =
      ((L.unit S).app ((F R S φ).extension.complex.obj X)).hom

/-- Nu for identity coefficients becomes the identity tensor identification.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.nu_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (X : Complex.{c, v, u} R),
    ((F R R (𝟙 R)).chains.nu.app X).hom ≫
        (restriction.{c, v, u} (𝟙 R)).map (((L.unit R).app X).hom) ≫
        ((L.resUnit R).app X).hom =
      ((L.tensorUnit R).app X).hom

/-- Chi for identity coefficients becomes the identity Hom comparison.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.chi_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A : Complex.{c, v, u} R),
    (F R R (𝟙 R)).homComparison P A ≫
        homMap.{c, v, u} (((L.unit R).app P).inv) (((L.unit R).app A).hom) =
      ((L.unit R).app (homComplex (R := R) P A)).hom

/-- Theta for identity coefficients is the identity after unit identifications.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.theta_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (P N : Complex.{c, v, u} R),
    ((F R R (𝟙 R)).chains.theta P N).hom ≫
        homMap.{c, v, u} (𝟙 P) (((L.resUnit R).app N).hom) =
      ((L.resUnit R).app
        (homComplex (R := R) ((F R R (𝟙 R)).extension.complex.obj P) N)).hom ≫
        homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N)

/-- Alpha for identity coefficients is the identity after tensor unit contraction.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.alpha_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A : Complex.{c, v, u} R),
    (F R R (𝟙 R)).alpha P A ≫
        homMap.{c, v, u} (𝟙 P) (((L.tensorUnit R).app A).hom) =
      ((L.tensorUnit R).app (homComplex (R := R) P A)).hom

/-- Sigma for identity coefficients is composition with its arbitrary target map.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.sigma_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A N : Complex.{c, v, u} R)
    (q : (F R R (𝟙 R)).extension.complex.obj A ⟶ N),
    (F R R (𝟙 R)).sigma P A N q ≫ homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N) =
      ((L.unit R).app (homComplex (R := R) P A)).hom ≫
        homMap.{c, v, u} (𝟙 P) ((((L.unit R).app A).inv) ≫ q)

/-- Nu respects contraction of an iterated scalar tensor.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.nu_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R),
    L.underlyingComp φ ψ X ≫ (restriction.{c, v, u} φ).map
        (((F S T ψ).chains.nu.app ((F R S φ).extension.complex.obj X)).hom) =
      ((F R T (φ ≫ ψ)).chains.nu.app X).hom ≫
        ((L.resComp R S T φ ψ).app ((F R T (φ ≫ ψ)).extension.complex.obj X)).inv ≫
        (restriction.{c, v, u} φ).map
          ((restriction.{c, v, u} ψ).map (((L.comp R S T φ ψ).app X).inv))

/-- Successive Hom comparisons contract to the direct Hom comparison.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.chi_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R),
    (F S T ψ).extension.complex.map ((F R S φ).homComparison P A) ≫
        (F S T ψ).homComparison ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A) ≫
        homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv)
          (((L.comp R S T φ ψ).app A).hom) =
      ((L.comp R S T φ ψ).app (homComplex (R := R) P A)).hom ≫
        (F R T (φ ≫ ψ)).homComparison P A

/-- Successive adjunction maps evaluate at the same twice-inserted unit.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.theta_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} T),
    (restriction.{c, v, u} φ).map
        (((F S T ψ).chains.theta ((F R S φ).extension.complex.obj P) N).hom) ≫
        ((F R S φ).chains.theta P ((restriction.{c, v, u} ψ).obj N)).hom ≫
        homMap.{c, v, u} (𝟙 P) (((L.resComp R S T φ ψ).app N).hom) =
      ((L.resComp R S T φ ψ).app (homComplex (R := T)
        ((F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj P)) N)).hom ≫
        (restriction.{c, v, u} (φ ≫ ψ)).map
          (homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N)) ≫
        ((F R T (φ ≫ ψ)).chains.theta P N).hom

/-- Alpha commutes with contraction of the iterated tensor and Hom evaluation.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.alpha_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R),
    (F R T (φ ≫ ψ)).alpha P A ≫
        homMap.{c, v, u} (𝟙 P) (L.underlyingComp φ ψ A) =
      L.underlyingComp φ ψ (homComplex (R := R) P A) ≫
        (restriction.{c, v, u} φ).map
          ((tensor.{c, v, u} ψ).map ((F R S φ).homComparison P A)) ≫
        (restriction.{c, v, u} φ).map
          ((F S T ψ).alpha ((F R S φ).extension.complex.obj P)
            ((F R S φ).extension.complex.obj A)) ≫
        ((F R S φ).chains.theta P
          ((tensor.{c, v, u} ψ).obj ((F R S φ).extension.complex.obj A))).hom

/-- Successive sigma agrees for any target and any compatible chain map.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.sigma_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R)
    (N : Complex.{c, v, u} T)
    (q : (F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj A) ⟶ N),
    (F S T ψ).extension.complex.map ((F R S φ).homComparison P A) ≫
        (F S T ψ).sigma ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A) N q ≫
        homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N) =
      ((L.comp R S T φ ψ).app (homComplex (R := R) P A)).hom ≫
        (F R T (φ ≫ ψ)).sigma P A N ((((L.comp R S T φ ψ).app A).inv) ≫ q)

/-- Composition of the supplied normalized maps is direct scalar change.
Source: Stacks 03CY, 03CZ and 0A8X, node proof steps 8 and 10
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientHomIteration
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop where
  /-- Both contractions of three scalar extensions agree. -/
  associativity : CoefficientHomIteration.associativity_law L
  /-- Inserting an identity extension before extension gives the same contraction. -/
  left_unit : CoefficientHomIteration.left_unit_law L
  /-- Inserting an identity extension after extension gives the same contraction. -/
  right_unit : CoefficientHomIteration.right_unit_law L
  /-- Nu for identity coefficients becomes the identity tensor identification. -/
  nu_id : CoefficientHomIteration.nu_id_law L
  /-- Chi for identity coefficients becomes the identity Hom comparison. -/
  chi_id : CoefficientHomIteration.chi_id_law L
  /-- Theta for identity coefficients is the identity after unit identifications. -/
  theta_id : CoefficientHomIteration.theta_id_law L
  /-- Alpha for identity coefficients is the identity after tensor unit contraction. -/
  alpha_id : CoefficientHomIteration.alpha_id_law L
  /-- Sigma for identity coefficients is composition with its arbitrary target map. -/
  sigma_id : CoefficientHomIteration.sigma_id_law L
  /-- Nu respects contraction of an iterated scalar tensor. -/
  nu_comp : CoefficientHomIteration.nu_comp_law L
  /-- Successive Hom comparisons contract to the direct Hom comparison. -/
  chi_comp : CoefficientHomIteration.chi_comp_law L
  /-- Successive adjunction maps evaluate at the same twice-inserted unit. -/
  theta_comp : CoefficientHomIteration.theta_comp_law L
  /-- Alpha commutes with contraction of the iterated tensor and Hom evaluation. -/
  alpha_comp : CoefficientHomIteration.alpha_comp_law L
  /-- Successive sigma agrees for any target and any compatible chain map. -/
  sigma_comp : CoefficientHomIteration.sigma_comp_law L

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
attribute [local semireducible] evaluate homMap Extension.complex
  NormalizedCoefficientMaps.homComparison
private theorem canonicalExtension_eq
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : E = canonicalExtension.{c, v, u} φ := by
  have hf : E.functor = (canonicalExtension.{c, v, u} φ).functor :=
    CategoryTheory.Functor.ext E.obj_eq (by
      intro M N f
      exact E.map_eq f)
  cases E
  cases hf
  rfl

private theorem dataSigma_unit
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedCoefficientMaps.{c, v, u} φ) (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u}
      S)
    (q : D.extension.complex.obj A ⟶ N) (n i k : ℤ) (hik : i + n = k)
    (V : Cᵒᵖ) (f : ((homComplex P A).X n).val.obj V) (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} (D.extension.complex.obj P) N n i k hik V
      (((D.sigma P A N q).f n).val.app V
        (D.extension.section (homComplex P A) n V 1 f))
      (D.extension.section P i V 1 x) =
    (q.f k).val.app V (D.extension.section A k V 1 (evaluate.{c, v, u} P A n i k hik V f x)) := by
  simpa only [one_mul, one_smul] using D.sigma_formula P A N q n i k hik V 1 1 f x


set_option backward.isDefEq.respectTransparency true

private def chainEmbedding {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : 𝟭 (Complex.{c, v, u} R) ⟶
      E.complex ⋙ restriction.{c, v, u} φ := by
  have he := canonicalExtension_eq.{c, v, u} E
  subst E
  exact (chainAdjunction.{c, v, u} φ).unit

private theorem chainEmbedding_pure
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (x : (X.X n).val.obj V) :
    (((chainEmbedding.{c, v, u} E).app X).f n).val.app V x = E.section X n V 1 x := by
  have he := canonicalExtension_eq.{c, v, u} E
  subst E
  exact chainAdjunction_unit_pure.{c, v, u} φ X n V x

private theorem normalizedScalarHom_ext
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedCoefficientMaps.{c, v, u} φ) (H P : Complex.{c, v, u} R) (N : Complex.{c, v, u}
      S)
    (f g : D.extension.complex.obj H ⟶ homComplex (R := S) (D.extension.complex.obj P) N)
    (hfg : ∀ (n i k : ℤ) (hik : i + n = k) (V : Cᵒᵖ)
      (z : (H.X n).val.obj V) (x : (P.X i).val.obj V),
      evaluate.{c, v, u} (D.extension.complex.obj P) N n i k hik V
        ((f.f n).val.app V (D.extension.section H n V 1 z))
        (D.extension.section P i V 1 x) =
      evaluate.{c, v, u} (D.extension.complex.obj P) N n i k hik V
        ((g.f n).val.app V (D.extension.section H n V 1 z))
        (D.extension.section P i V 1 x)) : f = g := by
  apply extension_hom_ext.{c, v, u} D.extension H
  intro n V z
  let a := (chainEmbedding.{c, v, u} D.extension).app H ≫
    (restriction.{c, v, u} φ).map f ≫ (D.chains.theta P N).hom
  let b := (chainEmbedding.{c, v, u} D.extension).app H ≫
    (restriction.{c, v, u} φ).map g ≫ (D.chains.theta P N).hom
  have hab : a = b := by
    apply HomologicalComplex.hom_ext
    intro m
    apply evaluate_hom_ext.{c, v, u} P ((restriction.{c, v, u} φ).obj N) m
    intro i k hik W y x
    change evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) m i k hik W
        ((((D.chains.theta P N).hom.f m).val.app W)
          ((f.f m).val.app W
            ((((chainEmbedding.{c, v, u} D.extension).app H).f m).val.app W y))) x =
      evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) m i k hik W
        ((((D.chains.theta P N).hom.f m).val.app W)
          ((g.f m).val.app W ((((chainEmbedding.{c, v, u} D.extension).app H).f m).val.app W y))) x
    rw [D.chains.theta_forward, D.chains.theta_forward, chainEmbedding_pure.{c, v, u}]
    exact hfg m i k hik W y x
  have hv := congrArg (fun t ↦ (t.f n).val.app V z) hab
  change (((D.chains.theta P N).hom.f n).val.app V
      ((f.f n).val.app V ((((chainEmbedding.{c, v, u} D.extension).app H).f n).val.app V z))) =
    (((D.chains.theta P N).hom.f n).val.app V
      ((g.f n).val.app V ((((chainEmbedding.{c, v, u} D.extension).app H).f n).val.app V z))) at hv
  rw [chainEmbedding_pure.{c, v, u}] at hv
  have he := congrArg (fun t ↦ (t.f n).val.app V)
    (D.chains.theta P N).hom_inv_id
  have hi := congrArg (fun t ↦ t ((f.f n).val.app V (D.extension.section H n V 1 z))) he
  have hj := congrArg (fun t ↦ t ((g.f n).val.app V (D.extension.section H n V 1 z))) he
  exact hi.symm.trans
    ((congrArg (((D.chains.theta P N).inv.f n).val.app V) hv).trans hj)

private theorem normalized_ext
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D D' : NormalizedCoefficientMaps.{c, v, u} φ) : D = D' := by
  have he : D.extension = D'.extension :=
    (canonicalExtension_eq.{c, v, u} D.extension).trans
      (canonicalExtension_eq.{c, v, u} D'.extension).symm
  rcases D with ⟨E, T, alpha, ha, sigma, hs⟩
  rcases D' with ⟨E', T', alpha', ha', sigma', hs'⟩
  dsimp only at he
  cases he
  have hn : T.nu = T'.nu := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply HomologicalComplex.hom_ext
    intro n
    apply tensorUnitMap_hom_ext.{c, v, u}
    intro V r x
    have h := (T.nu_pure X n V r x).trans (T'.nu_pure X n V r x).symm
    convert h using 1 <;> (unfold tensorSection tensorUnitMap; rfl)
  have ht : T.theta = T'.theta := by
    funext P N
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro n
    apply evaluate_hom_ext.{c, v, u}
    intro i k hik V f x
    exact (T.theta_forward P N n i k hik V f x).trans
      (T'.theta_forward P N n i k hik V f x).symm
  have halpha : alpha = alpha' := by
    funext P A
    apply HomologicalComplex.hom_ext
    intro n
    apply tensorModuleHom_ext.{c, v, u} φ
    intro i k hik V r f x
    exact (ha P A n i k hik V r f x).trans (ha' P A n i k hik V r f x).symm
  have hsigma : sigma = sigma' := by
    funext P A N q
    apply normalizedScalarHom_ext.{c, v, u} ⟨E, T, alpha, ha, sigma, hs⟩
    intro n i k hik V f x
    exact (hs P A N q n i k hik V 1 1 f x).trans
      (hs' P A N q n i k hik V 1 1 f x).symm
  cases T
  cases T'
  dsimp only at hn ht
  cases hn
  cases ht
  cases halpha
  cases hsigma
  rfl

private theorem tensor_hom_ext
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (H N : Complex.{c, v, u} R) (f g : (tensor.{c, v, u} φ).obj H ⟶ N)
    (h : ∀ (n : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V) (x : (H.X n).val.obj V),
      (f.f n).val.app V (tensorSection.{c, v, u} φ H n V s x) =
      (g.f n).val.app V (tensorSection.{c, v, u} φ H n V s x)) : f = g := by
  ext n : 1
  exact tensorUnitMap_hom_ext.{c, v, u} (scalarModule.{c, v, u} φ) (H.X n) (N.X n)
    (f.f n) (g.f n) (by
      intro V r x
      convert h n V r x using 1 <;> (unfold tensorSection tensorUnitMap; rfl))


set_option backward.isDefEq.respectTransparency false
private def normalizedFromData
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : Data.{c, v, u} φ) : NormalizedCoefficientMaps.{c, v, u} φ where
  extension := D.extension
  chains := chainsFromData.{c, v, u} D
  alpha := D.alpha
  alpha_evaluate := D.alpha_evaluate
  sigma := D.sigma
  sigma_formula := D.sigma_formula

private def squareFromData
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : Data.{c, v, u} φ} {Da : Data.{c, v, u} a}
    {Db : Data.{c, v, u} b} {D' : Data.{c, v, u} φ'}
    (Q : CoefficientSquare.{c, v, u} D Da Db D')
    (hInv : ∀ (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
      (s : S'.obj.obj V) (r : R'.obj.obj V) (x : (X.X n).val.obj V),
      (((Q.extensionIso.app X).inv.f n).val.app V)
        (D'.extension.section (Da.extension.complex.obj X) n V s
          (Da.extension.section X n V r x)) =
        Db.extension.section (D.extension.complex.obj X) n V (s * φ'.hom.app V r)
          (D.extension.section X n V 1 x)) :
    NormalizedCoefficientSquare.{c, v, u} (normalizedFromData D) (normalizedFromData Da)
      (normalizedFromData Db) (normalizedFromData D') where
  extensionIso := Q.extensionIso
  extensionIso_pure := Q.extensionIso_pure
  extensionIso_inv_pure := hInv
  restrictionMate := Q.restrictionMate
  restrictionMate_pure := Q.restrictionMate_pure

attribute [local semireducible] NormalizedCoefficientSquare.tensorComparison in
private theorem compatibleFromData
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : Data.{c, v, u} φ} {Da : Data.{c, v, u} a}
    {Db : Data.{c, v, u} b} {D' : Data.{c, v, u} φ'}
    (Q : CoefficientSquare.{c, v, u} D Da Db D')
    (hInv : ∀ (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
      (s : S'.obj.obj V) (r : R'.obj.obj V) (x : (X.X n).val.obj V),
      (((Q.extensionIso.app X).inv.f n).val.app V)
        (D'.extension.section (Da.extension.complex.obj X) n V s
          (Da.extension.section X n V r x)) =
        Db.extension.section (D.extension.complex.obj X) n V (s * φ'.hom.app V r)
          (D.extension.section X n V 1 x))
    (h : CoefficientCompatibility Q) :
    NormalizedCoefficientCompatibility (squareFromData.{c, v, u} Q hInv) where
  tensor_pure := h.tensor_pure
  nu := h.nu
  theta := h.theta
  alpha := h.alpha
  sigma := h.sigma

attribute [local instance] ordinaryExtension_additive

private def restrictionUnit (R : Sheaf J CommRingCat.{max c v u}) :
    restriction.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R) :=
  NatIso.ofComponents (fun X ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ Iso.refl _) (by intros; rfl)) (by intros; rfl)

private def restrictionComp {R S T : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) (ψ : S ⟶ T) :
    restriction.{c, v, u} ψ ⋙ restriction.{c, v, u} φ ≅ restriction.{c, v, u} (φ ≫ ψ) :=
  NatIso.ofComponents (fun X ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ Iso.refl _) (by intros; rfl)) (by intros; rfl)

private def extensionAdj {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : E.complex ⊣ restriction.{c, v, u} φ := by
  have he := canonicalExtension_eq.{c, v, u} E
  subst E
  exact chainAdjunction.{c, v, u} φ

private theorem extensionAdj_unit
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((extensionAdj.{c, v, u} E).unit.app X).f n).val.app V) x = E.section X n V 1 x := by
  have he := canonicalExtension_eq.{c, v, u} E
  subst E
  exact chainAdjunction_unit_pure.{c, v, u} φ X n V x

attribute [local irreducible] extensionAdj chainAdjunction ordinaryAdjunction
  scalarSheafHomEquiv Adjunction.leftAdjointUniq Adjunction.ofNatIsoRight Adjunction.comp

private theorem extension_base_smul
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (r : R.obj.obj V) (x : (X.X n).val.obj V) :
    E.section X n V s (r • x) = E.section X n V (s * φ.hom.app V r) x := by
  have he := canonicalExtension_eq.{c, v, u} E
  subst E
  exact scalarExtensionSection_base_smul φ (X.X n) V s r x


section
variable (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
  NormalizedCoefficientMaps.{c, v, u} φ)

private def familyUnit (R : Sheaf J CommRingCat.{max c v u}) :
    (F R R (𝟙 R)).extension.complex ≅ 𝟭 (Complex.{c, v, u} R) :=
  Adjunction.leftAdjointUniq
    ((extensionAdj.{c, v, u} (F R R (𝟙 R)).extension).ofNatIsoRight
      (restrictionUnit.{c, v, u} R)) Adjunction.id

private theorem familyUnit_one (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((familyUnit.{c, v, u} F R).app X).hom.f n).val.app V)
      ((F R R (𝟙 R)).extension.section X n V 1 x) = x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((extensionAdj.{c, v, u} (F R R (𝟙 R)).extension).ofNatIsoRight
      (restrictionUnit.{c, v, u} R)) Adjunction.id X
  rw [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app] at h
  have hh := congrArg (fun f ↦ (f.f n).val.app V x) h
  change ((((familyUnit.{c, v, u} F R).app X).hom.f n).val.app V)
    ((((extensionAdj.{c, v, u} (F R R (𝟙 R)).extension).unit.app X).f n).val.app V x) = x at hh
  rw [extensionAdj_unit.{c, v, u}] at hh
  exact hh

attribute [local irreducible] familyUnit

private theorem familyUnit_pure (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (X.X n).val.obj V) :
    ((((familyUnit.{c, v, u} F R).app X).hom.f n).val.app V)
      ((F R R (𝟙 R)).extension.section X n V r x) = r • x := by
  rw [extension_section_smul.{c, v, u}, map_smul, familyUnit_one.{c, v, u}]


private def familyComp {R S T : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) (ψ : S ⟶ T) :
    (F R S φ).extension.complex ⋙ (F S T ψ).extension.complex ≅
      (F R T (φ ≫ ψ)).extension.complex :=
  Adjunction.leftAdjointUniq
    (((extensionAdj.{c, v, u} (F R S φ).extension).comp
      (extensionAdj.{c, v, u} (F S T ψ).extension)).ofNatIsoRight
        (restrictionComp.{c, v, u} φ ψ)) (extensionAdj.{c, v, u} (F R T (φ ≫ ψ)).extension)

private theorem familyComp_one {R S T : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((familyComp.{c, v, u} F φ ψ).app X).hom.f n).val.app V)
      ((F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V 1
        ((F R S φ).extension.section X n V 1 x)) =
      (F R T (φ ≫ ψ)).extension.section X n V 1 x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((extensionAdj.{c, v, u} (F R S φ).extension).comp
      (extensionAdj.{c, v, u} (F S T ψ).extension)).ofNatIsoRight
        (restrictionComp.{c, v, u} φ ψ)) (extensionAdj.{c, v, u} (F R T (φ ≫ ψ)).extension) X
  rw [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app] at h
  have hh := congrArg (fun f ↦ (f.f n).val.app V x) h
  change ((((familyComp.{c, v, u} F φ ψ).app X).hom.f n).val.app V)
    ((((extensionAdj.{c, v, u} (F S T ψ).extension).unit.app
      ((F R S φ).extension.complex.obj X)).f n).val.app V
        ((((extensionAdj.{c, v, u} (F R S φ).extension).unit.app X).f n).val.app V x)) =
    ((((extensionAdj.{c, v, u} (F R T (φ ≫ ψ)).extension).unit.app X).f n).val.app V x) at hh
  rw [extensionAdj_unit.{c, v, u}, extensionAdj_unit.{c, v, u},
    extensionAdj_unit.{c, v, u}] at hh
  exact hh

attribute [local irreducible] familyComp

private theorem familyComp_pure {R S T : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : T.obj.obj V) (r : S.obj.obj V) (x : (X.X n).val.obj V) :
    ((((familyComp.{c, v, u} F φ ψ).app X).hom.f n).val.app V)
      ((F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
        ((F R S φ).extension.section X n V r x)) =
      (F R T (φ ≫ ψ)).extension.section X n V (t * ψ.hom.app V r) x := by
  rw [extension_section_smul.{c, v, u} (F R S φ).extension, extension_base_smul.{c, v, u},
    extension_section_smul.{c, v, u} (F S T ψ).extension, map_smul]
  exact (congrArg (fun z ↦ (t * ψ.hom.app V r) • z)
    (familyComp_one.{c, v, u} F φ ψ X n V x)).trans
    (extension_section_smul.{c, v, u} (F R T (φ ≫ ψ)).extension X n V
      (t * ψ.hom.app V r) x).symm


private def familyTensorUnit (R : Sheaf J CommRingCat.{max c v u}) :
    tensor.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R) :=
  (F R R (𝟙 R)).chains.nu ≪≫
    CategoryTheory.Functor.isoWhiskerRight (familyUnit.{c, v, u} F R) _ ≪≫
      restrictionUnit.{c, v, u} R

private theorem familyTensorUnit_pure (R : Sheaf J CommRingCat.{max c v u})
  (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
  (r : R.obj.obj V) (x : (X.X n).val.obj V) :
  ((((familyTensorUnit.{c, v, u} F R).app X).hom.f n).val.app V)
    (tensorSection.{c, v, u} (𝟙 R) X n V r x) = r • x := by
  change ((((restrictionUnit.{c, v, u} R).app X).hom.f n).val.app V)
    (((((familyUnit.{c, v, u} F R).app X).hom.f n).val.app V)
      (((((F R R (𝟙 R)).chains.nu.app X).hom.f n).val.app V)
        (tensorSection.{c, v, u} (𝟙 R) X n V r x))) = _
  rw [(F R R (𝟙 R)).chains.nu_pure, familyUnit_pure.{c, v, u}]
  rfl

attribute [local irreducible] familyTensorUnit

private def familyAssociators : CoefficientExtensionAssociators.{c, v, u} F where
  unit := familyUnit.{c, v, u} F
  unit_pure := familyUnit_pure.{c, v, u} F
  resUnit := restrictionUnit.{c, v, u}
  resUnit_pure := by intros; rfl
  comp := fun _ _ _ φ ψ ↦ familyComp.{c, v, u} F φ ψ
  comp_pure := fun _ _ _ φ ψ ↦ familyComp_pure.{c, v, u} F φ ψ
  resComp := fun _ _ _ φ ψ ↦ restrictionComp.{c, v, u} φ ψ
  resComp_pure := by intros; rfl
  tensorUnit := familyTensorUnit.{c, v, u} F
  tensorUnit_pure := familyTensorUnit_pure.{c, v, u} F

end
private theorem tensorNatural
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Q.TensorNatural := by
  intro X Y f
  have hn := D.chains.nu.hom.naturality f
  have hm := Q.restrictionMate.naturality (D.extension.complex.map f)
  have hk := Q.extensionIso.hom.naturality f
  have hi := D'.chains.nu.inv.naturality (Da.extension.complex.map f)
  dsimp only [Functor.comp_map, Iso.app_hom, Iso.app_inv] at hn hm hk hi
  unfold NormalizedCoefficientSquare.tensorComparison
  simp only [Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [← CategoryTheory.Functor.map_comp_assoc, hn,
    CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% hm]
  rw [← CategoryTheory.Functor.map_comp_assoc, hk,
    CategoryTheory.Functor.map_comp, Category.assoc, hi]


private theorem genericSquareInverse
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : Data.{c, v, u} φ} {Da : Data.{c, v, u} a}
    {Db : Data.{c, v, u} b} {D' : Data.{c, v, u} φ'}
    (Q : CoefficientSquare.{c, v, u} D Da Db D')
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S'.obj.obj V) (r : R'.obj.obj V) (x : (X.X n).val.obj V) :
    (((Q.extensionIso.app X).inv.f n).val.app V)
      (D'.extension.section (Da.extension.complex.obj X) n V s
        (Da.extension.section X n V r x)) =
      Db.extension.section (D.extension.complex.obj X) n V (s * φ'.hom.app V r)
        (D.extension.section X n V 1 x) := by
  have hb : D'.extension.section (Da.extension.complex.obj X) n V s
      (r • Da.extension.section X n V 1 x) =
      D'.extension.section (Da.extension.complex.obj X) n V (s * φ'.hom.app V r)
        (Da.extension.section X n V 1 x) := by
    unfold Extension.section
    rw [scalarExtensionSection_base_smul]
  rw [extension_section_smul.{c, v, u} Da.extension X n V r x, hb]
  have hf := Q.extensionIso_pure X n V (s * φ'.hom.app V r) 1 x
  simp only [map_one, mul_one] at hf
  have hi := congrArg (fun z ↦ (((Q.extensionIso.app X).inv.f n).val.app V) z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V
    (Db.extension.section (D.extension.complex.obj X) n V (s * φ'.hom.app V r)
      (D.extension.section X n V 1 x))) (Q.extensionIso.app X).hom_inv_id
  exact hi.symm.trans hh

private theorem squares_exists
    (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ) :
    Nonempty (CoefficientChainSquares.{c, v, u} F) := by
  classical
  obtain ⟨D, hD⟩ := exists_scalarHomChainIdentification.{c, v, u} (J := J)
  let G := fun R S φ ↦ normalizedFromData.{c, v, u} (D R S φ)
  have hG : G = F := by
    funext R S φ
    exact normalized_ext.{c, v, u} (G R S φ) (F R S φ)
  have hQ : Nonempty (CoefficientChainSquares.{c, v, u} G) := by
    let K := fun R S R' S' φ a b φ' h ↦ Classical.choose (hD R S R' S' φ a b φ' h)
    refine ⟨{ square := ?_, compatible := ?_, tensor_natural := ?_ }⟩
    · intro R S R' S' φ a b φ' h
      exact squareFromData.{c, v, u} (K R S R' S' φ a b φ' h)
        (genericSquareInverse.{c, v, u} _)
    · intro R S R' S' φ a b φ' h
      exact compatibleFromData.{c, v, u} (K R S R' S' φ a b φ' h)
        (genericSquareInverse.{c, v, u} _) (Classical.choose_spec (hD R S R' S' φ a b φ' h))
    · intro R S R' S' φ a b φ' h
      exact tensorNatural.{c, v, u} _
  rw [hG] at hQ
  exact hQ


set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Extension.complex





section
variable {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
  NormalizedCoefficientMaps.{c, v, u} φ}
  (L : CoefficientExtensionAssociators.{c, v, u} F)
include L in
private theorem towerComp_ext
    (R S T : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S) (ψ : S ⟶ T)
    (H : Complex.{c, v, u} R) (N : Complex.{c, v, u} T)
    (f g : (F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj H) ⟶ N)
    (h : ∀ (n : ℤ) (V : Cᵒᵖ) (x : (H.X n).val.obj V),
      (f.f n).val.app V ((F S T ψ).extension.section
        ((F R S φ).extension.complex.obj H) n V 1
        ((F R S φ).extension.section H n V 1 x)) =
      (g.f n).val.app V ((F S T ψ).extension.section
        ((F R S φ).extension.complex.obj H) n V 1
        ((F R S φ).extension.section H n V 1 x))) : f = g := by
  apply (cancel_epi (((L.comp R S T φ ψ).app H).inv)).mp
  apply extension_hom_ext.{c, v, u} (F R T (φ ≫ ψ)).extension
  intro n V x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [L.comp_inv]
  exact h n V x


include L in
private theorem towerCompThree_ext
    (R S T U : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (ξ : T ⟶ U)
    (H : Complex.{c, v, u} R) (N : Complex.{c, v, u} U)
    (f g : (F T U ξ).extension.complex.obj
      ((F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj H)) ⟶ N)
    (h : ∀ (n : ℤ) (V : Cᵒᵖ) (x : (H.X n).val.obj V),
      (f.f n).val.app V ((F T U ξ).extension.section
        ((F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj H)) n V 1
        ((F S T ψ).extension.section ((F R S φ).extension.complex.obj H) n V 1
          ((F R S φ).extension.section H n V 1 x))) =
      (g.f n).val.app V ((F T U ξ).extension.section
        ((F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj H)) n V 1
        ((F S T ψ).extension.section ((F R S φ).extension.complex.obj H) n V 1
          ((F R S φ).extension.section H n V 1 x)))) : f = g := by
  apply (cancel_epi (((L.comp S T U ψ ξ).app
    ((F R S φ).extension.complex.obj H)).inv)).mp
  apply towerComp_ext.{c, v, u} L R S U φ (ψ ≫ ξ) H N
  intro n V x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [L.comp_inv]
  exact h n V x

end

private theorem evaluate_smul_local {R : Sheaf J CommRingCat.{max c v u}}
    (P A : Complex.{c, v, u} R) (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (r : R.obj.obj V) (f : ((homComplex (R := R) P A).X n).val.obj V)
    (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} P A n i k h V (r • f) x = r • evaluate.{c, v, u} P A n i k h V f x := by
  unfold evaluate
  rw [map_smul]
  change R.obj.map (𝟙 V.unop).op r • evaluate P A n i k h V f x =
    r • evaluate P A n i k h V f x
  simp

private theorem transport_section
    (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ)
    {R S : Sheaf J CommRingCat.{max c v u}} {φ ψ : R ⟶ S} (h : φ = ψ)
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : S.obj.obj V) (x : (X.X n).val.obj V) :
    ((eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X) h)).f n).val.app V
      ((F R S φ).extension.section X n V r x) =
      (F R S ψ).extension.section X n V r x := by
  cases h
  rfl


private theorem dataChi_unit
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedCoefficientMaps.{c, v, u} φ) (P A : Complex.{c, v, u} R)
    (n i k : ℤ) (hik : i + n = k) (V : Cᵒᵖ)
    (f : ((homComplex P A).X n).val.obj V) (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} (D.extension.complex.obj P) (D.extension.complex.obj A) n i k hik V
      (((D.homComparison P A).f n).val.app V
        (D.extension.section (homComplex P A) n V 1 f))
      (D.extension.section P i V 1 x) =
      D.extension.section A k V 1 (evaluate.{c, v, u} P A n i k hik V f x) := by
  exact dataSigma_unit.{c, v, u} D P A (D.extension.complex.obj A) (𝟙 _) n i k hik V f x

section
variable {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
  NormalizedCoefficientMaps.{c, v, u} φ}
  (L : CoefficientExtensionAssociators.{c, v, u} F)

include L in
private theorem directHom_tower_ext
    {R S T : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) (ψ : S ⟶ T)
    (H P : Complex.{c, v, u} R) (N : Complex.{c, v, u} T)
    (f g : (F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj H) ⟶
      homComplex (R := T) ((F R T (φ ≫ ψ)).extension.complex.obj P) N)
    (hfg : ∀ (n i k : ℤ) (hik : i + n = k) (V : Cᵒᵖ)
      (z : (H.X n).val.obj V) (x : (P.X i).val.obj V),
      evaluate.{c, v, u} ((F R T (φ ≫ ψ)).extension.complex.obj P) N n i k hik V
        ((f.f n).val.app V ((F S T ψ).extension.section
          ((F R S φ).extension.complex.obj H) n V 1
          ((F R S φ).extension.section H n V 1 z)))
        ((F R T (φ ≫ ψ)).extension.section P i V 1 x) =
      evaluate.{c, v, u} ((F R T (φ ≫ ψ)).extension.complex.obj P) N n i k hik V
        ((g.f n).val.app V ((F S T ψ).extension.section
          ((F R S φ).extension.complex.obj H) n V 1
          ((F R S φ).extension.section H n V 1 z)))
        ((F R T (φ ≫ ψ)).extension.section P i V 1 x)) : f = g := by
  apply (cancel_epi (((L.comp R S T φ ψ).app H).inv)).mp
  apply normalizedScalarHom_ext.{c, v, u} (F R T (φ ≫ ψ)) H P N
  intro n i k hik V z x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [L.comp_inv]
  exact hfg n i k hik V z x


end


section
variable {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
  NormalizedCoefficientMaps.{c, v, u} φ}
  (L : CoefficientExtensionAssociators.{c, v, u} F)

private theorem nu_inv_pure
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedCoefficientMaps.{c, v, u} φ) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : S.obj.obj V) (x : (X.X n).val.obj V) :
    (((D.chains.nu.app X).inv.f n).val.app V)
      (D.extension.section X n V t x) = tensorSection.{c, v, u} φ X n V t x := by
  rw [← D.chains.nu_pure]
  exact congrArg (fun f ↦ (f.f n).val.app V (tensorSection.{c, v, u} φ X n V t x))
    (D.chains.nu.app X).hom_inv_id

private theorem underlyingComp_pure
    {R S T : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) (ψ : S ⟶ T)
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (t : T.obj.obj V) (x : (X.X n).val.obj V) :
    ((L.underlyingComp φ ψ X).f n).val.app V
      (tensorSection.{c, v, u} (φ ≫ ψ) X n V t x) =
      tensorSection.{c, v, u} ψ ((F R S φ).extension.complex.obj X) n V t
        ((F R S φ).extension.section X n V 1 x) := by
  unfold CoefficientExtensionAssociators.underlyingComp
  change (((((F S T ψ).chains.nu.app ((F R S φ).extension.complex.obj X)).inv.f n).val.app V)
    (((((L.comp R S T φ ψ).app X).inv.f n).val.app V)
      (((((L.resComp R S T φ ψ).app ((F R T (φ ≫ ψ)).extension.complex.obj X)).inv.f n).val.app V)
        (((((F R T (φ ≫ ψ)).chains.nu.app X).hom.f n).val.app V)
          (tensorSection.{c, v, u} (φ ≫ ψ) X n V t x))))) = _
  rw [(F R T (φ ≫ ψ)).chains.nu_pure, L.resComp_inv, L.comp_inv, nu_inv_pure.{c, v, u}]

end

section
variable {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
  NormalizedCoefficientMaps.{c, v, u} φ}
  (L : CoefficientExtensionAssociators.{c, v, u} F)
include L in
private theorem towerTensor_hom_ext
    {R S T U : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} (a : R ⟶ T) (c' : T ⟶ U)
    (X : Complex.{c, v, u} R) (N : Complex.{c, v, u} U)
    (f g : (F T U c').extension.complex.obj
      ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X)) ⟶ N)
    (hfg : ∀ (n : ℤ) (V : Cᵒᵖ) (t : S.obj.obj V) (x : (X.X n).val.obj V),
      (f.f n).val.app V ((F T U c').extension.section
        ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X)) n V 1
        ((F R T a).extension.section ((tensor.{c, v, u} φ).obj X) n V 1
          (tensorSection.{c, v, u} φ X n V t x))) =
      (g.f n).val.app V ((F T U c').extension.section
        ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X)) n V 1
        ((F R T a).extension.section ((tensor.{c, v, u} φ).obj X) n V 1
          (tensorSection.{c, v, u} φ X n V t x)))) :
    f = g := by
  apply towerComp_ext.{c, v, u} L R T U a c' ((tensor.{c, v, u} φ).obj X)
  intro n V z
  let f' := (chainEmbedding.{c, v, u} (F R T a).extension).app ((tensor.{c, v, u} φ).obj X) ≫
    (restriction.{c, v, u} a).map
      ((chainEmbedding.{c, v, u} (F T U c').extension).app
        ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X)) ≫
        (restriction.{c, v, u} c').map f)
  let g' := (chainEmbedding.{c, v, u} (F R T a).extension).app ((tensor.{c, v, u} φ).obj X) ≫
    (restriction.{c, v, u} a).map
      ((chainEmbedding.{c, v, u} (F T U c').extension).app
        ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X)) ≫
        (restriction.{c, v, u} c').map g)
  have hh : f' = g' := by
    apply tensor_hom_ext.{c, v, u} φ X
    intro k W t x
    change (f.f k).val.app W
        ((((chainEmbedding.{c, v, u} (F T U c').extension).app
          ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X))).f k).val.app W
            ((((chainEmbedding.{c, v, u} (F R T a).extension).app
              ((tensor.{c, v, u} φ).obj X)).f k).val.app W
                (tensorSection.{c, v, u} φ X k W t x))) =
      (g.f k).val.app W
        ((((chainEmbedding.{c, v, u} (F T U c').extension).app
          ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X))).f k).val.app W
            ((((chainEmbedding.{c, v, u} (F R T a).extension).app
              ((tensor.{c, v, u} φ).obj X)).f k).val.app W
                (tensorSection.{c, v, u} φ X k W t x)))
    rw [chainEmbedding_pure.{c, v, u}, chainEmbedding_pure.{c, v, u}]
    exact hfg k W t x
  have hv := congrArg (fun k ↦ (k.f n).val.app V z) hh
  change (f.f n).val.app V
      ((((chainEmbedding.{c, v, u} (F T U c').extension).app
        ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X))).f n).val.app V
          ((((chainEmbedding.{c, v, u} (F R T a).extension).app
            ((tensor.{c, v, u} φ).obj X)).f n).val.app V z)) =
    (g.f n).val.app V
      ((((chainEmbedding.{c, v, u} (F T U c').extension).app
        ((F R T a).extension.complex.obj ((tensor.{c, v, u} φ).obj X))).f n).val.app V
          ((((chainEmbedding.{c, v, u} (F R T a).extension).app
            ((tensor.{c, v, u} φ).obj X)).f n).val.app V z)) at hv
  rw [chainEmbedding_pure.{c, v, u}, chainEmbedding_pure.{c, v, u}] at hv
  exact hv

end


section
variable {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
  NormalizedCoefficientMaps.{c, v, u} φ}
  (L : CoefficientExtensionAssociators.{c, v, u} F)
  (Q : CoefficientChainSquares.{c, v, u} F)


private theorem pasting_kappa_id :
    CoefficientChainPasting.kappa_id_law L Q := by
  intro R S φ h X
  apply towerComp_ext.{c, v, u} L R S S φ (𝟙 S) X
  intro n V x
  change (((F R S φ).extension.complex.map (((L.unit R).app X).hom)).f n).val.app V
      (((((Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).extensionIso.app X).hom.f n).val.app V)
        ((F S S (𝟙 S)).extension.section ((F R S φ).extension.complex.obj X) n V 1
          ((F R S φ).extension.section X n V 1 x))) = _
  rw [(Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).extensionIso_pure,
    map_one, mul_one, extension_map_section_generic.{c, v, u}, L.unit_pure,
    L.unit_pure, one_smul, one_smul]
  rfl

private theorem pasting_mu_id :
    CoefficientChainPasting.mu_id_law L Q := by
  intro R S φ h N
  apply extension_hom_ext.{c, v, u} (F R R (𝟙 R)).extension
  intro n V z
  change (((L.unit S).app N).hom.f n).val.app V
      ((((Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).restrictionMate.app N).f n).val.app V
        ((F R R (𝟙 R)).extension.section ((restriction.{c, v, u} φ).obj N) n V 1 z)) = _
  rw [(Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).restrictionMate_pure,
    map_one, L.unit_pure, L.unit_pure]
  simp only [one_smul]

private theorem pasting_tau_id :
    CoefficientChainPasting.tau_id_law L Q := by
  intro R S φ h X
  apply extension_hom_ext.{c, v, u} (F R R (𝟙 R)).extension
  intro n V z
  let f := (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).tensorComparison X ≫
    (tensor.{c, v, u} φ).map (((L.unit R).app X).hom)
  let g := ((L.unit R).app ((tensor.{c, v, u} φ).obj X)).hom
  have hh : (chainEmbedding.{c, v, u} (F R R (𝟙 R)).extension).app
      ((tensor.{c, v, u} φ).obj X) ≫ (restriction.{c, v, u} (𝟙 R)).map f =
      (chainEmbedding.{c, v, u} (F R R (𝟙 R)).extension).app
        ((tensor.{c, v, u} φ).obj X) ≫ (restriction.{c, v, u} (𝟙 R)).map g := by
    apply tensor_hom_ext.{c, v, u} φ X
    intro k W t x
    change (f.f k).val.app W
        ((((chainEmbedding.{c, v, u} (F R R (𝟙 R)).extension).app
          ((tensor.{c, v, u} φ).obj X)).f k).val.app W
          (tensorSection.{c, v, u} φ X k W t x)) =
      (g.f k).val.app W
        ((((chainEmbedding.{c, v, u} (F R R (𝟙 R)).extension).app
          ((tensor.{c, v, u} φ).obj X)).f k).val.app W
          (tensorSection.{c, v, u} φ X k W t x))
    rw [chainEmbedding_pure.{c, v, u}]
    dsimp only [f, g]
    change (((tensor.{c, v, u} φ).map (((L.unit R).app X).hom)).f k).val.app W
        ((((Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).tensorComparison X).f k).val.app W
          ((F R R (𝟙 R)).extension.section ((tensor.{c, v, u} φ).obj X) k W 1
            (tensorSection.{c, v, u} φ X k W t x))) = _
    rw [(Q.compatible R S R S φ (𝟙 R) (𝟙 S) φ h).tensor_pure,
      tensor_map_section.{c, v, u}, L.unit_pure, L.unit_pure]
    simp only [map_one, one_mul, one_smul]
    rfl
  have hv := congrArg (fun t ↦ (t.f n).val.app V z) hh
  change (f.f n).val.app V
      ((((chainEmbedding.{c, v, u} (F R R (𝟙 R)).extension).app
        ((tensor.{c, v, u} φ).obj X)).f n).val.app V z) =
    (g.f n).val.app V
      ((((chainEmbedding.{c, v, u} (F R R (𝟙 R)).extension).app
        ((tensor.{c, v, u} φ).obj X)).f n).val.app V z) at hv
  rw [chainEmbedding_pure.{c, v, u}] at hv
  exact hv

private theorem pasting_kappa_comp :
    CoefficientChainPasting.kappa_comp_law L Q := by
  intro R S R' S' R'' S'' φ a b φ' c' d φ'' h h' hh X
  apply towerCompThree_ext.{c, v, u} L R S S' S'' φ b d X
  intro n V x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [extension_map_section_generic.{c, v, u},
    (Q.square R S R' S' φ a b φ' h).extensionIso_pure,
    (Q.square R' S' R'' S'' φ' c' d φ'' h').extensionIso_pure,
    L.comp_pure,
    (Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).extensionIso_pure,
    extension_map_section_generic.{c, v, u}, L.comp_inv]
  simp only [map_one, mul_one]
  rfl

private theorem pasting_mu_comp :
    CoefficientChainPasting.mu_comp_law L Q := by
  intro R S R' S' R'' S'' φ a b φ' c' d φ'' h h' hh N
  apply towerComp_ext.{c, v, u} L R R' R'' a c' ((restriction.{c, v, u} φ).obj N)
  intro n V z
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [extension_map_section_generic.{c, v, u},
    (Q.square R S R' S' φ a b φ' h).restrictionMate_pure,
    (Q.square R' S' R'' S'' φ' c' d φ'' h').restrictionMate_pure,
    L.comp_pure,
    (Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).restrictionMate_pure,
    L.comp_inv]
  simp only [map_one, mul_one]

private theorem pasting_tau_comp :
    CoefficientChainPasting.tau_comp_law L Q := by
  intro R S R' S' R'' S'' φ a b φ' c' d φ'' h h' hh X
  apply towerTensor_hom_ext.{c, v, u} L a c' X
  intro n V t x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [extension_map_section_generic.{c, v, u},
    (Q.compatible R S R' S' φ a b φ' h).tensor_pure,
    (Q.compatible R' S' R'' S'' φ' c' d φ'' h').tensor_pure,
    L.comp_pure,
    (Q.compatible R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).tensor_pure,
    tensor_map_section.{c, v, u}, L.comp_inv]
  simp only [map_one, one_mul, mul_one]
  rfl

private theorem coefficientPasting : CoefficientChainPasting L Q where
  kappa_id := pasting_kappa_id L Q
  mu_id := pasting_mu_id L Q
  tau_id := pasting_tau_id L Q
  kappa_comp := pasting_kappa_comp L Q
  mu_comp := pasting_mu_comp L Q
  tau_comp := pasting_tau_comp L Q

end

section
variable {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
  NormalizedCoefficientMaps.{c, v, u} φ}
  (L : CoefficientExtensionAssociators.{c, v, u} F)

private theorem iteration_associativity :
    CoefficientHomIteration.associativity_law L := by
  intro R S T V φ ψ ξ X
  apply towerCompThree_ext.{c, v, u} L R S T V φ ψ ξ X
  intro n W x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [extension_map_section_generic.{c, v, u}, L.comp_pure, L.comp_pure,
    L.comp_pure, L.comp_pure]
  simp only [map_one, mul_one]
  exact (transport_section.{c, v, u} F (Category.assoc φ ψ ξ).symm X n W 1 x).symm

private theorem iteration_left_unit :
    CoefficientHomIteration.left_unit_law L := by
  intro R S φ X
  apply towerComp_ext.{c, v, u} L R R S (𝟙 R) φ X
  intro n V x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [L.comp_pure, extension_map_section_generic.{c, v, u}, L.unit_pure]
  simp only [map_one, mul_one, one_smul]
  exact transport_section.{c, v, u} F (Category.id_comp φ) X n V 1 x

private theorem iteration_right_unit :
    CoefficientHomIteration.right_unit_law L := by
  intro R S φ X
  apply towerComp_ext.{c, v, u} L R S S φ (𝟙 S) X
  intro n V x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [L.comp_pure, L.unit_pure]
  simp only [map_one, mul_one, one_smul]
  exact transport_section.{c, v, u} F (Category.comp_id φ) X n V 1 x

private theorem iteration_nu_id :
    CoefficientHomIteration.nu_id_law L := by
  intro R X
  apply tensor_hom_ext.{c, v, u} (𝟙 R) X X
  intro n V r x
  change ((((L.resUnit R).app X).hom.f n).val.app V)
    (((((L.unit R).app X).hom.f n).val.app V)
      (((((F R R (𝟙 R)).chains.nu.app X).hom.f n).val.app V)
        (tensorSection.{c, v, u} (𝟙 R) X n V r x))) = _
  rw [(F R R (𝟙 R)).chains.nu_pure, L.unit_pure, L.resUnit_pure,
    L.tensorUnit_pure]

private theorem iteration_chi_id :
    CoefficientHomIteration.chi_id_law L := by
  intro R P A
  apply (cancel_epi (((L.unit R).app (homComplex (R := R) P A)).inv)).mp
  apply HomologicalComplex.hom_ext
  intro n
  apply evaluate_hom_ext.{c, v, u} P A n
  intro i k hik V f x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [L.unit_inv]
  rw [evaluate_homMap.{c, v, u}, L.unit_inv, dataChi_unit.{c, v, u},
    L.unit_pure, L.unit_pure, one_smul, one_smul]

private theorem iteration_theta_id :
    CoefficientHomIteration.theta_id_law L := by
  intro R P N
  apply HomologicalComplex.hom_ext
  intro n
  apply evaluate_hom_ext.{c, v, u} P N n
  intro i k hik V f x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have hl := evaluate_homMap.{c, v, u} (𝟙 P) (((L.resUnit R).app N).hom)
    n i k hik V ((((F R R (𝟙 R)).chains.theta P N).hom.f n).val.app V f) x
  have hr := evaluate_homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N)
    n i k hik V
    ((((L.resUnit R).app
      (homComplex (R := R) ((F R R (𝟙 R)).extension.complex.obj P) N)).hom.f n).val.app V f) x
  refine hl.trans ((L.resUnit_pure R N k V _).trans ?_)
  refine ((F R R (𝟙 R)).chains.theta_forward P N n i k hik V f x).trans ?_
  refine (congrArg (fun z ↦ evaluate.{c, v, u}
    ((F R R (𝟙 R)).extension.complex.obj P) N n i k hik V f z)
    (L.unit_inv R P i V x)).symm.trans ?_
  refine Eq.trans ?_ hr.symm
  exact (congrArg (fun z ↦ evaluate.{c, v, u}
    ((F R R (𝟙 R)).extension.complex.obj P) N n i k hik V z
      ((((L.unit R).app P).inv.f i).val.app V x))
    (L.resUnit_pure R
      (homComplex (R := R) ((F R R (𝟙 R)).extension.complex.obj P) N) n V f)).symm

private theorem iteration_alpha_id :
    CoefficientHomIteration.alpha_id_law L := by
  intro R P A
  apply HomologicalComplex.hom_ext
  intro n
  apply tensorModuleHom_ext.{c, v, u} (𝟙 R)
  intro i k hik V r f x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [evaluate_homMap.{c, v, u}, (F R R (𝟙 R)).alpha_evaluate, L.tensorUnit_pure,
    L.tensorUnit_pure]
  change r • evaluate.{c, v, u} P A n i k hik V f x =
    evaluate.{c, v, u} P A n i k hik V (r • f) x
  rw [evaluate_smul_local.{c, v, u}]

private theorem iteration_sigma_id :
    CoefficientHomIteration.sigma_id_law L := by
  intro R P A N q
  apply (cancel_epi (((L.unit R).app (homComplex (R := R) P A)).inv)).mp
  apply HomologicalComplex.hom_ext
  intro n
  apply evaluate_hom_ext.{c, v, u} P N n
  intro i k hik V f x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [L.unit_inv]
  rw [evaluate_homMap.{c, v, u}, L.unit_inv, dataSigma_unit.{c, v, u}, L.unit_pure, one_smul,
    evaluate_homMap.{c, v, u}]
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [L.unit_inv]
  rfl

private theorem iteration_nu_comp :
    CoefficientHomIteration.nu_comp_law L := by
  intro R S T φ ψ X
  unfold CoefficientExtensionAssociators.underlyingComp
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, Category.comp_id]

private theorem iteration_chi_comp :
    CoefficientHomIteration.chi_comp_law L := by
  intro R S T φ ψ P A
  apply directHom_tower_ext.{c, v, u} L φ ψ (homComplex P A) P
  intro n i k hik V f x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [evaluate_homMap.{c, v, u}, L.comp_inv, extension_map_section_generic.{c, v, u},
    dataChi_unit.{c, v, u}, dataChi_unit.{c, v, u}, L.comp_pure, L.comp_pure]
  simp only [map_one, mul_one]
  rw [dataChi_unit.{c, v, u}]

private theorem iteration_theta_comp :
    CoefficientHomIteration.theta_comp_law L := by
  intro R S T φ ψ P N
  apply HomologicalComplex.hom_ext
  intro n
  apply evaluate_hom_ext.{c, v, u}
  intro i k hik V f x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  let y := ((((F S T ψ).chains.theta ((F R S φ).extension.complex.obj P) N).hom.f n).val.app V f)
  let z := ((((F R S φ).chains.theta P ((restriction.{c, v, u} ψ).obj N)).hom.f n).val.app V y)
  let w := ((((L.resComp R S T φ ψ).app
    (homComplex (R := T) ((F S T ψ).extension.complex.obj
      ((F R S φ).extension.complex.obj P)) N)).hom.f n).val.app V f)
  let x' := (F R S φ).extension.section P i V 1 x
  let x'' := (F S T ψ).extension.section ((F R S φ).extension.complex.obj P) i V 1 x'
  have hl := evaluate_homMap.{c, v, u} (𝟙 P) (((L.resComp R S T φ ψ).app N).hom)
    n i k hik V z x
  have ht := (F R S φ).chains.theta_forward P ((restriction.{c, v, u} ψ).obj N)
    n i k hik V y x
  have hu := (F S T ψ).chains.theta_forward ((F R S φ).extension.complex.obj P) N
    n i k hik V f x'
  have hr := (F R T (φ ≫ ψ)).chains.theta_forward P N n i k hik V
    (((homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N)).f n).val.app V w) x
  have hv := evaluate_homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N)
    n i k hik V w ((F R T (φ ≫ ψ)).extension.section P i V 1 x)
  have hx := L.comp_inv R S T φ ψ P i V 1 x
  have hw := L.resComp_pure R S T φ ψ
    (homComplex (R := T) ((F S T ψ).extension.complex.obj
      ((F R S φ).extension.complex.obj P)) N) n V f
  refine (hl.trans ((L.resComp_pure R S T φ ψ N k V _).trans (ht.trans hu))).trans ?_
  refine Eq.trans ?_ hr.symm
  refine Eq.trans ?_ hv.symm
  change evaluate.{c, v, u} _ N n i k hik V f x'' =
    evaluate.{c, v, u} _ N n i k hik V w
      (((((L.comp R S T φ ψ).app P).inv.f i).val.app V)
        ((F R T (φ ≫ ψ)).extension.section P i V 1 x))
  rw [hx]
  exact (congrArg (fun t ↦ evaluate.{c, v, u} _ N n i k hik V t x'') hw).symm

private theorem iteration_alpha_comp :
    CoefficientHomIteration.alpha_comp_law L := by
  intro R S T φ ψ P A
  apply HomologicalComplex.hom_ext
  intro n
  apply tensorModuleHom_ext.{c, v, u} (φ ≫ ψ)
  intro i k hik V t f x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [evaluate_homMap.{c, v, u}, (F R T (φ ≫ ψ)).alpha_evaluate,
    underlyingComp_pure.{c, v, u}, underlyingComp_pure.{c, v, u}]
  change tensorSection.{c, v, u} ψ ((F R S φ).extension.complex.obj A) k V t
      ((F R S φ).extension.section A k V 1 (evaluate.{c, v, u} P A n i k hik V f x)) =
    evaluate.{c, v, u} P
      ((restriction.{c, v, u} φ).obj
        ((tensor.{c, v, u} ψ).obj ((F R S φ).extension.complex.obj A))) n i k hik V
      (((((F R S φ).chains.theta P
        ((tensor.{c, v, u} ψ).obj ((F R S φ).extension.complex.obj A))).hom.f n).val.app V)
        (((((F S T ψ).alpha ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A)).f n).val.app V)
          (((((tensor.{c, v, u} ψ).map ((F R S φ).homComparison P A)).f n).val.app V)
            (tensorSection.{c, v, u} ψ ((F R S φ).extension.complex.obj (homComplex P A))
              n V t ((F R S φ).extension.section (homComplex P A) n V 1 f))))) x
  rw [tensor_map_section.{c, v, u}, (F R S φ).chains.theta_forward,
    (F S T ψ).alpha_evaluate, dataChi_unit.{c, v, u}]


private theorem iteration_sigma_comp :
    CoefficientHomIteration.sigma_comp_law L := by
  intro R S T φ ψ P A N q
  apply directHom_tower_ext.{c, v, u} L φ ψ (homComplex P A) P
  intro n i k hik V f x
  simp only [HomologicalComplex.comp_f, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [evaluate_homMap.{c, v, u}, L.comp_inv, extension_map_section_generic.{c, v, u},
    dataSigma_unit.{c, v, u}, dataChi_unit.{c, v, u}, L.comp_pure]
  simp only [map_one, mul_one]
  rw [dataSigma_unit.{c, v, u}]
  change _ = (q.f k).val.app V
    (((((L.comp R S T φ ψ).app A).inv.f k).val.app V)
      ((F R T (φ ≫ ψ)).extension.section A k V 1
        (evaluate.{c, v, u} P A n i k hik V f x)))
  rw [L.comp_inv]
  rfl

private theorem coefficientIteration : CoefficientHomIteration L where
  associativity := iteration_associativity L
  left_unit := iteration_left_unit L
  right_unit := iteration_right_unit L
  nu_id := iteration_nu_id L
  chi_id := iteration_chi_id L
  theta_id := iteration_theta_id L
  alpha_id := iteration_alpha_id L
  sigma_id := iteration_sigma_id L
  nu_comp := iteration_nu_comp L
  chi_comp := iteration_chi_comp L
  theta_comp := iteration_theta_comp L
  alpha_comp := iteration_alpha_comp L
  sigma_comp := iteration_sigma_comp L

end


/-- Normalized coefficient-square coherence of actual sheaf Hom chain maps.
Source: Stacks Project, sites-modules.tex, Tags 03CY and 03CZ;
sites-cohomology.tex, Tag 0A8X
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence).

Proof, following the node:
1. On every slice use the tensor universal property
   (def-weil-pbc-module-tensor-product) and module sheafification
   (def-weil-presheaf-modules-sheafification) to construct and compare maps on
   nested tensor generators. For Hom-valued maps test every product coordinate
   (def-pur-hom-complex) and every further slice (def-pur-sheaf-hom).
2. Define kappa by multiplying the outer scalar with b(s); its inverse multiplies
   by phi'(r') and inserts 1. The commuting square gives inner R-balance;
   the outer balances use multiplication. The composites are identities by
   tensor balance. Substitution of dx and h(x) gives the chain and naturality laws.
3. Define mu(r' tensor z) = phi'(r') tensor z and
   tau(r' tensor (s tensor x)) = phi'(r')b(s) tensor (1 tensor x).
   The coefficient square gives both R-balances; these formulas are R'-linear,
   commute with restriction and differentials, and are natural in the last input.
4. For nu, both coefficient paths give phi'(r')b(s) tensor (1 tensor x),
   using lem-sfb-slice-scalar-hom-chain-adjunction.
5. For theta, evaluate a degree-n family at r'' tensor p in coordinate i.
   Both sides give phi'(r'r'') tensor g(1 tensor p). On the right kappa inverse
   sends 1 tensor (r'' tensor p) to phi'(r'') tensor (1 tensor p).
6. For alpha, evaluate at r'' tensor p. Both sides give
   phi'(r'r'')b(s) tensor (1 tensor f(p)); use R'-balance on the right.
7. For sigma, the two values are s't'phi'(r'')b(s) times
   w(1 tensor q(1 tensor f(p))) and the same scalar times
   q'(1 tensor (1 tensor f(p))). The assumed equation kappa_J;q' = B(q);w
   identifies the last factors. Steps 5--7 use the normalized evaluations of
   lem-sfb-scalar-hom-chain-evaluation; step 1 promotes them to chain equalities.
8. For successive u and v contract m tensor (l tensor x) to mv(l) tensor x,
   with inverse m tensor x mapping to m tensor (1 tensor x). For the identity
   use r tensor x mapping to rx with inverse x mapping to 1 tensor x.
   Tensor balance proves inverse, unit and associativity equations.
9. For two squares both kappa paths give s''d(s')db(s) tensor
   (1 tensor (1 tensor x)); both mu paths give phi''(r''c(r')) tensor z;
   both tau paths give phi''(r''c(r'))db(s) tensor (1 tensor (1 tensor x)).
   Identity squares give identity maps through the unit identifications.
10. Successive chi, tested on m tensor (l tensor f) at t tensor (s tensor p),
    evaluates to mt v(ls) tensor f(p), the direct value. Successive theta
    evaluates at 1 tensor (1 tensor p), the contracted unit. Alpha gives
    m tensor (l tensor f(p)), contracting to mv(l) tensor f(p). Nu preserves
    the same generators. Sigma at an arbitrary q has the same scalar product;
    the extension associator transports its source and target maps.
11. Apply the four coefficient equalities successively; steps 8--10 identify
    their maps and every intervening comparison with the direct square.
    Associativity and unit coherence make all pasted equations agree, including
    the identity square. All tensor maps are sheafification-unit images, and
    arbitrary product families are used, without finite support, flatness,
    boundedness, or invertibility of chi. Arbitrary compatible semilinear
    target changes are included through their induced map w. -/
theorem exists_scalarHomChainCoefficientCoherence
    (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ) :
    ∃ L : CoefficientExtensionAssociators.{c, v, u} F,
    ∃ Q : CoefficientChainSquares.{c, v, u} F,
      CoefficientChainPasting.{c, v, u} L Q ∧ CoefficientHomIteration.{c, v, u} L := by
  obtain ⟨Q⟩ := squares_exists.{c, v, u} F
  let L := familyAssociators.{c, v, u} F
  exact ⟨L, Q, coefficientPasting L Q, coefficientIteration L⟩

end SheafOfModules.StrictScalarHom
