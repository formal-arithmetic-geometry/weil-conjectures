/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction
public import Sheaf.Algebra.Homology.ScalarHomChainEvaluation
import Mathlib.LinearAlgebra.TensorProduct.Defs

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
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.StrictScalarHom

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection tensorSection evaluate homMap

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
  tensor_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R'.obj.obj V) (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((Q.tensorComparison A).f n).val.app V)
        (Da.extension.section ((tensor.{c, v, u} φ).obj A) n V r
          (tensorSection.{c, v, u} φ A n V s x)) =
      tensorSection.{c, v, u} φ' (Da.extension.complex.obj A) n V
        (φ'.hom.app V r * b.hom.app V s) (Da.extension.section A n V 1 x)
  /-- Nu commutes with the canonical coefficient maps. -/
  nu : ∀ (A : Complex.{c, v, u} R),
    Q.tensorComparison A ≫ (D'.chains.nu.app (Da.extension.complex.obj A)).hom =
      Da.extension.complex.map (D.chains.nu.app A).hom ≫
        Q.restrictionMate.app (D.extension.complex.obj A) ≫
        (restriction.{c, v, u} φ').map (Q.extensionIso.app A).hom
  /-- Theta commutes with the canonical Hom comparisons and the restriction mate. -/
  theta : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    Da.extension.complex.map (D.chains.theta P N).hom ≫
        Da.homComparison P ((restriction.{c, v, u} φ).obj N) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.restrictionMate.app N) =
      Q.restrictionMate.app (homComplex (R := S) (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (Db.homComparison (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (homMap.{c, v, u} (Q.extensionIso.app P).inv
          (𝟙 (Db.extension.complex.obj N))) ≫
        (D'.chains.theta (Da.extension.complex.obj P) (Db.extension.complex.obj N)).hom
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
  /-- The inverse inserts the unit. -/
  unit_inv : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((unit R).app X).inv.f n).val.app V) x =
      (F R R (𝟙 R)).extension.section X n V 1 x
  /-- Restriction along the identity is the identity functor. -/
  resUnit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    restriction.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R)
  /-- The restriction unit leaves every section unchanged. -/
  resUnit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((resUnit R).app X).hom.f n).val.app V) x = x
  /-- The inverse restriction unit leaves every section unchanged. -/
  resUnit_inv : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((resUnit R).app X).inv.f n).val.app V) x = x
  /-- The ordinary R-linear tensor unit identification. -/
  tensorUnit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    tensor.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R)
  /-- The tensor unit contracts r tensor x to rx. -/
  tensorUnit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (X.X n).val.obj V),
    ((((tensorUnit R).app X).hom.f n).val.app V)
        (tensorSection.{c, v, u} (𝟙 R) X n V r x) = r • x
  /-- Its inverse inserts the unit of R. -/
  tensorUnit_inv : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((tensorUnit R).app X).inv.f n).val.app V) x =
      tensorSection.{c, v, u} (𝟙 R) X n V 1 x
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
  /-- The inverse contraction inserts a unit in the inner extension. -/
  comp_inv : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : T.obj.obj V) (x : (X.X n).val.obj V),
    ((((comp R S T φ ψ).app X).inv.f n).val.app V)
        ((F R T (φ ≫ ψ)).extension.section X n V t x) =
      (F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
        ((F R S φ).extension.section X n V 1 x)
  /-- Restriction along a composite agrees with successive restriction. -/
  resComp : ∀ (R S T : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S) (ψ : S ⟶ T),
    restriction.{c, v, u} ψ ⋙ restriction.{c, v, u} φ ≅ restriction.{c, v, u} (φ ≫ ψ)
  /-- This restriction identification is the identity on sections. -/
  resComp_pure : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (N : Complex.{c, v, u} T)
    (n : ℤ) (V : Cᵒᵖ) (x : (N.X n).val.obj V),
    ((((resComp R S T φ ψ).app N).hom.f n).val.app V) x = x
  /-- The inverse restriction identification is also the identity on sections. -/
  resComp_inv : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (N : Complex.{c, v, u} T)
    (n : ℤ) (V : Cᵒᵖ) (x : (N.X n).val.obj V),
    ((((resComp R S T φ ψ).app N).inv.f n).val.app V) x = x

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

/-- Identity coefficient squares and pasted coefficient squares give the same maps.
Source: Stacks 03CY, 03CZ and 0A8X, node proof steps 8--11
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientChainPasting
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop where
  /-- Kappa is the identity after the unit identifications. -/
  kappa_id : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (X : Complex.{c, v, u} R),
    ((Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).extensionIso.app X).hom ≫
        (F R S φ).extension.complex.map (((L.unit R).app X).hom) =
      ((L.unit S).app ((F R S φ).extension.complex.obj X)).hom
  /-- Mu is the identity after the unit identifications. -/
  mu_id : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (N : Complex.{c, v, u} S),
    (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).restrictionMate.app N ≫
        (restriction.{c, v, u} φ).map (((L.unit S).app N).hom) =
      ((L.unit R).app ((restriction.{c, v, u} φ).obj N)).hom
  /-- Tau is the identity after the unit identifications. -/
  tau_id : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (X : Complex.{c, v, u} R),
    (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).tensorComparison X ≫
        (tensor.{c, v, u} φ).map (((L.unit R).app X).hom) =
      ((L.unit R).app ((tensor.{c, v, u} φ).obj X)).hom
  /-- Kappa for a pasted square is successive kappa, transported by associators. -/
  kappa_comp : ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
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
  /-- Mu for a pasted square is successive mu, with restriction of the associator. -/
  mu_comp : ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
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
  /-- Tau for a pasted square is successive tau, transported by associators. -/
  tau_comp : ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
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

/-- Composition of the supplied normalized maps is direct scalar change.
Source: Stacks 03CY, 03CZ and 0A8X, node proof steps 8 and 10
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientHomIteration
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop where
  /-- Both contractions of three scalar extensions agree. -/
  associativity : ∀ (R S T V : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (ξ : T ⟶ V) (X : Complex.{c, v, u} R),
    (F T V ξ).extension.complex.map (((L.comp R S T φ ψ).app X).hom) ≫
        ((L.comp R T V (φ ≫ ψ) ξ).app X).hom =
      ((L.comp S T V ψ ξ).app ((F R S φ).extension.complex.obj X)).hom ≫
        ((L.comp R S V φ (ψ ≫ ξ)).app X).hom ≫
        eqToHom (congrArg
          (fun f : R ⟶ V ↦ (F R V f).extension.complex.obj X)
          (Category.assoc φ ψ ξ).symm)
  /-- Inserting an identity extension before extension gives the same contraction. -/
  left_unit : ∀ (R S : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (X : Complex.{c, v, u} R),
    ((L.comp R R S (𝟙 R) φ).app X).hom ≫
        eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X)
          (Category.id_comp φ)) =
      (F R S φ).extension.complex.map (((L.unit R).app X).hom)
  /-- Inserting an identity extension after extension gives the same contraction. -/
  right_unit : ∀ (R S : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (X : Complex.{c, v, u} R),
    ((L.comp R S S φ (𝟙 S)).app X).hom ≫
        eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X)
          (Category.comp_id φ)) =
      ((L.unit S).app ((F R S φ).extension.complex.obj X)).hom
  /-- Nu for identity coefficients becomes the identity tensor identification. -/
  nu_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (X : Complex.{c, v, u} R),
    ((F R R (𝟙 R)).chains.nu.app X).hom ≫
        (restriction.{c, v, u} (𝟙 R)).map (((L.unit R).app X).hom) ≫
        ((L.resUnit R).app X).hom =
      ((L.tensorUnit R).app X).hom
  /-- Chi for identity coefficients becomes the identity Hom comparison. -/
  chi_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A : Complex.{c, v, u} R),
    (F R R (𝟙 R)).homComparison P A ≫
        homMap.{c, v, u} (((L.unit R).app P).inv) (((L.unit R).app A).hom) =
      ((L.unit R).app (homComplex (R := R) P A)).hom
  /-- Theta for identity coefficients is the identity after unit identifications. -/
  theta_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (P N : Complex.{c, v, u} R),
    ((F R R (𝟙 R)).chains.theta P N).hom ≫
        homMap.{c, v, u} (𝟙 P) (((L.resUnit R).app N).hom) =
      ((L.resUnit R).app
        (homComplex (R := R) ((F R R (𝟙 R)).extension.complex.obj P) N)).hom ≫
        homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N)
  /-- Alpha for identity coefficients is the identity after tensor unit contraction. -/
  alpha_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A : Complex.{c, v, u} R),
    (F R R (𝟙 R)).alpha P A ≫
        homMap.{c, v, u} (𝟙 P) (((L.tensorUnit R).app A).hom) =
      ((L.tensorUnit R).app (homComplex (R := R) P A)).hom
  /-- Sigma for identity coefficients is composition with its arbitrary target map. -/
  sigma_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A N : Complex.{c, v, u} R)
    (q : (F R R (𝟙 R)).extension.complex.obj A ⟶ N),
    (F R R (𝟙 R)).sigma P A N q ≫ homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N) =
      ((L.unit R).app (homComplex (R := R) P A)).hom ≫
        homMap.{c, v, u} (𝟙 P) ((((L.unit R).app A).inv) ≫ q)
  /-- Nu respects contraction of an iterated scalar tensor. -/
  nu_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R),
    L.underlyingComp φ ψ X ≫ (restriction.{c, v, u} φ).map
        (((F S T ψ).chains.nu.app ((F R S φ).extension.complex.obj X)).hom) =
      ((F R T (φ ≫ ψ)).chains.nu.app X).hom ≫
        ((L.resComp R S T φ ψ).app ((F R T (φ ≫ ψ)).extension.complex.obj X)).inv ≫
        (restriction.{c, v, u} φ).map
          ((restriction.{c, v, u} ψ).map (((L.comp R S T φ ψ).app X).inv))
  /-- Successive Hom comparisons contract to the direct Hom comparison. -/
  chi_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R),
    (F S T ψ).extension.complex.map ((F R S φ).homComparison P A) ≫
        (F S T ψ).homComparison ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A) ≫
        homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv)
          (((L.comp R S T φ ψ).app A).hom) =
      ((L.comp R S T φ ψ).app (homComplex (R := R) P A)).hom ≫
        (F R T (φ ≫ ψ)).homComparison P A
  /-- Successive adjunction maps evaluate at the same twice-inserted unit. -/
  theta_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
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
  /-- Alpha commutes with contraction of the iterated tensor and Hom evaluation. -/
  alpha_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
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
  /-- Successive sigma agrees for any target and any compatible chain map. -/
  sigma_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R)
    (N : Complex.{c, v, u} T)
    (q : (F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj A) ⟶ N),
    (F S T ψ).extension.complex.map ((F R S φ).homComparison P A) ≫
        (F S T ψ).sigma ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A) N q ≫
        homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N) =
      ((L.comp R S T φ ψ).app (homComplex (R := R) P A)).hom ≫
        (F R T (φ ≫ ψ)).sigma P A N ((((L.comp R S T φ ψ).app A).inv) ≫ q)

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
  sorry

end SheafOfModules.StrictScalarHom
