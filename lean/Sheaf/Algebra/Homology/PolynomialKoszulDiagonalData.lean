/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Normalized comparison data for polynomial Koszul diagonal classes

Source: Stacks Project, dualizing.tex, Tags 0E2E, 0A70, 0A71, 0BZI and 0BZJ;
the explicit graph construction in lem-sfb-polynomial-koszul-diagonal-class.
(blueprint: def-sfb-polynomial-koszul-diagonal-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The existing K-flat scalar-extension functor's evaluation-normalized adjunction.
Source: Stacks 08DW (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def koszulDiagonalExtensionAdjunction {P T : Type u} [CommRing P] [CommRing T]
    (f : P →+* T) :
    relativeDualizingDerivedExtension f ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory :=
  letI := ModuleCat.extendScalars_preservesKFlatQuasiIso f
  (ModuleCat.extendRestrictScalarsAdj f).derivedAdjunction.ofNatIsoRight
    (ModuleCat.restrictScalars f).rightDerivedFunctorIsoMapDerivedCategory

/-- Restriction around a commutative square, before taking its scalar-extension mate.
Source: Stacks 0A70 (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def koszulDiagonalRestrictionSquare {P B T D : Type u}
    [CommRing P] [CommRing B] [CommRing T] [CommRing D]
    (p : P →+* B) (g : P →+* T) (b : B →+* D) (q : T →+* D)
    (h : b.comp p = q.comp g) :
    (ModuleCat.restrictScalars b).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars p).mapDerivedCategory ≅
      (ModuleCat.restrictScalars q).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars g).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp p b)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ModuleCat.restrictScalarsComp' g q (b.comp p) h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The canonical scalar/restriction comparison is the mate of the restriction square.
Its invertibility is a conclusion in the Tor-independent situations, not an input.
Source: Stacks 0A71 (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def koszulDiagonalScalarMate {P B T D : Type u}
    [CommRing P] [CommRing B] [CommRing T] [CommRing D]
    (p : P →+* B) (g : P →+* T) (b : B →+* D) (q : T →+* D)
    (h : b.comp p = q.comp g) (N : DerivedCategory (ModuleCat.{u} B)) :
    (relativeDualizingDerivedExtension g).obj
        ((ModuleCat.restrictScalars p).mapDerivedCategory.obj N) ⟶
      (ModuleCat.restrictScalars q).mapDerivedCategory.obj
        ((relativeDualizingDerivedExtension b).obj N) :=
  (relativeDualizingDerivedExtension g).map
    ((ModuleCat.restrictScalars p).mapDerivedCategory.map
      ((koszulDiagonalExtensionAdjunction b).unit.app N)) ≫
    (relativeDualizingDerivedExtension g).map
      ((koszulDiagonalRestrictionSquare p g b q h).hom.app _) ≫
    (koszulDiagonalExtensionAdjunction g).counit.app _

/-- A polynomial algebra localized at one element (hence at any finite list), with a
surjective presentation of B. The localization is along the specified coordinate map.
Source: Stacks 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
structure PolynomialKoszulChart (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] where
  n : ℕ
  P : CommAlgCat.{u} R
  coordinates : MvPolynomial (Fin n) R →ₐ[R] P
  h : MvPolynomial (Fin n) R
  localized : @IsLocalization (MvPolynomial (Fin n) R) _ (Submonoid.powers h) P _
    coordinates.toRingHom.toAlgebra
  quotient : P →ₐ[R] B
  surjective : Function.Surjective quotient

/-- The top differential module of a localized chart, using the recorded exterior power.
Source: Stacks 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.top {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (C : PolynomialKoszulChart R B) : ModuleCat.{u} C.P :=
  ModuleCat.of C.P (⋀[C.P]^C.n (KaehlerDifferential R C.P))

/-- The image of the ordered polynomial volume, with the empty wedge when n=0.
Source: Stacks 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.volume {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (C : PolynomialKoszulChart R B) : C.top :=
  exteriorPower.ιMulti C.P C.n (fun i ↦
    KaehlerDifferential.D R C.P (C.coordinates (MvPolynomial.X i)))

/-- The actual top differential coefficient in degree -n.
Source: Stacks 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.coefficient {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    DerivedCategory (ModuleCat.{u} C.P) :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top)

/-- The localized polynomial coinduction model, retaining the precomposition action.
Source: Stacks 0A70 and 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.model {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    DerivedCategory (ModuleCat.{u} B) :=
  (ModuleCat.derivedCoinduction C.quotient.toRingHom).obj C.coefficient

/-- Its first diagonal pullback, with the first copy of B fixed.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.firstPullback {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    DerivedCategory (ModuleCat.{u} (B ⊗[R] B)) :=
  relativeDualizingModuleFirstPullback R B C.model

/-- The graph ring P tensor_R B_2 and its quotient onto the two-copy algebra.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphQuotient {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    (C.P ⊗[R] B) →+* (B ⊗[R] B) :=
  (Algebra.TensorProduct.map C.quotient (AlgHom.id R B)).toRingHom

/-- Evaluation at the graph x_i = bar x_i, with coefficient copy B_2.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphEvaluation {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    (C.P ⊗[R] B) →+* B :=
  (Algebra.TensorProduct.lmul' R (S := B)).toRingHom.comp C.graphQuotient

/-- The ordered graph equations, including localized polynomial presentations.
Source: Stacks 0622, 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphEquations {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    Fin C.n → C.P ⊗[R] B :=
  fun i ↦ C.coordinates (MvPolynomial.X i) ⊗ₜ[R] (1 : B) -
    (1 : C.P) ⊗ₜ[R] C.quotient (C.coordinates (MvPolynomial.X i))

/-- The ordered graph Koszul complex in degrees -n,...,0, from the shared construction.
Source: Stacks 0622, 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphKoszul {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    CochainComplex (ModuleCat.{u} (C.P ⊗[R] B)) ℤ :=
  (ExteriorAlgebra.koszulComplex _ C.n C.graphEquations).extend
    ComplexShape.embeddingDownNat

/-- A coefficient map's derived scalar mate, with the ordinary single-term normalization.
Source: Stacks 08DW, 0A71 (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def koszulDiagonalSingleMate {P T : Type u} [CommRing P] [CommRing T]
    (g : P →+* T) (i : ℤ) (M : ModuleCat.{u} P) (N : ModuleCat.{u} T)
    (ω : M ⟶ (ModuleCat.restrictScalars g).obj N) :
    (relativeDualizingDerivedExtension g).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ i).obj M)) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ i).obj N) :=
  ((koszulDiagonalExtensionAdjunction g).homEquiv _ _).symm
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ i).map ω) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.restrictScalars g) (.up ℤ) i).inv.app N) ≫
      (ModuleCat.restrictScalars g).mapDerivedCategoryFactors.inv.app _)

/-- The normalized comparison between two paths of derived scalar extension.
Source: Stacks 08DW (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def koszulDiagonalExtensionSquare {P B T D : Type u}
    [CommRing P] [CommRing B] [CommRing T] [CommRing D]
    (p : P →+* B) (g : P →+* T) (b : B →+* D) (q : T →+* D)
    (h : b.comp p = q.comp g) :
    relativeDualizingDerivedExtension p ⋙ relativeDualizingDerivedExtension b ≅
      relativeDualizingDerivedExtension g ⋙ relativeDualizingDerivedExtension q :=
  (((koszulDiagonalExtensionAdjunction p).comp
    (koszulDiagonalExtensionAdjunction b)).ofNatIsoRight
      (koszulDiagonalRestrictionSquare p g b q h)).leftAdjointUniq
        ((koszulDiagonalExtensionAdjunction g).comp
          (koszulDiagonalExtensionAdjunction q))

/-- Coinduction transitivity, uniquely fixed by the composite evaluation counit.
Source: Stacks 0A70 (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def koszulDiagonalCoinductionComp {P A B : Type u}
    [CommRing P] [CommRing A] [CommRing B] (q : P →+* A) (δ : A →+* B) :
    ModuleCat.derivedCoinduction q ⋙ ModuleCat.derivedCoinduction δ ≅
      ModuleCat.derivedCoinduction (δ.comp q) :=
  (((ModuleCat.derivedCoinductionAdjunction δ).comp
    (ModuleCat.derivedCoinductionAdjunction q)).ofNatIsoLeft
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp q δ) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).symm).rightAdjointUniq
          (ModuleCat.derivedCoinductionAdjunction (δ.comp q))

/-- The graph coefficient line is scalar extension of the ordered top differential line.
Differential base change identifies it with the top differentials over the second copy of B.
Source: Stacks 0E2E, 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphTop {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    ModuleCat.{u} (C.P ⊗[R] B) :=
  (ModuleCat.extendScalars
    (Algebra.TensorProduct.includeLeft : C.P →ₐ[R] C.P ⊗[R] B).toRingHom).obj C.top

/-- The scalar-extended ordered differential volume.
Source: Stacks 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphVolume {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) : C.graphTop :=
  ((ModuleCat.extendRestrictScalarsAdj
    (Algebra.TensorProduct.includeLeft : C.P →ₐ[R] C.P ⊗[R] B).toRingHom).unit.app
      C.top) C.volume

/-- The graph coefficient complex, in cohomological degree -n.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphCoefficientComplex {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    CochainComplex (ModuleCat.{u} (C.P ⊗[R] B)) ℤ :=
  (CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.graphTop

/-- The actual scalar-extension comparison on the graph coefficient line.
Source: Stacks 08DW (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphCoefficientMap {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    (relativeDualizingDerivedExtension
      (Algebra.TensorProduct.includeLeft : C.P →ₐ[R] C.P ⊗[R] B).toRingHom).obj
        C.coefficient ⟶ DerivedCategory.Q.obj C.graphCoefficientComplex :=
  koszulDiagonalSingleMate _ (-(C.n : ℤ)) C.top C.graphTop
    ((ModuleCat.extendRestrictScalarsAdj _).unit.app C.top)

/-- Ordered wedge in the graph Koszul term, transported through extension by zero.
Source: Stacks 0622 (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.graphWedge {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B)
    (k : ℕ) (v : Fin k → Fin C.n →₀ (C.P ⊗[R] B)) :
    C.graphKoszul.X (-(k : ℤ)) :=
  ((ExteriorAlgebra.koszulComplex _ C.n C.graphEquations).extendXIso
    ComplexShape.embeddingDownNat (i := k) rfl).inv
      (exteriorPower.ιMulti _ k v)

/-- The B-module in degree zero, before diagonal restriction.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def koszulDiagonalUnit (B : Type u) [CommRing B] : DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of B B))

/-- The top graph cocycle specifies the inverse trace. Its augmentation sends 1 to 1;
the cocycle sends the ordered top graph wedge to the ordered differential volume.
The equation is in D(T), using the actual evaluation counit. This fixes the trace,
including all standard cohomological signs, rather than an arbitrary generator.
Source: Stacks 0BZI, 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def IsKoszulDiagonalGraphTrace {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B)
    (τ : (ModuleCat.derivedCoinduction C.graphEvaluation).obj
      (DerivedCategory.Q.obj C.graphCoefficientComplex) ≅ koszulDiagonalUnit B) : Prop :=
  ∃ a : C.graphKoszul ⟶
      ((ModuleCat.restrictScalars C.graphEvaluation).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of B B)),
    QuasiIso a ∧
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of B B)).hom
      (a.f 0 (C.graphWedge 0 (fun i ↦ Fin.elim0 i))) = 1 ∧
    ∃ z : C.graphKoszul ⟶ C.graphCoefficientComplex,
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-(C.n : ℤ)) C.graphTop).hom
        (z.f (-(C.n : ℤ)) (C.graphWedge C.n (fun i ↦ Finsupp.single i 1))) =
          C.graphVolume ∧
      DerivedCategory.Q.map a ≫
        (ModuleCat.restrictScalars C.graphEvaluation).mapDerivedCategoryFactors.inv.app _ ≫
        (ModuleCat.restrictScalars C.graphEvaluation).mapDerivedCategory.map τ.inv ≫
        (ModuleCat.derivedCoinductionAdjunction C.graphEvaluation).counit.app _ =
          DerivedCategory.Q.map z

/-- The diagonal coinduction object with its B-action.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.diagonalHom {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    DerivedCategory (ModuleCat.{u} B) :=
  (ModuleCat.derivedCoinduction
    (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).obj C.firstPullback

/-- Graph exchange is fixed by the extended evaluation counit and the actual top form map.
Its composite with evaluation-normalized transitivity and the graph trace is kappa.
Source: Stacks 0A71, 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def IsKoszulDiagonalNormalization {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B)
    (κ : C.diagonalHom ≅ koszulDiagonalUnit B) : Prop :=
  ∃ β : C.firstPullback ≅ (ModuleCat.derivedCoinduction C.graphQuotient).obj
      (DerivedCategory.Q.obj C.graphCoefficientComplex),
    ∃ h : (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom.comp
        C.quotient.toRingHom = C.graphQuotient.comp
          (Algebra.TensorProduct.includeLeft : C.P →ₐ[R] C.P ⊗[R] B).toRingHom,
      IsIso C.graphCoefficientMap ∧
      IsIso (koszulDiagonalScalarMate C.quotient.toRingHom
        (Algebra.TensorProduct.includeLeft : C.P →ₐ[R] C.P ⊗[R] B).toRingHom
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom
        C.graphQuotient h C.model) ∧
      koszulDiagonalScalarMate C.quotient.toRingHom
          (Algebra.TensorProduct.includeLeft : C.P →ₐ[R] C.P ⊗[R] B).toRingHom
          (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom
          C.graphQuotient h C.model ≫
        (ModuleCat.restrictScalars C.graphQuotient).mapDerivedCategory.map β.hom ≫
        (ModuleCat.derivedCoinductionAdjunction C.graphQuotient).counit.app _ =
          (relativeDualizingDerivedExtension
            (Algebra.TensorProduct.includeLeft : C.P →ₐ[R] C.P ⊗[R] B).toRingHom).map
              ((ModuleCat.derivedCoinductionAdjunction C.quotient.toRingHom).counit.app
                C.coefficient) ≫ C.graphCoefficientMap ∧
      ∃ τ : (ModuleCat.derivedCoinduction C.graphEvaluation).obj
          (DerivedCategory.Q.obj C.graphCoefficientComplex) ≅ koszulDiagonalUnit B,
        IsKoszulDiagonalGraphTrace C τ ∧
        κ.hom = (ModuleCat.derivedCoinduction
          (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).map β.hom ≫
            (koszulDiagonalCoinductionComp (P := C.P ⊗[R] B) (A := B ⊗[R] B)
              (B := B) C.graphQuotient (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).hom.app
                (DerivedCategory.Q.obj C.graphCoefficientComplex) ≫ τ.hom

/-- The specified class is the adjunct of the inverse normalized diagonal isomorphism.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.diagonalClass {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B)
    (κ : C.diagonalHom ≅ koszulDiagonalUnit B) :
    relativeDualizingModuleDiagonal R B ⟶ C.firstPullback :=
  DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R (S := B)).toRingHom)
        (.up ℤ) 0).inv.app (ModuleCat.of B B)) ≫
  (ModuleCat.restrictScalars
    (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).mapDerivedCategoryFactors.inv.app
      ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of B B)) ≫
    ((ModuleCat.derivedCoinductionAdjunction
      (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).homEquiv
        (koszulDiagonalUnit B) C.firstPullback).symm κ.inv

/-- A change of polynomial charts, including its actual top differential map.
The coordinate equations and ordered-volume equation fix the coefficient map uniquely.
Source: Stacks 0E2E, 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
structure KoszulDiagonalChartChange {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart S D) where
  base : R →+* S
  ring : B →+* D
  ambient : C.P →+* E.P
  base_comm : ring.comp (algebraMap R B) = (algebraMap S D).comp base
  ambient_comm : ambient.comp (algebraMap R C.P) = (algebraMap S E.P).comp base
  quotient_comm : ring.comp C.quotient.toRingHom = E.quotient.toRingHom.comp ambient
  dimension : C.n = E.n
  coordinate : ∀ i : Fin C.n,
    ambient (C.coordinates (MvPolynomial.X i)) =
      E.coordinates (MvPolynomial.X (Fin.cast dimension i))
  differential : C.top ⟶ (ModuleCat.restrictScalars ambient).obj E.top
  volume : differential C.volume = E.volume

/-- Scalar extension or simultaneous localization. Both are pushouts on the presentation;
for scalar extension the base square is a pushout, and for simultaneous localization
both ambient and quotient localize the same element. Base localization is scalar extension.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalChartChange.IsAdmissible {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    {C : PolynomialKoszulChart R B} {E : PolynomialKoszulChart S D}
    (F : KoszulDiagonalChartChange C E) : Prop :=
  IsPushout (CommRingCat.ofHom C.quotient.toRingHom) (CommRingCat.ofHom F.ambient)
    (CommRingCat.ofHom F.ring) (CommRingCat.ofHom E.quotient.toRingHom) ∧
  (IsPushout (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom F.base)
    (CommRingCat.ofHom F.ring) (CommRingCat.ofHom (algebraMap S D)) ∨
    (Function.Bijective F.base ∧ ∃ h : C.P,
      @IsLocalization C.P _ (Submonoid.powers h) E.P _ F.ambient.toAlgebra ∧
      @IsLocalization B _ (Submonoid.powers (C.quotient h)) D _ F.ring.toAlgebra))

/-- The induced map of the two diagonal algebras, including both factors.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalChartChange.diagonalRing {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    {C : PolynomialKoszulChart R B} {E : PolynomialKoszulChart S D}
    (F : KoszulDiagonalChartChange C E) : (B ⊗[R] B) →+* (D ⊗[S] D) :=
  Algebra.TensorProduct.mapRingHom F.base F.ring F.ring F.base_comm F.base_comm

/-- The coefficient comparison for a change of charts is the scalar mate of its
ordered differential map, followed by the degree change induced by the equal dimensions.
Source: Stacks 08DW, 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalChartChange.coefficientMap {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    {C : PolynomialKoszulChart R B} {E : PolynomialKoszulChart S D}
    (F : KoszulDiagonalChartChange C E) :
    (relativeDualizingDerivedExtension F.ambient).obj C.coefficient ⟶ E.coefficient :=
  koszulDiagonalSingleMate F.ambient (-(C.n : ℤ)) C.top E.top F.differential ≫
    eqToHom (congrArg
      (fun n : ℕ ↦ DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} E.P) (-(n : ℤ))).obj E.top)) F.dimension)

/-- The coinduction exchange is specified by the extended evaluation counit.
Source: Stacks 0A71 (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalChartChange.IsComparison {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    {C : PolynomialKoszulChart R B} {E : PolynomialKoszulChart S D}
    (F : KoszulDiagonalChartChange C E)
    (c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model) : Prop :=
  IsIso F.coefficientMap ∧
    IsIso (koszulDiagonalScalarMate C.quotient.toRingHom F.ambient F.ring
      E.quotient.toRingHom F.quotient_comm C.model) ∧
    koszulDiagonalScalarMate C.quotient.toRingHom F.ambient F.ring
        E.quotient.toRingHom F.quotient_comm C.model ≫
      (ModuleCat.restrictScalars E.quotient.toRingHom).mapDerivedCategory.map c.hom ≫
      (ModuleCat.derivedCoinductionAdjunction E.quotient.toRingHom).counit.app _ =
        (relativeDualizingDerivedExtension F.ambient).map
          ((ModuleCat.derivedCoinductionAdjunction C.quotient.toRingHom).counit.app
            C.coefficient) ≫ F.coefficientMap

/-- The canonical comparison between extended first pullbacks; it is fixed by the
scalar-extension adjunctions, including the specified comparison c on the coefficient.
Source: Stacks 08DW, 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalChartChange.firstPullbackMap {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    {C : PolynomialKoszulChart R B} {E : PolynomialKoszulChart S D}
    (F : KoszulDiagonalChartChange C E)
    (h : F.diagonalRing.comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom =
      (Algebra.TensorProduct.includeLeft : D →ₐ[S] D ⊗[S] D).toRingHom.comp F.ring)
    (c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model) :
    (relativeDualizingDerivedExtension F.diagonalRing).obj C.firstPullback ⟶
      E.firstPullback :=
  (koszulDiagonalExtensionSquare
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom F.ring
    F.diagonalRing
    (Algebra.TensorProduct.includeLeft : D →ₐ[S] D ⊗[S] D).toRingHom h).hom.app C.model ≫
      (relativeDualizingDerivedExtension
        (Algebra.TensorProduct.includeLeft : D →ₐ[S] D ⊗[S] D).toRingHom).map c.hom

/-- A comparison of diagonal degree-zero objects is the scalar mate of b : B → D.
The formula on every element specifies the ordinary module map, before deriving.
Source: Stacks 08DW, 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalChartChange.IsDiagonalComparison {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    {C : PolynomialKoszulChart R B} {E : PolynomialKoszulChart S D}
    (F : KoszulDiagonalChartChange C E)
    (d : (relativeDualizingDerivedExtension F.diagonalRing).obj
      (relativeDualizingModuleDiagonal R B) ≅ relativeDualizingModuleDiagonal S D) : Prop :=
  ∃ ω : (ModuleCat.restrictScalars
      (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).obj (ModuleCat.of B B) ⟶
      (ModuleCat.restrictScalars F.diagonalRing).obj
        ((ModuleCat.restrictScalars
          (Algebra.TensorProduct.lmul' S (S := D)).toRingHom).obj (ModuleCat.of D D)),
    (∀ b : B, ω b = F.ring b) ∧
      d.hom = koszulDiagonalSingleMate F.diagonalRing 0 _ _ ω

/-- A scalar or localization comparison carries the normalized diagonal class.
Source: Stacks 0E2E and the explicit graph construction
(blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalChartChange.PreservesClass {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    {C : PolynomialKoszulChart R B} {E : PolynomialKoszulChart S D}
    (F : KoszulDiagonalChartChange C E)
    (κ : C.diagonalHom ≅ koszulDiagonalUnit B)
    (κE : E.diagonalHom ≅ koszulDiagonalUnit D)
    (c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model) : Prop :=
  ∃ h : F.diagonalRing.comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom =
      (Algebra.TensorProduct.includeLeft : D →ₐ[S] D ⊗[S] D).toRingHom.comp F.ring,
    IsIso (F.firstPullbackMap h c) ∧
    ∃ d : (relativeDualizingDerivedExtension F.diagonalRing).obj
        (relativeDualizingModuleDiagonal R B) ≅ relativeDualizingModuleDiagonal S D,
      F.IsDiagonalComparison d ∧
      (relativeDualizingDerivedExtension F.diagonalRing).map (C.diagonalClass κ) ≫
        F.firstPullbackMap h c = d.hom ≫ E.diagonalClass κE

/-- Identify the single-term coefficient with Omega^n[n] by the standard shift comparison.
Source: Stacks 0BZI (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def PolynomialKoszulChart.coefficientShiftIso {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (C : PolynomialKoszulChart R B) :
    ((DerivedCategory.singleFunctor _ 0).obj C.top)⟦(C.n : ℤ)⟧ ≅ C.coefficient :=
  (DerivedCategory.singleFunctors (ModuleCat.{u} C.P)).shiftIso
    (C.n : ℤ) (-(C.n : ℤ)) 0 (add_neg_cancel _) |>.app C.top

/-- Add one polynomial lastVariable, with its old-coordinate inclusion and evaluation at a lift.
The displayed polynomial equivalence ensures this is precisely P[t], not another extension.
Source: Stacks 0BZJ (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
structure KoszulDiagonalRefinement {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    (C E : PolynomialKoszulChart R B) where
  dimension : E.n = C.n + 1
  inclusion : C.P →ₐ[R] E.P
  evaluation : E.P →ₐ[R] C.P
  lift : C.P
  lastVariable : E.P
  polynomial : E.P ≃+* Polynomial C.P
  polynomial_old : ∀ p : C.P, polynomial (inclusion p) = Polynomial.C p
  polynomial_new : polynomial lastVariable = Polynomial.X
  evaluation_old : evaluation.comp inclusion = AlgHom.id R C.P
  evaluation_new : evaluation lastVariable = lift
  quotient : C.quotient.comp evaluation = E.quotient
  coordinates_old : ∀ i : Fin C.n,
    E.coordinates (MvPolynomial.X (Fin.cast dimension.symm i.castSucc)) =
      inclusion (C.coordinates (MvPolynomial.X i))
  coordinates_new : E.coordinates
    (MvPolynomial.X (Fin.cast dimension.symm (Fin.last C.n))) = lastVariable

/-- Multiplication by the additional graph equation t-a on the top differential line.
Source: Stacks 0BZJ (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalRefinement.equationMap {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    {C E : PolynomialKoszulChart R B} (F : KoszulDiagonalRefinement C E) : E.top ⟶ E.top :=
  ModuleCat.ofHom (LinearMap.lsmul E.P E.top (F.lastVariable - F.inclusion F.lift))

/-- The last differential is d(t-a); its top wedge maps to the old volume. The boundary
of the actual two-term resolution specifies the inverse contraction, with cohomological signs.
Mathlib's `singleδ` is the negative roof: on the cone `[V_Q --(t-a)--> V_Q]` it is minus the
cocycle sending the degree -1 term identically to `V_Q`. The contraction uses its negative,
the Koszul evaluation `dual(t-a) ⊗ d(t-a) ↦ 1`, the same convention as the graph trace of
`IsKoszulDiagonalGraphTrace` (top wedge to volume).
Source: Stacks 0BZI, 0BZJ (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalRefinement.IsContraction {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    {C E : PolynomialKoszulChart R B} (F : KoszulDiagonalRefinement C E)
    (e : (ModuleCat.derivedCoinduction F.evaluation.toRingHom).obj E.coefficient ≅
      C.coefficient) : Prop :=
  ∃ q : E.top ⟶ (ModuleCat.restrictScalars F.evaluation.toRingHom).obj C.top,
    q E.volume = C.volume ∧
    ∃ hz : F.equationMap ≫ q = 0,
    ∃ hs : (ShortComplex.mk F.equationMap q hz).ShortExact,
      e.inv = (ModuleCat.derivedCoinductionAdjunction F.evaluation.toRingHom).homEquiv _ _
        ((ModuleCat.restrictScalars F.evaluation.toRingHom).mapDerivedCategory.map
          C.coefficientShiftIso.inv ≫
        (Functor.commShiftIso
          (ModuleCat.restrictScalars F.evaluation.toRingHom).mapDerivedCategory
            (C.n : ℤ)).hom.app ((DerivedCategory.singleFunctor _ 0).obj C.top) ≫
        ((ModuleCat.restrictScalars F.evaluation.toRingHom).mapDerivedCategorySingleFunctor
          0).hom.app C.top⟦(C.n : ℤ)⟧' ≫ (-hs.singleδ)⟦(C.n : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) (C.n : ℤ) (E.n : ℤ)
          (by have h := F.dimension; omega)).inv.app
          ((DerivedCategory.singleFunctor _ 0).obj E.top) ≫
        E.coefficientShiftIso.hom)

/-- Refined coinduction comparison, formed by pasting the evaluation counits and contraction.
Source: Stacks 0A70, 0BZJ (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalRefinement.modelMap {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    {C E : PolynomialKoszulChart R B} (F : KoszulDiagonalRefinement C E)
    (e : (ModuleCat.derivedCoinduction F.evaluation.toRingHom).obj E.coefficient ≅
      C.coefficient) : E.model ⟶ C.model :=
  (ModuleCat.derivedCoinductionAdjunction C.quotient.toRingHom).homEquiv _ _
    ((ModuleCat.derivedCoinductionAdjunction F.evaluation.toRingHom).homEquiv _ _
      ((Functor.mapDerivedCategoryNatIso
        (ModuleCat.restrictScalarsComp' F.evaluation.toRingHom C.quotient.toRingHom
          E.quotient.toRingHom (congrArg AlgHom.toRingHom F.quotient).symm) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).inv.app E.model ≫
        (ModuleCat.derivedCoinductionAdjunction E.quotient.toRingHom).counit.app
          E.coefficient) ≫ e.hom)

/-- Preservation of the specified class by the evaluation-normalized refinement map.
Source: Stacks 0BZJ (blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
def KoszulDiagonalRefinement.PreservesClass {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    {C E : PolynomialKoszulChart R B} (F : KoszulDiagonalRefinement C E)
    (κ : C.diagonalHom ≅ koszulDiagonalUnit B)
    (κE : E.diagonalHom ≅ koszulDiagonalUnit B) : Prop :=
  ∃ e : (ModuleCat.derivedCoinduction F.evaluation.toRingHom).obj E.coefficient ≅
      C.coefficient,
    F.IsContraction e ∧ IsIso (F.modelMap e) ∧
    E.diagonalClass κE ≫
      (relativeDualizingDerivedExtension
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom).map
          (F.modelMap e) = C.diagonalClass κ ∧
    ∀ (G : KoszulDiagonalRefinement C E)
      (eG : (ModuleCat.derivedCoinduction G.evaluation.toRingHom).obj E.coefficient ≅
        C.coefficient), G.IsContraction eG → F.modelMap e = G.modelMap eG

/-- Ordered iterated evaluation refinements, carrying their actual composite model maps.
Source: Stacks 0BZJ and evaluation pasting
(blueprint: def-sfb-polynomial-koszul-diagonal-data). -/
inductive KoszulDiagonalRefinementPath {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] :
    (C E : PolynomialKoszulChart R B) → (E.model ⟶ C.model) → Prop
  | identity (C : PolynomialKoszulChart R B) :
      KoszulDiagonalRefinementPath C C (𝟙 C.model)
  | step (C E J : PolynomialKoszulChart R B) (F : KoszulDiagonalRefinement C E)
      (e : (ModuleCat.derivedCoinduction F.evaluation.toRingHom).obj E.coefficient ≅
        C.coefficient) (he : F.IsContraction e) (g : J.model ⟶ E.model)
      (hg : KoszulDiagonalRefinementPath E J g) :
      KoszulDiagonalRefinementPath C J (g ≫ F.modelMap e)

end AlgebraicGeometry
