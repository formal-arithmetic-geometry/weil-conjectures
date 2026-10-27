/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
import WeilConjectures.RingTheory.KoszulDualComplex
import WeilConjectures.RingTheory.KoszulComplementaryEquivalences
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Polynomial graph coinduction with its ordered Koszul orientation

Source: Stacks Project, dualizing.tex, Tag 0BZE; duality.tex, Tag 0BQZ;
the polynomial graph specialization and explicit action/sign calculation in the DAG.
(blueprint: lem-trf-polynomial-graph-coinduction).

The helpers only name the existing Koszul complex, K-flat scalar extension, and
canonical maps used to state the normalization. In particular no adjoint, comparison,
or resolution is chosen from an unproved existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- The shared ordered Koszul complex, placed in degrees -n,...,0.
Source: Stacks 0622, 062F, 0BQZ
(blueprint: lem-trf-polynomial-graph-coinduction). -/
abbrev polynomialGraphKoszul (A : Type u) [CommRing A] (n : ℕ) (a : Fin n → A) :
    CochainComplex (ModuleCat.{u} (MvPolynomial (Fin n) A)) ℤ :=
  (ExteriorAlgebra.koszulComplex (MvPolynomial (Fin n) A) n
    (fun j ↦ MvPolynomial.X j - MvPolynomial.C (a j))).extend
      ComplexShape.embeddingDownNat

/-- Ordered wedge in a term of the graph complex, including the empty wedge.
Source: Stacks 0622, 0BQZ
(blueprint: lem-trf-polynomial-graph-coinduction). -/
def polynomialGraphWedge (A : Type u) [CommRing A] (n : ℕ) (a : Fin n → A)
    (k : ℕ) (v : Fin k → Fin n →₀ MvPolynomial (Fin n) A) :
    (polynomialGraphKoszul A n a).X (-(k : ℤ)) :=
  ((ExteriorAlgebra.koszulComplex (MvPolynomial (Fin n) A) n
    (fun j ↦ MvPolynomial.X j - MvPolynomial.C (a j))).extendXIso
      ComplexShape.embeddingDownNat (i := k) rfl).inv
        (exteriorPower.ιMulti _ k v)

/-- The ordinary ring module in cohomological degree zero, localized into D(A).
Source: Stacks 05RR, 0BZE
(blueprint: lem-trf-polynomial-graph-coinduction). -/
abbrev polynomialGraphUnit (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A A))

/-- K-flat extension along the coefficient inclusion, i.e. S tensor_A^L -.
This is an abbreviation for the existing total left derived construction.
Source: Stacks 06Y6, 0BZE
(blueprint: lem-trf-polynomial-graph-coinduction). -/
abbrev polynomialGraphExtension (A : Type u) [CommRing A] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin n) A)) :=
  letI := extendScalars_preservesKFlatQuasiIso
    (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)
  (extendScalars (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).leftDerivedFunctor

/-- The evaluation-normalized extension/restriction adjunction for the coefficient map.
Source: Stacks 08DW, 06Y6
(blueprint: lem-trf-polynomial-graph-coinduction). -/
def polynomialGraphExtensionAdjunction (A : Type u) [CommRing A] (n : ℕ) :
    polynomialGraphExtension A n ⊣
      (restrictScalars (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).mapDerivedCategory :=
  letI := extendScalars_preservesKFlatQuasiIso
    (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)
  (extendRestrictScalarsAdj (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).derivedAdjunction
    |>.ofNatIsoRight (restrictScalars
      (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).rightDerivedFunctorIsoMapDerivedCategory

/-- The derived coefficient map A[0] -> S[0], with S restricted along C.
It is localization of the ordinary coefficient inclusion, with the standard single-complex
and exact-restriction comparisons. Its extension adjoint fixes the unit comparison.
Source: Stacks 06Y6, 0BZE
(blueprint: lem-trf-polynomial-graph-coinduction). -/
def polynomialGraphCoefficient (A : Type u) [CommRing A] (n : ℕ) :
    polynomialGraphUnit A ⟶
      (restrictScalars (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).mapDerivedCategory.obj
        (polynomialGraphUnit (MvPolynomial (Fin n) A)) :=
  DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
    (semilinearMapAddEquiv (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)
      (ModuleCat.of A A) (ModuleCat.of (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A))
      (MvPolynomial.C : A →+* MvPolynomial (Fin n) A).toSemilinearMap)) ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (restrictScalars (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)) (.up ℤ) 0).inv.app
        (ModuleCat.of (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A))) ≫
    (Functor.mapDerivedCategoryFactors
      (restrictScalars (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))).inv.app
      ((CochainComplex.singleFunctor _ 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A)))

/-- The scalar-restriction identification coming from evaluation composed with C = id.
Source: Stacks 06Y6; the explicit ei=1 action check in the node
(blueprint: lem-trf-polynomial-graph-coinduction). -/
def polynomialGraphSectionIso (A : Type u) [CommRing A] (n : ℕ) (a : Fin n → A) :
    (restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapDerivedCategory ⋙
      (restrictScalars (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).mapDerivedCategory ≅
        𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    (Functor.mapDerivedCategoryNatIso
      (restrictScalarsComp' (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)
        (MvPolynomial.eval₂Hom (RingHom.id A) a) (RingHom.id A)
        (MvPolynomial.eval₂Hom_comp_C (RingHom.id A) a).symm)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictScalarsId A) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The derived graph quotient S tensor_A^L T -> T, viewed over S via evaluation.
Its adjoint is exactly the inverse of the canonical ei=1 restriction identification.
For n=0 this fixes the identity comparison without identifying polynomial carriers.
Source: Stacks 06Y6, 0BZE
(blueprint: lem-trf-polynomial-graph-coinduction). -/
def polynomialGraphQuotient (A : Type u) [CommRing A] (n : ℕ) (a : Fin n → A)
    (T : DerivedCategory (ModuleCat.{u} A)) :
    (polynomialGraphExtension A n).obj T ⟶
      (restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapDerivedCategory.obj T :=
  ((polynomialGraphExtensionAdjunction A n).homEquiv _ _).symm
    ((polynomialGraphSectionIso A n a).inv.app T)

/-- Shifted augmentation in D(S), transported through the canonical localization and
restriction comparisons. No inverse of the augmentation is used in this map.
Source: Stacks 05RR, 0BQZ
(blueprint: lem-trf-polynomial-graph-coinduction). -/
def polynomialGraphShiftedAugmentation (A : Type u) [CommRing A] (n : ℕ) (a : Fin n → A)
    (ε : polynomialGraphKoszul A n a ⟶
      ((restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapHomologicalComplex
        (.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A A))) :
    DerivedCategory.Q.obj ((polynomialGraphKoszul A n a)⟦-(n : ℤ)⟧) ⟶
      (restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapDerivedCategory.obj
        ((polynomialGraphUnit A)⟦-(n : ℤ)⟧) :=
  ((DerivedCategory.Q (C := ModuleCat.{u} (MvPolynomial (Fin n) A))).commShiftIso
    (-(n : ℤ))).hom.app (polynomialGraphKoszul A n a) ≫
    (DerivedCategory.Q.map ε)⟦-(n : ℤ)⟧' ≫
    ((restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapDerivedCategoryFactors.inv.app
      ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A A)))⟦-(n : ℤ)⟧' ≫
    ((restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapDerivedCategory.commShiftIso
      (-(n : ℤ))).inv.app _

/-- The graph Koszul augmentation is a bounded finite-free resolution. Its ordered top
functional fixes C_e(S[0]) = A[-n], with the original A-action. Coinduction after coefficient
extension is naturally shift by -n on the entire unbounded derived category.
The unit component is the oriented chi after the coefficient-normalized unit isomorphism beta.
The last equation fixes the identity comparison when n=0, using the canonical graph quotient,
the shift-zero identification and the evaluation counit, rather than an arbitrary automorphism.

Source: Stacks 0BZE, 0BQZ, 062F, with the node's explicit polynomial specialization
(blueprint: lem-trf-polynomial-graph-coinduction).

Proof (the six DAG steps):
1. Evaluating the first j variables identifies S/(f_1,...,f_j) with the remaining polynomial
ring. Multiplication by the next monic linear polynomial is injective by descending comparison
of coefficients, also over the zero ring. The final quotient is e, whose coefficient section is C.
2. Apply lem-weil-pbc-regular-sequence-koszul-regular to this successive injectivity.
The shared Koszul differential has image (f) in degree zero; hence its augmentation resolves A.
Exterior-power bases give finite-free terms and zero outside degrees -n,...,0.
3. The signed dual of def-sc-koszul-dual-complex and the equivalences of
lem-sc-koszul-complementary-equivalences give zero cohomology except in degree n.
The top functional lambda maps to e(lambda(e_1 wedge ... wedge e_n)); its boundary ideal is (f).
It sends the ordered dual basis to 1, also for the empty tuple.
4. lem-trf-derived-coinduction-adjunction and lem-pod-projective-hom-evaluation-model compute
C_e(S) by that dual. On a K-injective model, (b h)(c)=h(cb)=h(C(b)c)=C(b)h(c).
Thus the top identification is linear for the original A-action, since e(C(b))=b.
lem-sf-derived-concentrated-single gives the oriented isomorphism chi. Its inverse adjunct,
pulled back along the shifted augmentation, is precisely the top map z in the equation below.
5. The resolution makes A perfect over S. Apply lem-trf-perfect-algebra-coinduction-tensor
to N=S tensor_A^L T to identify its coinduction with N tensor_S^L C_e(S), naturally in T.
6. Choose a flat-term K-flat model P by lem-pc-kflat-resolution. By
lem-pur-kflat-change-of-rings, S tensor_A P is K-flat over S. The tensor computation of
lem-pc-derived-tensor-second-factor-functor cancels S using e C=1: in degree p send
(s tensor v) tensor b to (-1)^(np)e(s)bv in P[-n]; the inverse sends v to
(-1)^(np)(1 tensor v) tensor 1. Balancing uses e C=1; the sign changes by (-1)^n as p increases,
exactly the shifted differential. These formulas commute with chain maps and K-flat comparisons.
They give the natural isomorphism alpha with no bound or Tor hypothesis. On the unit,
scalar-extension adjunction identifies beta with C, so the component is the oriented chi.
For n=0 all signs are 1, the empty top functional is the identity, and the inverse comparison
is the adjunct of
the inverse graph quotient, giving the last equation. All zero-ring objects are zero. -/
theorem polynomial_graph_coinduction (A : Type u) [CommRing A] (n : ℕ) (a : Fin n → A) :
    (∀ j : ℤ, Module.Free (MvPolynomial (Fin n) A) ((polynomialGraphKoszul A n a).X j) ∧
      Module.Finite (MvPolynomial (Fin n) A) ((polynomialGraphKoszul A n a).X j)) ∧
    (∀ j : ℤ, j < -(n : ℤ) ∨ 0 < j → IsZero ((polynomialGraphKoszul A n a).X j)) ∧
    ∃ ε : polynomialGraphKoszul A n a ⟶
        ((restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapHomologicalComplex
          (.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A A)),
      QuasiIso ε ∧
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom
        (ε.f 0 (polynomialGraphWedge A n a 0 (fun j ↦ Fin.elim0 j))) = 1 ∧
      ∃ χ : (derivedCoinduction (MvPolynomial.eval₂Hom (RingHom.id A) a)).obj
          (polynomialGraphUnit (MvPolynomial (Fin n) A)) ≅
            (polynomialGraphUnit A)⟦-(n : ℤ)⟧,
        ∃ z : (polynomialGraphKoszul A n a)⟦-(n : ℤ)⟧ ⟶
            (CochainComplex.singleFunctor _ 0).obj (ModuleCat.of (MvPolynomial (Fin n) A)
              (MvPolynomial (Fin n) A)),
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (ModuleCat.of (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A))).hom
              (z.f 0 (((polynomialGraphKoszul A n a).shiftFunctorObjXIso (-(n : ℤ)) 0
                (-(n : ℤ)) (Int.zero_add _).symm).inv
                  (polynomialGraphWedge A n a n (fun j ↦ Finsupp.single j 1)))) = 1 ∧
          polynomialGraphShiftedAugmentation A n a ε ≫
            (restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapDerivedCategory.map
              χ.inv ≫
            (derivedCoinductionAdjunction (MvPolynomial.eval₂Hom (RingHom.id A) a)).counit.app
              (polynomialGraphUnit (MvPolynomial (Fin n) A)) = DerivedCategory.Q.map z ∧
          ∃ α : polynomialGraphExtension A n ⋙
              derivedCoinduction (MvPolynomial.eval₂Hom (RingHom.id A) a) ≅
                shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-(n : ℤ)),
            ∃ β : (polynomialGraphExtension A n).obj (polynomialGraphUnit A) ≅
                polynomialGraphUnit (MvPolynomial (Fin n) A),
              (polynomialGraphExtensionAdjunction A n).homEquiv _ _ β.hom =
                polynomialGraphCoefficient A n ∧
              α.hom.app (polynomialGraphUnit A) =
                (derivedCoinduction (MvPolynomial.eval₂Hom (RingHom.id A) a)).map β.hom ≫
                  χ.hom ∧
            ∀ (h : n = 0) (T : DerivedCategory (ModuleCat.{u} A)),
              polynomialGraphQuotient A n a T ≫
                (restrictScalars (MvPolynomial.eval₂Hom (RingHom.id A) a)).mapDerivedCategory.map
                  ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} A)) ℤ).inv.app T ≫
                    eqToHom (congrArg (fun k : ℕ ↦ T⟦-(k : ℤ)⟧) h.symm) ≫ α.inv.app T) ≫
                (derivedCoinductionAdjunction (MvPolynomial.eval₂Hom (RingHom.id A) a)).counit.app
                  ((polynomialGraphExtension A n).obj T) =
                    𝟙 ((polynomialGraphExtension A n).obj T) := by
  sorry

end ModuleCat
