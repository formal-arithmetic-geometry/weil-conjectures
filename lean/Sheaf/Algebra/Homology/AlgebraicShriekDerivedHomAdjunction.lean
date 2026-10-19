/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.HomTensorTotal
import Sheaf.CategoryTheory.RingedSiteDualityMaps
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Internal derived Hom and algebraic coinduction

Source: Stacks Project, dualizing.tex, Tags 0A70, 0A71 and 0BZW(1)(c)
(blueprint: lem-trf-algebraic-shriek-derived-hom-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace ModuleCat

/-- The existing signed evaluation chain map, selected from its coordinate characterization.
That characterization determines every component uniquely, even for unbounded complexes;
no projectivity hypothesis is used in the evaluation map itself.
Source: Stacks 0A5Y and 0GWQ
(blueprint: lem-trf-algebraic-shriek-derived-hom-adjunction). -/
def coinductionHomEvaluation {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (E I : CochainComplex (ModuleCat.{u} R) ℤ) :
    E ⊗ CochainComplex.moduleHomComplex E I ⟶ I :=
  (Classical.choose (Classical.choose_spec
    (CochainComplex.projective_hom_evaluation_model R))) E I

/-- The canonical comparison from the localized ordinary Hom complex to internal derived Hom:
transpose its signed evaluation after the localization tensorator. This fixes its normalization.
Source: Stacks 0A5Y, 0GWQ, 0A70 and 0A71
(blueprint: lem-trf-algebraic-shriek-derived-hom-adjunction). -/
def coinductionHomComparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (E I : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (CochainComplex.moduleHomComplex E I) ⟶
      (ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj I) :=
  MonoidalClosed.curry
    (Functor.LaxMonoidal.μ DerivedCategory.Q E (CochainComplex.moduleHomComplex E I) ≫
      DerivedCategory.Q.map (coinductionHomEvaluation E I))

variable {P A : Type u} [CommRing P] [CommRing A] (f : P →+* A)
  [HasDerivedCategory.{u} (ModuleCat.{u} P)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)]

/-- Coinduction commutes with shifts by the canonical mate of the exact restriction shift.
In particular C(P[n]) is canonically D[n], for D = C(P[0]).
Source: Stacks 0A70 and 0BZW(1)(c)
(blueprint: lem-trf-algebraic-shriek-derived-hom-adjunction). -/
def coinductionHomShift (Y : DerivedCategory (ModuleCat.{u} P)) (n : ℤ) :
    (derivedCoinduction f).obj (Y⟦n⟧) ≅ ((derivedCoinduction f).obj Y)⟦n⟧ :=
  letI := (derivedCoinductionAdjunction f).rightAdjointCommShift ℤ
  ((derivedCoinduction f).commShiftIso n).app Y

/-- The source of the enriched coinduction adjunction, as a bifunctor.
Source: Stacks 0A70 (blueprint: lem-trf-algebraic-shriek-derived-hom-adjunction). -/
def coinductionHomLeft :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} P) ⥤
      DerivedCategory (ModuleCat.{u} P) :=
  (𝟭 _).prod (derivedCoinduction f) ⋙
    Functor.uncurry.obj MonoidalClosed.internalHom ⋙ (restrictScalars f).mapDerivedCategory

/-- The target bifunctor, RHom_P(UX,Y).
Source: Stacks 0A70 (blueprint: lem-trf-algebraic-shriek-derived-hom-adjunction). -/
def coinductionHomRight :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} P) ⥤
      DerivedCategory (ModuleCat.{u} P) :=
  (restrictScalars f).mapDerivedCategory.op.prod (𝟭 _) ⋙
    Functor.uncurry.obj MonoidalClosed.internalHom

/-- Scalar action becomes coefficient bidual evaluation, before cancelling the equal shifts.
The right side is the transpose of braided evaluation, precomposed in its Hom variable by
UC(Y) ≅ RHom_P(A[0],Y). The left side transports scalar action on K along C(Y) ≅ K.
Consequently the equality has no choice of a map with merely the correct source and target.
Source: Stacks 0BZW(1)(c), normalized by 0A70 and 0A71
(blueprint: lem-trf-algebraic-shriek-derived-hom-adjunction). -/
def coinductionHomScalarFormula
    (θ : coinductionHomLeft f ≅ coinductionHomRight f)
    (κ : derivedCoinduction f ⋙ (restrictScalars f).mapDerivedCategory ≅
      ihom ((restrictScalars f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))))
    (Y : DerivedCategory (ModuleCat.{u} P))
    (K : DerivedCategory (ModuleCat.{u} A)) (s : (derivedCoinduction f).obj Y ≅ K) : Prop :=
  (restrictScalars f).mapDerivedCategory.map
      ((DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} A)).hom ≫
        MonoidalClosed.curry' (𝟙 K)) ≫
      (restrictScalars f).mapDerivedCategory.map ((ihom K).map s.inv) ≫
      θ.hom.app (op K, Y) =
    MonoidalClosed.curry (C := DerivedCategory (ModuleCat.{u} P))
      (((DerivedMonoidal.braidedCategory' DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{u} P) (.up ℤ))).braiding
          ((ihom ((restrictScalars f).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A A)))).obj Y)
          ((restrictScalars f).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))).hom
        ≫ (ihom.ev ((restrictScalars f).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))).app Y) ≫
      (MonoidalClosed.pre
        ((restrictScalars f).mapDerivedCategory.map s.inv ≫ κ.hom.app Y)).app Y

/-- The enriched coinduction adjunction and its scalar-to-bidual normalization.
Source: Stacks 0A70, 0A71 and 0BZW, proof of (1)(c)
(blueprint: lem-trf-algebraic-shriek-derived-hom-adjunction).

The two comparison families are fixed by transposed signed evaluation. Thus the equation
for θ identifies its value with localization of the displayed chain isomorphism T, rather
than choosing unrelated isomorphisms between its source and target. The family κ is θ at
the unit A[0], with the ordinary unit-Hom identification. The last clause uses the canonical
shift mate C(P[n]) ≅ C(P)[n]; its right side is coefficient biduality into P[n]. Cancelling
both shifts gives precisely biduality into P[0].

Proof:
1. Represent Y by a K-injective P-complex I and X by an A-complex E. Coinduce I,
with (a h)(b) = h(ba), using the existing ordinary coextension functor.
2. On each product Hom coordinate define T(z)(x) = z(x)(1), and its inverse by
S(z)(x)(a) = z(ax). A-linearity gives TS = ST = id. Evaluation commutes with
both terms of d(z) = d_I z - (-1)^r z d_E (def-pur-hom-complex).
3. Restriction is exact. A map from an acyclic A-complex into coinduced I transposes
to a map into I and hence has a null homotopy. Transpose that homotopy back; this
proves coinduced I is K-injective (def-pur-kinjective-complex).
4. Internal Hom into these K-injectives computes the two derived Homs. Transpose
signed evaluation to obtain the canonical model comparisons. Localize T. Its formulas
commute with precomposition and postcomposition, giving θ on the two derived variables.
Quasi-isomorphisms of representatives are inverted by lem-pur-rhom-well-defined;
Hom into a K-injective computes derived morphisms by lem-weil-pbc-kinjective-hom-derived.
5. The simultaneous shift comparison on a degree-r cochain has factor (-1)^(nr).
This commutes with evaluation at one and has factor one in degree zero. The canonical
coinduction shift mate is therefore the usual coinduced shift identification.
6. Scalar action a on the shifted coinduced complex becomes h ↦ (a h)(1) = h(a).
This is an equality of chain maps, without any perfection hypothesis.
7. Resolve A[0] and its dual by K-flat complexes (lem-pc-kflat-resolution). The tensor
models of lem-weil-pbc-site-derived-tensor-descent and the currying of
lem-sc-derived-hom-tensor-total identify coefficient evaluation with (h,x) ↦ h(x).
The Hom targets are K-injective by lem-pur-hom-kflat-into-kinjective.
8. The transpose after Koszul exchange is the canonical bidual map
(lem-sfb-ringed-site-duality-maps). The sign on x vanishes unless x has degree zero;
in degree zero it is one. Thus the map in step 6 is exactly that transpose. This
proves the final equality for every integer shift, including zero and negative shifts.
-/
theorem algebraicShriek_derivedHom_adjunction :
    ∃ hJ : ∀ (I : CochainComplex (ModuleCat.{u} P) ℤ),
        I.IsKInjective → ((coinductionComplexFunctor f).obj I).IsKInjective,
      ∃ eP : ∀ (E I : CochainComplex (ModuleCat.{u} P) ℤ) (_hI : I.IsKInjective),
          DerivedCategory.Q.obj (CochainComplex.moduleHomComplex E I) ≅
            (ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj I),
        ∃ eA : ∀ (E I : CochainComplex (ModuleCat.{u} A) ℤ) (_hI : I.IsKInjective),
            DerivedCategory.Q.obj (CochainComplex.moduleHomComplex E I) ≅
              (ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj I),
          ∃ T : ∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
              (I : CochainComplex (ModuleCat.{u} P) ℤ),
              ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
                  (CochainComplex.moduleHomComplex E ((coinductionComplexFunctor f).obj I)) ≅
                CochainComplex.moduleHomComplex
                  (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E) I,
            ∃ θ : coinductionHomLeft f ≅ coinductionHomRight f,
              ∃ κ : derivedCoinduction f ⋙ (restrictScalars f).mapDerivedCategory ≅
                  ihom ((restrictScalars f).mapDerivedCategory.obj
                    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))),
                (∀ (E I : CochainComplex (ModuleCat.{u} P) ℤ) (hI : I.IsKInjective),
                  (eP E I hI).hom = coinductionHomComparison E I) ∧
                (∀ (E I : CochainComplex (ModuleCat.{u} A) ℤ) (hI : I.IsKInjective),
                  (eA E I hI).hom = coinductionHomComparison E I) ∧
                (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
                  (I : CochainComplex (ModuleCat.{u} P) ℤ) (r p q : ℤ) (h : p + r = q)
                  (z : (CochainComplex.moduleHomComplex E
                    ((coinductionComplexFunctor f).obj I)).X r) (x : E.X p),
                  (((T E I).hom.f r z).v p q h) x =
                    (coinductionEvaluation f I).f q ((z.v p q h) x)) ∧
                (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
                  (I : CochainComplex (ModuleCat.{u} P) ℤ) (r p q : ℤ) (h : p + r = q)
                  (z : (CochainComplex.moduleHomComplex
                    (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E) I).X r)
                  (x : E.X p) (a : A),
                  (coinductionEvaluation f I).f q
                      (a • (((T E I).inv.f r z).v p q h) x) = (z.v p q h) (a • x)) ∧
                (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
                  (I : CochainComplex (ModuleCat.{u} P) ℤ) (hI : I.IsKInjective),
                  θ.hom.app (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj I) =
                    (restrictScalars f).mapDerivedCategory.map
                      ((ihom (DerivedCategory.Q.obj E)).map
                        (@derivedCoinductionModel P A _ _ f _ _ I hI).hom) ≫
                    (restrictScalars f).mapDerivedCategory.map
                      (eA E ((coinductionComplexFunctor f).obj I) (hJ I hI)).inv ≫
                    (restrictScalars f).mapDerivedCategoryFactors.hom.app
                      (CochainComplex.moduleHomComplex E ((coinductionComplexFunctor f).obj I)) ≫
                    DerivedCategory.Q.map (T E I).hom ≫
                    (eP (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E) I hI).hom ≫
                    (MonoidalClosed.pre
                      ((restrictScalars f).mapDerivedCategoryFactors.hom.app E)).app
                        (DerivedCategory.Q.obj I)) ∧
                (∀ Y : DerivedCategory (ModuleCat.{u} P),
                  κ.hom.app Y =
                    (restrictScalars f).mapDerivedCategory.map
                      ((MonoidalClosed.unitNatIso.hom.app ((derivedCoinduction f).obj Y)) ≫
                        (MonoidalClosed.pre
                          (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} A)).hom).app
                            ((derivedCoinduction f).obj Y)) ≫
                      θ.hom.app
                        (op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                          (ModuleCat.of A A)), Y)) ∧
                (∀ n : ℤ, coinductionHomScalarFormula f θ κ
                  (((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
                    (ModuleCat.of P P))⟦n⟧)
                  (((derivedCoinduction f).obj
                    ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
                      (ModuleCat.of P P)))⟦n⟧)
                  (coinductionHomShift f
                    ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
                      (ModuleCat.of P P)) n)) := by
  sorry

end ModuleCat
