/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module
public import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData
public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
/-! # Finite-free coordinates for the scalar-Hom comparison

Source: Stacks Project, Tags 08J9 and 08JA.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory

section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

/-- The basis components of a finite-free scalar-extension isomorphism, specified
on every K-flat representative. The degreewise map is multiplication by the actual
basis section, followed by sheafification; the localization square fixes its derived class.
Source: Stacks Project, Tags 08J9 and 08JA.
(blueprint: lem-sf-ringed-finite-free-hom-coordinates). -/
def RingedFiniteFreeBasisCoordinates
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J R)]
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)]
    (d : ℕ) (e : (SheafOfModules.scalarRestriction φ).obj
      (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
      SheafOfModules.free
        (R := SheafOfModules.derivedChangeRingIndependentCoefficients J R)
        (ULift.{max c v r} (Fin d)))
    (E : SheafOfModules.scalarModules J R ⥤ SheafOfModules.scalarModules J S)
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    [E.Additive]
    (T : DerivedCategory (SheafOfModules.scalarModules J R) ⥤
      DerivedCategory (SheafOfModules.scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (X : DerivedCategory (SheafOfModules.scalarModules J R))
    (a : (⨁ fun _ : Fin d ↦ X) ≅ (SheafOfModules.scalarDerivedRestriction φ).obj
      (T.obj X)) : Prop :=
  ∀ (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F →
    ∀ (q : DerivedCategory.Q.obj F ≅ X) (j : Fin d),
    ∃ b : F ⟶ ((SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj F),
      (∀ (n : ℤ) (V : Cᵒᵖ) (x : (F.X n).val.obj V),
        (b.f n).val.app V x = ringedFiniteFreeScalarSection.{c, v, r} J φ E h (F.X n) V
          (((SheafOfModules.ιFree (ULift.up j) ≫ e.inv).val.app V)
            (show R.obj.obj V from 1)) x) ∧
      q.inv ≫ DerivedCategory.Q.map b ≫
          (SheafOfModules.scalarRestrictionComparison φ).inv.app
            ((E.mapHomologicalComplex (.up ℤ)).obj F) =
        biproduct.ι _ j ≫ a.hom ≫
          (SheafOfModules.scalarDerivedRestriction φ).map (T.map q.inv ≫ ε.app F)

/-- Basis coordinates of the restricted evaluation comparison.
The basis identifications are fixed on every K-flat representative by their actual
basis sections. The ordinary scalar adjunction is fixed by its unit sections, its
derived adjunction by its chain transposes, and β by restricted evaluation. Only
the resulting equation on basis inclusions remains to be calculated. Product preservation,
the matrix calculation, naturality, conservativity and assembly of the internal-Hom
isomorphism are proved outside.
Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 08JA, finite-free
specialization of lemma-internal-hom and lemma-section-RHom-over-U.
(blueprint: lem-sf-ringed-finite-free-hom-coordinates).

Proof: use the displayed basis of S over R. On K-flat representatives the maps
(x_j) ↦ sum e_j tensor x_j and the basis coefficient maps are inverse chain maps.
Finite sums preserve quasi-isomorphisms, giving a_X : X^d ≅ U(TX).
The normalized scalar-Hom adjunction identifies U H_S(TP,TQ) with H_R(P,UTQ),
giving β. Transport its ordinary and derived adjunctions to E and T using their
actual object and map formulas and the unique universal counit comparison. Their
unit and chain-transpose equations fix the transported adjunctions. The displayed
transpose equation for β expands scalarHomRestrictedEvaluation: insert eta_P,
apply the counit mate of μ, and restrict S-evaluation. Transpose bijectivity fixes β.
Use a_H and a_Q for the two displayed basis isomorphisms. Transpose
β after the restricted comparison and the i-th basis inclusion. The normalized
scalar unit inserts 1, while the κ formula and μ square multiply it by e_i.
Its transpose is evaluation followed by the i-th basis inclusion on Q.
Uniqueness of transpose gives precisely H_R(P,ι_i followed by a_Q), the equation
asserted here. These identities can be checked on actual K-flat representatives
and localized. Rank zero has no inclusions; no boundedness is used.
No preservation of products or invertibility of the comparison is asserted here. -/
theorem ringedFiniteFreeHomBaseChange_coordinates
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (d : ℕ) (e :
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map φ)).obj
          (SheafOfModules.unit
            (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        SheafOfModules.free (R :=
          SheafOfModules.derivedChangeRingIndependentCoefficients J R)
            (ULift.{max c v r} (Fin d)))
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
      (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
      (_hm : ∀ {M N : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)} (f : M ⟶ N),
        E.map f = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
          eqToHom (h N).symm)
      [_hE : E.Additive]
      (T : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
        DerivedCategory (SheafOfModules.{max c v r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
      (ε : DerivedCategory.Q ⋙ T ⟶
        E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (_hT : T.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) (ComplexShape.up ℤ)))
      (AR : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J R))
      (AS : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J S))
      (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
      (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS)
      (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
      (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
    (hκ : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (Q.X q) U 1 y)))
    (hcomp : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          IsIso (ε.app P) ∧ IsIso (ε.app Q) ∧
          T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
            ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom)) :
    ∃ (adj : E ⊣ SheafOfModules.scalarRestriction φ)
      (δ : T ⊣ SheafOfModules.scalarDerivedRestriction φ),
      (∀ (M : SheafOfModules.scalarModules J R) (V : Cᵒᵖ) (x : M.val.obj V),
        (adj.unit.app M).val.app V x = ringedFiniteFreeScalarSection.{c, v, r} J φ E h M V 1 x) ∧
      (∀ (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (F.X n)) →
        ∀ (N : CochainComplex (SheafOfModules.scalarModules J S) ℤ)
          (g : F ⟶ ((SheafOfModules.scalarRestriction φ).mapHomologicalComplex
            (.up ℤ)).obj N),
        (δ.homEquiv (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj N)).symm
            (DerivedCategory.Q.map g ≫
              (SheafOfModules.scalarRestrictionComparison φ).inv.app N) =
          ε.app F ≫ DerivedCategory.Q.map
            (SheafOfModules.scalarChainTranspose.{c, v, max c v r} φ E _hE adj F N g)) ∧
    ∀ P Q : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)),
    ∃ (a : (⨁ fun _ : Fin d ↦
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≅
      (SheafOfModules.scalarDerivedRestriction φ).obj
        (T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q))))
      (aQ : (⨁ fun _ : Fin d ↦ Q) ≅
        (SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))
      (β : (SheafOfModules.scalarDerivedRestriction φ).obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj (op (T.obj P), T.obj Q)) ≅
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op P, (SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))),
      RingedFiniteFreeBasisCoordinates.{c, v, r, w} J φ d e E h T ε
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) a ∧
      RingedFiniteFreeBasisCoordinates.{c, v, r, w} J φ d e E h T ε Q aQ ∧
      (AR.transpose _ P ((SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))).symm
          β.hom =
        AR.tensor.map (Prod.mkHom (𝟙 _) (δ.unit.app P)) ≫
          δ.unit.app _ ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (μ.hom.app _ ≫ AS.tensor.map
              (Prod.mkHom (δ.counit.app _) (δ.counit.app _))) ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (AS.evaluation (T.obj P) (T.obj Q)) ∧
      ∀ i : Fin d,
        biproduct.ι _ i ≫ a.hom ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (AS.transpose _ (T.obj P) (T.obj Q)
              (μ.inv.app
                ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q), P) ≫
                T.map (AR.evaluation P Q))) ≫ β.hom =
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (𝟙 (op P)) (biproduct.ι _ i ≫ aQ.hom)) := by
  sorry

end Site
end CategoryTheory
