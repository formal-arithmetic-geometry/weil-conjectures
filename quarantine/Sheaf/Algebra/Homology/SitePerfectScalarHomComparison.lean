/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.CategoryTheory.RingedSitePerfectDuality

/-! # Evaluation-normalized scalar Hom comparison for a site-perfect source

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, lemma-dual-perfect-complex;
current blueprint lem-fix-operation-reduction.proof.md, paragraph 1.
(blueprint: lem-fix-site-perfect-scalar-hom).

The auxiliary data retain the existing scalar universal pair, fixed K-flat tensor
models, and Koszul symmetry. The comparison is constructed by the specified transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local irreducible] SheafOfModules.monoidalCategory derivedInternalHomOfUniverses

namespace CategoryTheory

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J S)]

/-- The canonical ordinary scalar tensor formula on pure generators, before localization.
Source: Stacks 07A4; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def SiteScalarHomGeneratorFormula
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (κ : coefficientTotalTensor.{r, c, v} J R ⋙ D.E.mapHomologicalComplex (.up ℤ) ≅
      (D.E.mapHomologicalComplex (.up ℤ)).prod (D.E.mapHomologicalComplex (.up ℤ)) ⋙
        coefficientTotalTensor.{r, c, v} J S) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
      (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      ((κ.hom.app (P, Q)).f (p + q)).val.app U
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
          (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
          U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
            P Q p q (p + q) rfl U x y)) =
      WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
        ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y)

/-- The canonical derived tensor comparison is fixed by its K-flat counit square.
This is the same representative characterization as ringed-topos tensor pullback.
Source: Stacks 07A4; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def SiteScalarHomTensorNormalization
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (AR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (AS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (MR : CoefficientTensorModels.{r, c, v, w} J R AR)
    (MS : CoefficientTensorModels.{r, c, v, w} J S AS)
    (κ : coefficientTotalTensor.{r, c, v} J R ⋙ D.E.mapHomologicalComplex (.up ℤ) ≅
      (D.E.mapHomologicalComplex (.up ℤ)).prod (D.E.mapHomologicalComplex (.up ℤ)) ⋙
        coefficientTotalTensor.{r, c, v} J S)
    (μ : AR.tensor ⋙ D.T ≅ D.T.prod D.T ⋙ AS.tensor) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
      ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
        D.T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
            μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            AS.tensor.map (Prod.mkHom (D.ε.app P) (D.ε.app Q)) =
          D.ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
            DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
            (MS.iso J S AS _ _ hEP hEQ).hom

attribute [local irreducible] SiteScalarHomGeneratorFormula SiteScalarHomTensorNormalization

/-- A presentation of the actual scalar and tensor operations used in the Hom map.
The final two fields are exactly the canonical pure-tensor and K-flat counit squares
of the published scalar tensor comparison, with no finite-free hypothesis on S.
These data are existential conclusions of the main theorem, not extra hypotheses.
Source: Stacks 07A4, 08J9 and 08JJ; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
structure SitePerfectScalarHomData where
  /-- The existing universal derived change of rings, with actual ordinary extension. -/
  scalar : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ
  /-- The closed structure with the fixed derived internal Hom over R. -/
  sourceClosed : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- The closed structure with the fixed derived internal Hom over S. -/
  targetClosed : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S)
  /-- Its actual K-flat tensor and Hom-evaluation normalization over R. -/
  sourceModel : CoefficientTensorModels.{r, c, v, w} J R sourceClosed
  /-- Its actual K-flat tensor and Hom-evaluation normalization over S. -/
  targetModel : CoefficientTensorModels.{r, c, v, w} J S targetClosed
  /-- The symmetry over R. -/
  sourceSymmetry : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ sourceClosed.monoidal
  /-- The symmetry over S. -/
  targetSymmetry : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J S))
    _ targetClosed.monoidal
  /-- The source symmetry is the Koszul symmetry and its unit is R in degree zero. -/
  sourceCoherence : RingedDerivedTensorCoherence.{c, v, r, w} J R
    sourceClosed sourceModel sourceSymmetry
  /-- The target symmetry is the Koszul symmetry and its unit is S in degree zero. -/
  targetCoherence : RingedDerivedTensorCoherence.{c, v, r, w} J S
    targetClosed targetModel targetSymmetry
  /-- The ordinary total-tensor scalar comparison. -/
  complexIso : coefficientTotalTensor.{r, c, v} J R ⋙
      scalar.E.mapHomologicalComplex (.up ℤ) ≅
    (scalar.E.mapHomologicalComplex (.up ℤ)).prod
      (scalar.E.mapHomologicalComplex (.up ℤ)) ⋙ coefficientTotalTensor.{r, c, v} J S
  /-- The derived comparison t: F(P tensor Q) = FP tensor FQ. -/
  tensorIso : sourceClosed.tensor ⋙ scalar.T ≅ scalar.T.prod scalar.T ⋙ targetClosed.tensor
  /-- The ordinary comparison is fixed on sheafified pure tensor generators. -/
  generators : SiteScalarHomGeneratorFormula J φ scalar complexIso
  /-- The derived comparison is the localization of this same chain comparison. -/
  normalization : SiteScalarHomTensorNormalization J φ scalar sourceClosed targetClosed
    sourceModel targetModel complexIso tensorIso

variable (M : SitePerfectScalarHomData.{c, v, r, w} J φ)

/-- The evaluation P tensor RHom(P,Q) to Q in the tensor order of the node.
It is the recorded counit preceded by the canonical Koszul symmetry.
Source: Stacks 08J9 and 08JJ; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def siteScalarHomSourceEvaluation
    (P Q : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    M.sourceClosed.tensor.obj
      (P, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ⟶ Q :=
  (M.sourceSymmetry.braiding P
    ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q))).hom ≫
      M.sourceClosed.evaluation P Q

/-- The canonical comparison is the left tensor-Hom transpose of F(evaluation) after
inverse tensor comparison. The leading target symmetry converts the published
Hom-tensor-P adjunction into the P-tensor-Hom adjunction, with no choice of map.
Source: Stacks 08JJ and 07A4; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def siteScalarHomComparison
    (P Q : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    M.scalar.T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op (M.scalar.T.obj P), M.scalar.T.obj Q) :=
  M.targetClosed.transpose _ (M.scalar.T.obj P) (M.scalar.T.obj Q)
    ((M.targetSymmetry.braiding
      (M.scalar.T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)))
      (M.scalar.T.obj P)).hom ≫
        M.tensorIso.inv.app
          (P, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≫
        M.scalar.T.map (siteScalarHomSourceEvaluation J φ M P Q))

end Site

/-- Scalar extension commutes with internal Hom from a site-perfect object, by the
specified evaluation transpose, naturally in both variables. No flatness of S over R
or boundedness, constructibility or Tor-amplitude restriction on Q is assumed.

Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex, applied over both rings;
current blueprint lem-fix-operation-reduction.proof.md, paragraph 1.
(blueprint: lem-fix-site-perfect-scalar-hom).

Proof:
1. Regard the ring map as a morphism of ringed topoi over the identity topos. Use
   lem-pur-derived-change-of-rings for F and its K-flat universal pair. The canonical
   comparison of lem-weil-pbc-ringed-topoi-derived-tensor-pullback and the coherent
   structures of lem-sf-ringed-derived-closed-symmetric-monoidal and
   lem-sfb-ringed-derived-monoidal-comparisons give the displayed normalized data.
2. For perfect P put D = RHom(P,R). By lem-sfb-ringed-site-duality-maps the evaluation
   comparison D tensor N to RHom(P,N) is the transpose of evaluation tensor 1_N,
   after symmetry. Its invertibility for every unbounded N is exactly
   lem-sfb-ringed-site-perfect-duality, checked locally on bounded finite-free retracts.
3. Apply lem-fix-closed-evaluation-dual-criterion to those actual comparisons. Its
   coevaluation is the inverse evaluation comparison at P applied to the transpose
   of 1_P. Both triangle identities hold for the specified evaluation.
4. Apply lem-fix-monoidal-dual-hom-comparison to this dual pair and the canonical
   strong tensor structure on F. Its comparison is the same transpose as
   siteScalarHomComparison, so that specified map is invertible for every Q.
5. Inverse transposition gives the displayed evaluation equation. Transposing both
   sides of the naturality square for a:P' to P and b:Q to Q' gives the same map,
   by naturality of evaluation and the tensor comparison. Hence both naturalities
   hold, including zero objects, identity ring maps and the zero coefficient ring. -/
theorem sitePerfectScalarHomComparison
    (X : AlgebraicGeometry.Scheme.{u})
    [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) r}]
    [(AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) r}]
    [∀ U : X.ProEt, HasSheafify ((AlgebraicGeometry.Scheme.ProEt.topology X).over U)
      AddCommGrpCat.{max (u + 1) r}]
    [∀ U : X.ProEt, ((AlgebraicGeometry.Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) r}]
    (R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{max (u + 1) r})
    (φ : R ⟶ S)
    [HasDerivedCategory.{w} (RingedTensorModules.{u + 1, u, r}
      (AlgebraicGeometry.Scheme.ProEt.topology X) R)]
    [HasDerivedCategory.{w} (RingedTensorModules.{u + 1, u, r}
      (AlgebraicGeometry.Scheme.ProEt.topology X) S)] :
    ∃ M : SitePerfectScalarHomData.{u + 1, u, r, w}
        (AlgebraicGeometry.Scheme.ProEt.topology X) φ,
      (∀ P : DerivedCategory (RingedTensorModules.{u + 1, u, r}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R),
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, r, w} R P →
        ∀ Q : DerivedCategory (RingedTensorModules.{u + 1, u, r}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R),
        IsIso (siteScalarHomComparison _ φ M P Q)) ∧
      (∀ (P P' Q Q' : DerivedCategory (RingedTensorModules.{u + 1, u, r}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R)) (a : P' ⟶ P) (b : Q ⟶ Q'),
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, r, w} R P →
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, r, w} R P' →
        siteScalarHomComparison _ φ M P Q ≫
            (derivedInternalHomOfUniverses.{u + 1, u, r, w} _ S).map
              (Prod.mkHom (M.scalar.T.map a).op (M.scalar.T.map b)) =
          M.scalar.T.map ((derivedInternalHomOfUniverses.{u + 1, u, r, w} _ R).map
            (Prod.mkHom a.op b)) ≫ siteScalarHomComparison _ φ M P' Q') ∧
      (∀ P Q : DerivedCategory (RingedTensorModules.{u + 1, u, r}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R),
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, r, w} R P →
        M.targetClosed.tensor.map (Prod.mkHom (𝟙 (M.scalar.T.obj P))
            (siteScalarHomComparison _ φ M P Q)) ≫
          (M.targetSymmetry.braiding (M.scalar.T.obj P)
            ((derivedInternalHomOfUniverses.{u + 1, u, r, w} _ S).obj
              (op (M.scalar.T.obj P), M.scalar.T.obj Q))).hom ≫
          M.targetClosed.evaluation (M.scalar.T.obj P) (M.scalar.T.obj Q) =
        M.tensorIso.inv.app
            (P, (derivedInternalHomOfUniverses.{u + 1, u, r, w} _ R).obj (op P, Q)) ≫
          M.scalar.T.map (siteScalarHomSourceEvaluation _ φ M P Q)) := by
  sorry

end CategoryTheory
