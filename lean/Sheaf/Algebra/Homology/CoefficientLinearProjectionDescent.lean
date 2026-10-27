module

public import Sheaf.Algebra.Homology.LocalizedStrictTensorData
public import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Sheaf.Paper.RestrictionDerivedProducts
public import Sheaf.Algebra.Homology.ExtensionTensorComparisonIndependent
import Sheaf.Algebra.Homology.RingedOpenFlatResolution
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Coefficient-linear normalized slice projection descent

Source: Stacks Project, sites-cohomology.tex, Tags 0GL1, 06YU and 06YY;
coefficient-linear refinement in the node's proof, Steps 1--7.
(blueprint: lem-sf-cbc-coefficient-linear-projection-descent).

Scalar extension uses the existing cochain model. Underlying tensor with the target
ring is presented by the universal left-derived pair of ordinary scalar extension
followed by scalar restriction. This is the right-sided one-sided tensor model:
ordinary scalar extension is the sheafified tensor with the target ring, and its
universal counit is the one-sided computation comparison. No resolution is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.LocalizedStrictTensor
namespace SheafOfModules.CoefficientProjection

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The specified coefficient-linear projection, on every resolving complex.
Source: Stacks 0GL1 and 06YY, node proof Steps 2--3
(blueprint: lem-sf-cbc-coefficient-linear-projection-descent). -/
def LinearNormalized (S : Under R)
    (e : ScalarModel.{c, v, r} R S)
    (eV : ScalarModel.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S))
    (η : localizedSystemExtension.{c, v, r} R V ⋙ e.E ≅
      eV.E ⋙ localizedSystemExtension.{c, v, r} S.right V)
    (β : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ e.T ≅
      eV.T ⋙ (localizedSystemExtension.{c, v, r} S.right V).mapDerivedCategory) : Prop :=
  letI := e.additive
  letI := eV.additive
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionAdditive.{c, v, r} S.right V
  ∀ P : CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ,
    Resolving.{max c v, v, r} (R.over V) P →
    e.T.map ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app P) ≫
      e.ε.app (((localizedSystemExtension.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((scalarComparisonOnComplexes.{c, v, r} R V S e eV η).hom.app P) =
    β.hom.app (DerivedCategory.Q.obj P) ≫
      (localizedSystemExtension.{c, v, r} S.right V).mapDerivedCategory.map (eV.ε.app P) ≫
      (localizedSystemExtension.{c, v, r} S.right V).mapDerivedCategoryFactors.hom.app
        ((eV.E.mapHomologicalComplex (.up ℤ)).obj P)

/-- Scalar restriction of beta, with the independently normalized tensor identifications.
Here theta is the inverse of the node's kappa. Source: node proof Step 6, Stacks 06YU
(blueprint: lem-sf-cbc-coefficient-linear-projection-descent). -/
def underlyingComparison (S : Under R)
    (e : ScalarModel.{c, v, r} R S)
    (eV : ScalarModel.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S))
    (θ : scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S) ⋙
      localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} S.right V ⋙ scalars.{c, v, r} R S)
    (A : D.{c, v, r} R ⥤ D.{c, v, r} R)
    (AV : D.{max c v, v, r} (R.over V) ⥤ D.{max c v, v, r} (R.over V))
    (x : e.T ⋙ (scalars.{c, v, r} R S).mapDerivedCategory ≅ A)
    (y : eV.T ⋙ (scalars.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj S)).mapDerivedCategory ≅ AV)
    (β : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ e.T ≅
      eV.T ⋙ (localizedSystemExtension.{c, v, r} S.right V).mapDerivedCategory) :
    (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ A ≅
      AV ⋙ (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory :=
  (Functor.isoWhiskerLeft (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory x).symm ≪≫
    Functor.isoWhiskerRight β (scalars.{c, v, r} R S).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft eV.T (scalarExtensionDerived.{c, v, r} R V S θ).symm ≪≫
    Functor.isoWhiskerRight y (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory

/-- The ordinary underlying chain map r_P is degreewise kappa after eta, with the
canonical exact-restriction comparison inserted by mapHomologicalComplexComp.
Source: node proof Steps 2 and 5--6, Stacks 0GL1
(blueprint: lem-sf-cbc-coefficient-linear-projection-descent). -/
def ordinaryUnderlying (S : Under R)
    (e : ScalarModel.{c, v, r} R S)
    (eV : ScalarModel.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S))
    (θ : scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S) ⋙
      localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} S.right V ⋙ scalars.{c, v, r} R S)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ e.E ≅
      eV.E ⋙ localizedSystemExtension.{c, v, r} S.right V) :
    localizedSystemExtension.{c, v, r} R V ⋙ e.E ⋙ scalars.{c, v, r} R S ≅
      (eV.E ⋙ scalars.{max c v, v, r} (R.over V)
        ((sliceAlgebras.{c, v, r} R V).obj S)) ⋙ localizedSystemExtension.{c, v, r} R V :=
  Functor.isoWhiskerRight η (scalars.{c, v, r} R S) ≪≫ Functor.isoWhiskerLeft eV.E θ.symm

/-- The underlying representative equation using the specified one-sided counits.
`a` and `aV` are the universal computation transformations for underlying tensor.
Source: node proof Steps 5--7, Stacks 06YU
(blueprint: lem-sf-cbc-coefficient-linear-projection-descent). -/
def UnderlyingNormalized (S : Under R)
    (e : ScalarModel.{c, v, r} R S)
    (eV : ScalarModel.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S))
    (θ : scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S) ⋙
      localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} S.right V ⋙ scalars.{c, v, r} R S)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ e.E ≅
      eV.E ⋙ localizedSystemExtension.{c, v, r} S.right V)
    (A : D.{c, v, r} R ⥤ D.{c, v, r} R)
    (AV : D.{max c v, v, r} (R.over V) ⥤ D.{max c v, v, r} (R.over V))
    (a : DerivedCategory.Q ⋙ A ⟶
      (e.E ⋙ scalars.{c, v, r} R S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (aV : DerivedCategory.Q ⋙ AV ⟶
      (eV.E ⋙ scalars.{max c v, v, r} (R.over V)
        ((sliceAlgebras.{c, v, r} R V).obj S)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ρ : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ A ⟶
      AV ⋙ (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory) : Prop :=
  letI := e.additive
  letI := eV.additive
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionAdditive.{c, v, r} S.right V
  ∀ P : CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ,
    Resolving.{max c v, v, r} (R.over V) P →
    A.map ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app P) ≫
      a.app (((localizedSystemExtension.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (ordinaryUnderlying.{c, v, r} R V S e eV θ η) (.up ℤ)).hom.app P) =
    ρ.app (DerivedCategory.Q.obj P) ≫
      (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.map (aV.app P) ≫
      (localizedSystemExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app
        (((eV.E ⋙ scalars.{max c v, v, r} (R.over V)
          ((sliceAlgebras.{c, v, r} R V).obj S)).mapHomologicalComplex (.up ℤ)).obj P)

/-- The specified ordinary S-linear projection descends uniquely, and its scalar
restriction is exactly the uniquely normalized underlying derived projection.
The underlying tensors are specified by universal left-derived pairs for ordinary
scalar extension followed by restriction; this is the equivalent one-sided tensor
presentation, retaining its counit. The comparisons x and y are conclusions with
independent counit equations, so the underlying normalization is not self-imposed.

Source: Stacks Project, sites-cohomology.tex, Tags 0GL1, 06YU, 06YY;
coefficient-linear refinement, node proof Steps 1--7.
(blueprint: lem-sf-cbc-coefficient-linear-projection-descent).

Proof:
1. Flat-term K-flat complexes resolve all objects. Exact localized extension preserves
quasi-isomorphisms and carries these complexes to flat-term K-flat complexes
(lem-cbc-ringed-open-flat-resolution). The scalar computation counits are invertible
there (lem-weil-pbc-ringed-topoi-derived-pullback).
2. Apply eta degreewise. Its naturality gives the differential squares, chain-map
naturality, and compatibility with homotopies. The result is an S-linear chain iso.
3. Conjugate its localization by the scalar counits and the exact-extension comparison,
obtaining the equation LinearNormalized on resolving models.
4. Resolving localization and its fully faithful restriction on transformations extend
this comparison and its inverse uniquely to beta (lem-weil-pbc-site-derived-tensor-descent,
lem-weil-pbc-localization-universal-property). This proves existence and uniqueness in D(S).
5. Exact scalar restriction descends kappa. Ordinary scalar extension followed by
restriction is tensor with the restricted target ring
(lem-cbc-extension-tensor-comparison-independent). Its left derived universal pair is
the one-sided tensor computation of lem-trf-site-one-sided-tensor-normalization.
6. The two universal computations descend the identities on the ordinary restricted
scalar-extension models to x and y. Their counit equations specify them independently
of beta. Naturality of derived kappa identifies y followed by extension with the
corresponding ambient comparison. In underlyingComparison adjacent inverse factors
cancel; what remains is Q(kappa eta) and exactly UnderlyingNormalized.
7. Any natural R-linear transformation with this equation agrees on every resolving
model. Full faithfulness of resolving localization makes it equal to the displayed
underlyingComparison. This includes every strict-tower evaluation satisfying the same
computation equation. No flatness of the ring map, bounds or completeness are used. -/
theorem coefficient_linear_projection_descent (S : Under R)
    (e : ScalarModel.{c, v, r} R S)
    (eV : ScalarModel.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S))
    (θ : scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj S) ⋙
      localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} S.right V ⋙ scalars.{c, v, r} R S)
    (hθ : ScalarExtensionNormalized.{c, v, r} R V S θ)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ e.E ≅
      eV.E ⋙ localizedSystemExtension.{c, v, r} S.right V)
    (A : D.{c, v, r} R ⥤ D.{c, v, r} R)
    (AV : D.{max c v, v, r} (R.over V) ⥤ D.{max c v, v, r} (R.over V))
    (a : DerivedCategory.Q ⋙ A ⟶
      (e.E ⋙ scalars.{c, v, r} R S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (aV : DerivedCategory.Q ⋙ AV ⟶
      (eV.E ⋙ scalars.{max c v, v, r} (R.over V)
        ((sliceAlgebras.{c, v, r} R V).obj S)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ha : A.IsLeftDerivedFunctor a (HomologicalComplex.quasiIso _ (.up ℤ)))
    (haV : AV.IsLeftDerivedFunctor aV (HomologicalComplex.quasiIso _ (.up ℤ))) :
    ∃ (β : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ e.T ≅
        eV.T ⋙ (localizedSystemExtension.{c, v, r} S.right V).mapDerivedCategory),
      LinearNormalized.{c, v, r} R V S e eV η β ∧
      (∀ β', LinearNormalized.{c, v, r} R V S e eV η β' → β' = β) ∧
      ∃ (x : e.T ⋙ (scalars.{c, v, r} R S).mapDerivedCategory ≅ A)
        (y : eV.T ⋙ (scalars.{max c v, v, r} (R.over V)
          ((sliceAlgebras.{c, v, r} R V).obj S)).mapDerivedCategory ≅ AV),
        (∀ P : CochainComplex (Modules.{c, v, r} R) ℤ,
          x.hom.app (DerivedCategory.Q.obj P) ≫ a.app P =
            (scalars.{c, v, r} R S).mapDerivedCategory.map (e.ε.app P) ≫
              (scalars.{c, v, r} R S).mapDerivedCategoryFactors.hom.app
                ((e.E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
        (∀ P : CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ,
          y.hom.app (DerivedCategory.Q.obj P) ≫ aV.app P =
            (scalars.{max c v, v, r} (R.over V)
              ((sliceAlgebras.{c, v, r} R V).obj S)).mapDerivedCategory.map (eV.ε.app P) ≫
              (scalars.{max c v, v, r} (R.over V)
                ((sliceAlgebras.{c, v, r} R V).obj S)).mapDerivedCategoryFactors.hom.app
                  ((eV.E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
        UnderlyingNormalized.{c, v, r} R V S e eV θ η A AV a aV
          (underlyingComparison.{c, v, r} R V S e eV θ A AV x y β).hom ∧
        (∀ ρ' : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ A ⟶
            AV ⋙ (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory,
          UnderlyingNormalized.{c, v, r} R V S e eV θ η A AV a aV ρ' →
            ρ' = (underlyingComparison.{c, v, r} R V S e eV θ A AV x y β).hom) := by
  sorry

end SheafOfModules.CoefficientProjection
