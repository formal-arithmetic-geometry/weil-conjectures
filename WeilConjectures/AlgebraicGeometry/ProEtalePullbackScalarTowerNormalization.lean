/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization

/-!
# Normalization of pullback and successive finite coefficient extension

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-direct-image.proof.md, Step 4, with the Step 1 pullback comparisons
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization).

The predicates below spell out the normalization of the already specified maps. They
introduce no replacement functor, tensor product, or choice of a derived comparison.
Pure tensors mean their sheafification images. The scalar-first convention in the
existing scalar-extension API writes the paper's x tensor s as s tensor x.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The ordinary tensor and universal derived presentation supplied directly by the
nonlegacy independent-coefficient theorem. Its object and map equations fix the
ordinary sheafified tensor, and its universal counit fixes the derived comparison.
The derived functor is the already prescribed scalar extension, definitionally.
Source: Stacks 03EK, 06YY
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization). -/
def scalarTowerPresentation
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    SheafOfModules.SuccessiveDerivedQuotient.Presentation.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T)
      (hD := fun R ↦ proEtaleRingModules_hasDerivedCategory T R)
      (proEtaleConstantRingMap (T := T) φ) :=
  letI : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let h := SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (proEtaleConstantRingMap (T := T) φ)
  { ordinary := h.choose
    obj_eq := h.choose_spec.choose
    map_eq := h.choose_spec.choose_spec.choose
    additive := h.choose_spec.choose_spec.choose_spec.choose
    derived := scalarExtensionFunctor φ T
    counit := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
    universal := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1 }

/-- The universal counit on cochain representatives, using only the canonical
homotopy-quotient factorization maps. This is the counit of the nonlegacy presentation,
with its prescribed derived functor; no comparison is chosen independently.
Source: Stacks 06XN, 06YY
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization). -/
def scalarTowerComplexCounit
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    (scalarExtensionFunctor φ T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((scalarTowerPresentation φ T).ordinary.mapHomologicalComplex (.up ℤ)).obj P) :=
  (scalarExtensionFunctor φ T).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (scalarTowerPresentation φ T).counit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((scalarTowerPresentation φ T).ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((scalarTowerPresentation φ T).ordinary.mapHomologicalComplex (.up ℤ)).obj P)

/-- Forward and inverse local formulas for an ordinary scalar associator. These use
the existing nonlegacy sheafified pure tensors, transported by the presentation's
object equation. C-linearity fixes the action on the last tensor factor.
Source: blueprint direct-image proof Step 4; Stacks 03EK, 06YY
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization). -/
def ScalarTowerPureTensorNormalization
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u})
    (β : (scalarTowerPresentation φ T).ordinary ⋙ (scalarTowerPresentation ψ T).ordinary ≅
      (scalarTowerPresentation (ψ.comp φ) T).ordinary) : Prop :=
  ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
    CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing T A) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := proEtaleConstantRing T A) (P.X i)) →
    ∀ (i : ℤ) (W : T.ProEtᵒᵖ) (x : (P.X i).val.obj W)
    (s : (proEtaleConstantRing T B).obj.obj W) (t : (proEtaleConstantRing T C).obj.obj W),
    ((β.hom.app (P.X i)).val.app W
      (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (scalarTowerPresentation ψ T)
        ((scalarTowerPresentation φ T).ordinary.obj (P.X i)) W t
        (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (scalarTowerPresentation φ T)
          (P.X i) W s x)) =
      SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
        (scalarTowerPresentation (ψ.comp φ) T) (P.X i) W
          (((proEtaleConstantRingMap (T := T) ψ).hom.app W) s * t) x) ∧
    ((β.inv.app (P.X i)).val.app W
      (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
        (scalarTowerPresentation (ψ.comp φ) T) (P.X i) W t x) =
      SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (scalarTowerPresentation ψ T)
        ((scalarTowerPresentation φ T).ordinary.obj (P.X i)) W t
        (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (scalarTowerPresentation φ T)
          (P.X i) W 1 x))

/-- The K-flat computation condition for a candidate derived scalar associator.
The ordinary isomorphism is fixed by both pure-tensor formulas. Localization of its
termwise chain map computes the candidate via the prescribed universal scalar counits.
All flat-term K-flat representatives are quantified, so no boundedness is imposed.
Source: blueprint direct-image proof Step 4; Stacks 06YY and 0G7E
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization). -/
def IsScalarTowerRepresentativeNormalization
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u})
    (α : scalarExtensionFunctor φ T ⋙ scalarExtensionFunctor ψ T ≅
      scalarExtensionFunctor (ψ.comp φ) T) : Prop :=
  ∃ β : (scalarTowerPresentation φ T).ordinary ⋙ (scalarTowerPresentation ψ T).ordinary ≅
      (scalarTowerPresentation (ψ.comp φ) T).ordinary,
    ScalarTowerPureTensorNormalization φ ψ T β ∧
    ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
      CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing T A) P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology T) (R := proEtaleConstantRing T A) (P.X i)) →
      α.hom.app (DerivedCategory.Q.obj P) ≫ scalarTowerComplexCounit (ψ.comp φ) T P =
        (scalarExtensionFunctor ψ T).map (scalarTowerComplexCounit φ T P) ≫
          scalarTowerComplexCounit ψ T
            (((scalarTowerPresentation φ T).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P)

/-- A candidate derived pullback comparison has the prescribed B-linear normalization.
The ordinary isomorphism sends the pullback of x tensor s to the pullback of x
 tensor c_B(s), using the canonical adjunction units for inverse-image sections.
Its components are B-module morphisms, so B acts on the last tensor factor.
The final equation identifies its termwise localization with the candidate using
canonical scalar counits and exact pullback factors, in D(Z,B) itself.
All flat-term K-flat representatives are quantified, without bounds on their degrees.
Source: blueprint direct-image proof Steps 1 and 4; Stacks 03EL, 06YY, 07A4
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization). -/
def IsPullbackScalarRepresentativeNormalization
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (lam : scalarExtensionFunctor φ Y ⋙ proEtaleConstantRingDerivedPullback B q ≅
      proEtaleConstantRingDerivedPullback A q ⋙ scalarExtensionFunctor φ Z) : Prop :=
  ∃ t : (scalarTowerPresentation φ Y).ordinary ⋙
        proEtaleConstantRingPullback B q ≅
      proEtaleConstantRingPullback A q ⋙
        (scalarTowerPresentation φ Z).ordinary,
    (∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEt)
      (x : M.val.obj (Opposite.op V))
      (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op V)),
      (t.hom.app M).val.app (Opposite.op ((proEtaleBaseChange q).obj V))
        (((proEtaleConstantRingAdjunction B q).unit.app
          ((scalarTowerPresentation φ Y).ordinary.obj M)).val.app
            (Opposite.op V)
              (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (scalarTowerPresentation φ Y)
                M (Opposite.op V) s x)) =
      SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (scalarTowerPresentation φ Z)
        ((proEtaleConstantRingPullback A q).obj M)
        (Opposite.op ((proEtaleBaseChange q).obj V))
        (((proEtaleRingDirectImageMap q (proEtaleConstantRing Y B)
          (proEtaleConstantRing Z B) (proEtaleConstantRingComparison q B)).hom.app
            (Opposite.op V)) s)
        (((proEtaleConstantRingAdjunction A q).unit.app M).val.app (Opposite.op V) x)) ∧
    ∀ (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ),
      CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing Y A) P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) →
      (proEtaleConstantRingDerivedPullback B q).map
          (scalarTowerComplexCounit φ Y P) ≫
        (proEtaleConstantRingPullback B q).mapDerivedCategoryFactors.hom.app
          (((scalarTowerPresentation φ Y).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P) =
      lam.hom.app (DerivedCategory.Q.obj P) ≫
        (scalarExtensionFunctor φ Z).map
          ((proEtaleConstantRingPullback A q).mapDerivedCategoryFactors.hom.app P) ≫
        scalarTowerComplexCounit φ Z
          (((proEtaleConstantRingPullback A q).mapHomologicalComplex (.up ℤ)).obj P)

/-- The already specified associator satisfies the tensor formulas and is the unique
natural isomorphism with the representative normalization.
Source: blueprint direct-image proof Step 4
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization). -/
def PrescribedScalarTowerNormalization
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u}) : Prop :=
  IsScalarTowerRepresentativeNormalization φ ψ T (scalarExtensionFunctor_composition φ ψ T) ∧
  ∃! α : scalarExtensionFunctor φ T ⋙ scalarExtensionFunctor ψ T ≅
      scalarExtensionFunctor (ψ.comp φ) T,
    IsScalarTowerRepresentativeNormalization φ ψ T α

/-- The already specified pullback comparison is uniquely determined by balancing
on all flat-term K-flat representatives, including its target coefficient action.
Source: blueprint direct-image proof Steps 1 and 4
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization). -/
def PrescribedPullbackScalarNormalization
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (q : Z ⟶ Y) : Prop :=
  IsPullbackScalarRepresentativeNormalization φ q (directImageScalarPullbackIso φ q) ∧
  ∃! lam : scalarExtensionFunctor φ Y ⋙ proEtaleConstantRingDerivedPullback B q ≅
      proEtaleConstantRingDerivedPullback A q ⋙ scalarExtensionFunctor φ Z,
    IsPullbackScalarRepresentativeNormalization φ q lam

end AlgebraicGeometry.ProEtale
