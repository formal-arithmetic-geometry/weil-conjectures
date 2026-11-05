/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomThickLocus
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat

/-! # Evaluation-defined finite-coefficient internal-Hom arrow

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md`, opening paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow).

The arrow is the transpose of the scalar extension of evaluation after the canonical
monoidal tensor comparison.  The ambient construction is available for unbounded objects;
the finite constructible finite-Tor condition is imposed by the surrounding theorem.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local instance] DerivedCategory.braidedCategory'

/-- The native étale right-tensor adjunction, obtained by braiding the closed
structure so its counit has the node's evaluation order H ⊗ K → M.
Source: Stacks 07A4; blueprint thm-coef-finite-hom, opening paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
noncomputable def derivedTensorHomRightAdjunction
    {R : Type (u + 1)} [CommRing R] (X : Scheme.{u})
    (K : DerivedCategoryModule R X) :
    tensorRight K ⊣ (derivedHom (ModuleCat.{u + 1} R) X).obj (op K) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} R) K).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight K)

/--
Evaluation-defined comparison after an arbitrary unital coefficient homomorphism.

The three construction steps from the node are explicit.  First, `φ` gives the
everywhere-defined derived scalar extension `scalarExtension φ X`.  Second, the
inverse of the node’s canonical comparison μ is used in the direction
`F H_A(K,M) ⊗ F K → F(H_A(K,M) ⊗ K)`, and is followed by the image of the native
evaluation.  Third, the resulting map is sent through the `B` tensor--Hom
adjunction bijection.  Thus the body is a fixed transpose, rather than a choice from
the thick-locus existence theorem.

Source: blueprint `def-sf-etale-finite-coefficient-hom-arrow`, opening paragraph.
(blueprint: def-sf-etale-finite-coefficient-hom-arrow) -/
noncomputable def sfEtaleFiniteCoefficientHomArrow
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B)
    (K M : DerivedCategoryModule A X) :
    (EtaleHomLeft X φ M).obj (op K) ⟶ (EtaleHomRight X φ M).obj (op K) :=
  (derivedTensorHomRightAdjunction X ((scalarExtension φ X).obj K)).homEquiv _ _
    ((etaleHomTensorComparison X φ
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) K).hom ≫
      (scalarExtension φ X).map
        ((derivedTensorHomRightAdjunction X K).counit.app M))

/--
General-site form of the finite-coefficient evaluation transpose.  A site-specific
choice of tensor bifunctors, internal-Hom bifunctors, their two-variable adjunctions,
the scalar-extension functor, and its canonical tensor comparison supplies either the
small étale or the pro-étale instance from the node.  The body is the fixed `D`
tensor--Hom transpose of the image of evaluation after the comparison.

Source: blueprint `def-sf-etale-finite-coefficient-hom-arrow`, opening paragraph.
(blueprint: def-sf-etale-finite-coefficient-hom-arrow) -/
noncomputable def sfFiniteCoefficientHomArrowGeneral
    {C : Type w₁} {D : Type w₂} [Category.{v} C] [Category.{w} D]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (adj : T ⊣₂ H)
    (S : D ⥤ D ⥤ D) (J : Dᵒᵖ ⥤ D ⥤ D) (adj' : S ⊣₂ J)
    (F : C ⥤ D)
    (μ : ∀ U V : C, (S.obj (F.obj U)).obj (F.obj V) ≅
      F.obj ((T.obj U).obj V)) (K M : C) :
    F.obj ((H.obj (op K)).obj M) ⟶
      (J.obj (op (F.obj K))).obj (F.obj M) :=
  adj'.homEquiv ((μ K ((H.obj (op K)).obj M)).hom ≫
    F.map ((adj.adj K).counit.app M))

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory
attribute [local instance] DerivedCategory.braidedCategory'

set_option maxHeartbeats 10000000 in
-- Elaborating the native derived closed/tensor structures needs this budget.
set_option maxRecDepth 100000 in
/-- The canonical coefficient tensor comparison on the published small pro-étale
module derived category, in the node's direction μ : F(U ⊗ V) ≅ F U ⊗ F V.
It is the K-flat derived tensor comparison of ordinary sheafified scalar balancing,
transported by the unique adjunction-compatible identification with the published
scalar extension from `lem-pur-derived-change-of-rings`. Thus it is the constant-coefficient
realization of the comparison
of lem-weil-pbc-ringed-topoi-derived-tensor-pullback: both are normalized by ordinary
balancing on flat-term K-flat representatives, with no coefficient-flatness assumption.
Source: Stacks 06YY and 07A4; blueprint thm-coef-finite-hom, opening paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
noncomputable def sfProEtaleCoefficientTensorComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B)
    (K L : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj (K ⊗ L) ≅
      (Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj K ⊗
        (Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj L := by
  let J := ProEt.topology X
  let : Algebra A B := φ.toAlgebra
  let E := Sheaf.extendScalars J φ
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} A)) :=
    ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0}
      (Sheaf J (ModuleCat.{u + 1} A))).has_colimits_of_shape _⟩
  have : E.PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ f hf
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (Sheaf.extendScalarsCompRestrictScalarsIso J A B) f hP hQ
  let a : E.leftDerivedFunctor ⊣ Sheaf.derivedRestrictScalars J φ :=
    (Sheaf.extendScalarsAdjunction J φ).derivedAdjunction.ofNatIsoRight
      (Sheaf.restrictScalars J φ).rightDerivedFunctorIsoMapDerivedCategory
  let fixedAdjunction : Sheaf.fixedCoefficientDerivedScalarExtension J φ ⊣
      Sheaf.derivedRestrictScalars J φ :=
    letI := Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint J φ
    Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)
  let e := a.leftAdjointUniq fixedAdjunction
  exact (e.app (K ⊗ L)).symm ≪≫ (E.leftDerivedTensorIso K).app L ≪≫
    tensorIso (e.app K) (e.app L)

set_option maxHeartbeats 10000000 in
-- Elaborating the native derived closed/tensor structures needs this budget.
set_option maxRecDepth 100000 in
/-- The native right-tensor adjunction on the published pro-étale derived module
category. Braiding the published left-tensor adjunction gives evaluation in the
node's order RHom(K,M) ⊗ K → M.
Source: Stacks 07A4; blueprint thm-coef-finite-hom, opening paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
noncomputable def sfProEtaleTensorHomRightAdjunction
    {A : Type (u + 1)} [CommRing A] (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    tensorRight K ⊣ (derivedHom (ModuleCat.{u + 1} A) X).obj (op K) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight K)

set_option maxHeartbeats 10000000 in
-- Elaborating the native derived closed/tensor structures needs this budget.
set_option maxRecDepth 100000 in
/-- The concrete pro-étale coefficient internal-Hom arrow, with all three node steps.
First use `Sheaf.fixedCoefficientDerivedScalarExtension` along φ, the recorded
everywhere-defined derived scalar extension F of lem-pur-derived-change-of-rings.
Second compose μ⁻¹ at (RHom_A(K,M),K) with F of the native evaluation H ⊗ K → M.
Third transpose by the B-linear right-tensor/internal-Hom adjunction. No arbitrary
comparison, evaluation, scalar functor, or downstream existence theorem is an argument.
Source: blueprint thm-coef-finite-hom, opening paragraph; Stacks 06YY and 07A4
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
noncomputable def sfProEtaleFiniteCoefficientHomArrow
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B)
    (K M : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ⟶
      ((derivedHom (ModuleCat.{u + 1} B) X).obj
        (op ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj K))).obj
          ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj M) :=
  (sfProEtaleTensorHomRightAdjunction X
    ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj K)).homEquiv _ _
      ((sfProEtaleCoefficientTensorComparison X φ
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) K).inv ≫
        (Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).map
          ((sfProEtaleTensorHomRightAdjunction X K).counit.app M))

end AlgebraicGeometry.ProEtale
