/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Paper.ProEtaleConstantModulePullbackHomology
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy
import Sheaf.Paper.RestrictionDerivedProducts
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.FiniteRingActionLocalConstancy
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-! # Finite local models for restricted scalar-extension cohomology

Source: Stacks Project, sites-cohomology.tex, Tag 094H,
lemma-locally-constant-tensor-product; sites-modules.tex, Tag 093S,
lemma-morphism-locally-constant; blueprint scalar-extension proof (2)
(blueprint: lem-sp-restricted-scalar-cohomology-local-constancy).

The scalar-extension helper retains independent site and localization universes.
The theorem gives finite B-module models separately in each cohomological degree.
-/

@[expose] public section
set_option autoImplicit false
universe uC vC r u wA wB
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Constant-coefficient derived scalar extension, with the right-factor target action.
Source: Stacks Project, Tag 06YY
(blueprint: lem-sp-restricted-scalar-cohomology-local-constancy).
The universal left-derived pair determines the selected functor up to its canonical
counit-compatible isomorphism. Its ordinary functor is sheafified scalar extension,
and its counit computes the tensor on K-flat representatives. -/
noncomputable def constantCoefficientScalarExtensionOfUniverses
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wA} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A))))]
    [HasDerivedCategory.{wB} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of B))))] :
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A)))) ⥤
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of B)))) :=
  (Classical.choice (nonempty_derivedChangeOfRingsCochainModel
    ((constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom f)))).T

end SheafOfModules

namespace AlgebraicGeometry.Scheme

-- Select the fixed-size instances only while elaborating this theorem.
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify in
/-- Derived extension of finite coefficients has finite local target-module models
in every degree after any restriction satisfying the stated input hypotheses.

Source: Stacks Project, Tags 094H and 093S; blueprint scalar-extension proof (2)
(blueprint: lem-sp-restricted-scalar-cohomology-local-constancy).

Proof:
1. Choose a K-flat resolution of a representative of K (lem-pc-kflat-resolution).
The cochain model of derived change of rings (lem-pur-derived-change-of-rings)
computes K_B by tensoring this resolution with B_T, retaining the right B-action.
Restricting scalars gives the usual derived tensor with Res(B_T)[0]
(def-weil-derived-tensor, def-pc-sheaf-restrict-scalars).
2. Exact constant-coefficient pullback commutes with cohomology and upper bounds
(lem-pur-proetale-constant-module-pullback-homology). The second tensor input has
only constant cohomology B in degree zero: use
lem-sfb-geometric-inverse-image-constant-module and
lem-pur-proetale-constant-coefficient-comparison. Its stalks are finite by
lem-weil-proetale-constant-sheaf-stalk; zero cohomology has the zero model.
3. Apply lem-pur-proetale-restricted-tensor-finite-local-constancy. It gives
locally constant A-module cohomology with finite stalks after restriction.
4. Exact scalar restriction commutes with cohomology
(lem-weil-pbc-restriction-derived-products). Both coefficient pullbacks have the
same underlying abelian inverse image (lem-pe-constant-left-module-inverse-image),
using the canonical coefficient comparisons of step 2. Thus their underlying
set sheaves are isomorphic; no flatness of B over A is required.
5. Choose constant A-module models on a cover. On nonempty covering members,
choose a geometric point: lem-weil-proetale-weakly-etale-localization and
lem-weil-proetale-constant-sheaf-stalk identify the model with its finite stalk.
Pointed neighbourhoods mapping to a covering member are cofinal by fibre products
(def-weil-proetale-geometric-stalk). On empty members use the zero module.
Pulling the cover back to each site object gives finite constant set models.
6. Apply lem-sp-finite-ring-action-local-constancy with the finite ring B.
Refine to make its finite operation tables constant; this yields finite B-module
models and B-linear isomorphisms on localized ringed sites. Do this separately
for each q, so neither a common cover nor a lower cohomological bound is required. -/
theorem restrictedScalarCohomology_finiteLocalModels
    {T X : Scheme.{u}} (a : X ⟶ T)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (f : A →+* B)
    [HasDerivedCategory.{wA} (proEtaleRingModules.{u} T (proEtaleConstantRing T A))]
    [HasDerivedCategory.{wB} (proEtaleRingModules.{u} T (proEtaleConstantRing T B))]
    (K : DerivedCategory (proEtaleRingModules.{u} T (proEtaleConstantRing T A)))
    (hKb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules.{u} T (proEtaleConstantRing T A)) j).obj K))
    (hK : ∀ j : ℤ,
      IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} X A
        (proEtaleConstantModulePullback a A
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules.{u} T (proEtaleConstantRing T A)) j).obj K)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback a A
            ((DerivedCategory.homologyFunctor
              (proEtaleRingModules.{u} T (proEtaleConstantRing T A)) j).obj K))))
    (q : ℤ) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses.{u, u} X B (fun M ↦ Finite M)
      (proEtaleConstantModulePullback a B
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules.{u} T (proEtaleConstantRing T B)) q).obj
            ((SheafOfModules.constantCoefficientScalarExtensionOfUniverses.{u + 1, u, u + 1, wA, wB}
              (ProEt.topology T)
              ((ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).symm.toRingHom.comp
                (f.comp (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).toRingHom))).obj K))) := by
  sorry

end AlgebraicGeometry.Scheme
