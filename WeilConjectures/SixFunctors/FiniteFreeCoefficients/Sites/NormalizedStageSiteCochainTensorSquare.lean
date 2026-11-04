/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-!
# Signed cochain lift of the scalar/site tensor square

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 07A4 and 0G7E;
finite coefficient scalar/site transport in the blueprint
lem-coef-finite-free-extension, Paragraphs 1--3.
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace WeilConjectures.FiniteFreeCoefficients.Sites

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

-- The existing sheafified scalar balancing tensorator (`composeAndSheafifyOplaxMonoidal`),
-- specialized to the etale site, as in `NormalizedStageSiteSheafTensorSquare`.
local instance etaleScalarOplax {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

-- The ordinary etale scalar extension is a left adjoint (Stacks 06YY), so it preserves the
-- coproducts of the signed total tensor; `ExceptionalCoefficientMaps` is not imported here.
local instance etaleScalarIsLeftAdjoint {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).IsLeftAdjoint :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ X).isLeftAdjoint

/-- The termwise canonical scalar/site mate on ordinary cochain complexes.
Source: Stacks 03EL and 07A4
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
abbrev scalarSiteCochain
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  (NatTrans.mapHomologicalComplex
    (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv (.up ℤ)).app P

/-- Signed total tensor comparison for the etale-to-pro-etale inverse image.
Its homogeneous summands are the ordinary site tensor maps.
Source: Stacks 03EL and 07A4
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
abbrev siteTensorCochain (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)).app P).app Q

/-- Signed total tensor comparison for ordinary etale scalar extension.
Source: Stacks 07A4, normalized scalar tensor maps
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
abbrev etaleScalarTensorCochain
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.etaleSheafExtendScalars φ X)).app P).app Q

/-- Signed total tensor comparison for ordinary pro-etale scalar extension.
Source: Stacks 07A4, normalized scalar tensor maps
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
abbrev proEtaleScalarTensorCochain
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P Q : CochainComplex
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :=
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.sheafExtendScalars φ X)).app P).app Q

/-- The scalar/site square for signed total tensors commutes before localization.

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 07A4 and 0G7E;
latest blueprint lem-coef-finite-free-extension, Paragraphs 1--3.
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square)

Proof:
1. In degree n, form the direct sum over p + q = n of the ordinary scalar/site tensor
maps. All four functors are additive left adjoints and preserve these direct sums.
The four total comparisons above are exactly this canonical construction, using
`CochainComplex.mapBifunctor` for the signed total tensor.
2. Naturality in each variable commutes with the two differentials separately.
Additivity commutes with the scalar (-1)^p in the second differential, and all maps
preserve the bidegree, so the Koszul signs on both paths are the same.
3. On each summand the ordinary sheaf tensor square gives equality: locally each route
sends b tensor (p tensor q) to (b tensor p) tensor (1 tensor q). The direct-sum universal
property proves the equality of components, hence of cochain maps. The flat-term
K-flat hypotheses are retained as the representative context of the assertion.
-/
theorem normalized_stage_site_cochain_tensor_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hPflat : ∀ n : ℤ, ObjectProperty.flat (P.X n))
    (_hQflat : ∀ n : ℤ, ObjectProperty.flat (Q.X n))
    (_hPK : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (_hQK : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    ((ProEtale.sheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).map
          (siteTensorCochain A X P Q) ≫
        proEtaleScalarTensorCochain φ X
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
            (.up ℤ)).obj P)
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
            (.up ℤ)).obj Q) ≫
        (scalarSiteCochain φ X P ⊗ₘ scalarSiteCochain φ X Q) =
      scalarSiteCochain φ X (P ⊗ Q) ≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapHomologicalComplex
          (.up ℤ)).map (etaleScalarTensorCochain φ X P Q) ≫
        siteTensorCochain B X
          (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P)
          (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj Q) := by
  sorry

end WeilConjectures.FiniteFreeCoefficients.Sites
