/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CompactSupportNormalizedScalarIsomorphisms
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses

import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemCompactSupportRestrictionCocycle
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel
import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # Unit and tower equations for normalized compact-support scalar comparisons

Source: Weil conjectures blueprint, lem-weil-compact-support-finite-field-independence,
first sentence, compatibility with composition and identity extensions
(blueprint: lem-weil-compact-support-normalized-scalar-descent).

The comparisons are the prescribed whole-system tensor-unit mates, rationalized in the
raw Hom scalar localizations. Only the unit and tower equations are asserted.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)

/-- The raw rationalizations of the fixed normalized compact-support scalar mates
satisfy the unit and tower equations in the actual rational derived categories.
Source: lem-weil-compact-support-finite-field-independence, first sentence,
compatibility with composition
(blueprint: lem-weil-compact-support-normalized-scalar-descent).

Proof (the seven steps of the DAG):
1. By lem-weil-compact-support-system-transpose-normalization identify the prescribed
integral maps with the fixed limits of the whole-system scalar-adjunction mates q.
Their transpose is restriction comparison composed with compact support of the unit.
The relevant Hom bijection is on whole derived systems, for every derived target.
2. Apply lem-weil-system-compact-support-restriction-cocycle: restriction comparisons
compose along A to M to N, and identity restriction has identity comparison. The
same-index valuation quotient maps commute with transitions; no flatness is needed.
3. Use lem-pur-system-scalar-coherence and lem-weil-mixed-reduction-unit-composition:
the scalar associator carries the iterated adjunction unit to the direct unit, and
the scalar unitor carries the identity-extension unit to identity. The composite
Hom bijection first transposes along N/M, then along M/A, and is injective.
4. Transpose both tower routes. Naturality moves q for M/A through the second unit;
insert the defining transpose equations for q for N/M and M/A. Naturality of the
first restriction comparison moves the second input unit through it. This calculation
is in whole derived-system Hom sets, not a lift from individual quotient indices.
5. Combine the two restriction comparisons by Step 2. Naturality for the source
associator and Step 3 reduce the transpose to that of the direct route. Injectivity
proves the system tower equation. For identity extension both unit routes transpose
to identity, proving the system unit equation by the single Hom bijection.
6. Realize on coherent reductions. By lem-coef-normalized-dvr-effectivity and
lem-coef-derived-system-evaluation-calculus the intermediate reduction-realization
counits are invertible. Their naturality moves each q through its adjacent counit,
and inverse counits cancel. The fixed system normalization therefore identifies the
realized routes with the prescribed integral routes. Use
lem-pur-coefficient-extension-reduction-model, lem-pur-completed-line-tensor-coherence
and lem-coef-semilinear-derived-sections to identify their associators and units.
This uses the actual fixed realization, without assuming finite-evaluation faithfulness.
7. Apply raw Hom scalar localization, which preserves identity and composition and
has unchanged objects. The rational action sends a tensor v to a tensor F(v), and
hence the two integral equations become exactly the two displayed rational equations.
All system identities allow repeated fields, so both conclusions include those cases. -/
/- Unit equation component of normalized compact-support scalar descent.
(blueprint: lem-weil-compact-support-normalized-scalar-descent). -/
theorem sfCompactSupportNormalizedScalarDescentUnit
    (l : ℕ) [Fact l.Prime]
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (b : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c (Coefficient.{u} l Ω A) ⋙
          integralTransition l Ω Y A B h ≅
        integralTransition l Ω X A B h ⋙
          sfCompactSupportFiniteIntegralFunctor l K₀ hl c (Coefficient.{u} l Ω B))
    (_hb : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
      SfCompactSupportIntegralBetaSpec l K₀ hl c
        (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
        (coefficientInclusion l Ω A B h) (b A B h))
    (_hsystem : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω A) X),
      ((b A B h).hom.app K).hom = sfCompactSupportScalarSystemMap l K₀ hl c
        (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
        (coefficientInclusion l Ω A B h) K)
    (β : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
      sfCompactSupportFiniteFunctor l K₀ hl c (Coefficient.{u} l Ω A) ⋙
          transition l Ω Y A B h ≅
        transition l Ω X A B h ⋙
          sfCompactSupportFiniteFunctor l K₀ hl c (Coefficient.{u} l Ω B))
    (_hβ : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B)
      (K : Stage l Ω X A), HEq ((β A B h).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω B) Y).map
          ((b A B h).hom.app K.obj))) :
    (∀ (A : Padic.FiniteCoefficientFields l Ω) (K : Stage l Ω X A),
      (β A A le_rfl).hom.app K ≫
          (sfCompactSupportFiniteFunctor l K₀ hl c (Coefficient.{u} l Ω A)).map
            ((unitor l Ω X A).hom.app K) =
        (unitor l Ω Y A).hom.app
          ((sfCompactSupportFiniteFunctor l K₀ hl c (Coefficient.{u} l Ω A)).obj K)) := by
  sorry

end WeilConjectures
