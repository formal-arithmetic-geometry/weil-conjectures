/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NQ and NJ
-/
module

public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage

/-!
# Completed coefficient transport and Weil categories

Source: Weil conjectures blueprint, finite coefficient and Weil-category definitions
(blueprint: def-wf-automorphism-completed-transport).

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `pbcIsoModulePullback`, `pbcIsoAmbientPullback`: exact coefficient transport.
- `pbcIsoCompletedPullback_identification`: the completed-pullback identification.
- `pbcRationalIsoPullback`: transport on the raw rational coefficient category.
- `pbcIsoRationalScalarComparison`: the normalized scalar/transport comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

include hf in
/-- The coefficient map is invertible for a scheme isomorphism.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: the site equivalence preserves all limits. Each finite constant-ring
comparison is invertible by the isomorphism inverse-image theorem. Apply
preservation of the limit to these finite comparisons. Their limit is precisely
the map defined by the recorded projection equations. -/
@[instance] theorem pbcIsoCoefficientMap_isIso : IsIso (completedCoefficientMap f d) := by
  sorry

/-- Exact module transport: inverse image followed by the canonical scalar identification.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
abbrev pbcIsoModulePullback :
    pbcModules Y (pbcAdicCompletion Y d) ⥤ pbcModules X (pbcAdicCompletion X d) :=
  proEtaleRingModulePullback f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (asIso (completedCoefficientMap f d))

/-- The module pullback is an exact equivalence with inverse transport along f inverse.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: inverse-image equivalences for the two inverse site functors identify
the completed coefficient sheaves by the finite projection equations. The
unit and counit of their site equivalence therefore lift to modules. Both
functors are exact, since site equivalences and ring identifications are exact. -/
@[instance] theorem pbcIsoModulePullback_isEquivalence :
    (pbcIsoModulePullback f d).IsEquivalence := by
  sorry

/-- The exact equivalence transported to complexes and localized at quasi-isomorphisms.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
abbrev pbcIsoAmbientPullback : PbcCompletedDerived Y d ⥤ PbcCompletedDerived X d :=
  (pbcIsoModulePullback f d).mapDerivedCategory

/-- The two recorded ordinary inverse images have the same tensor object and map formulas.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: both coefficient maps are the existing completedCoefficientMap. The ordinary
scalar extension in completedModulePullback is fixed on objects and maps by the
change-of-rings universal pair, so its formulas are precisely changeOfRings and
changeOfRingsHom. Functor extensionality gives the displayed equality.
-/
theorem pbcIsoModulePullback_eq_completed :
    pbcIsoModulePullback f d = completedModulePullback f d := by
  sorry

/-- Exact descent is the unique ordinary derived inverse image with its universal counit.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: exactness makes the termwise descent with its localization factorization a
left-derived pair. Transport its counit through the equality of the two ordinary
functors. The universal property of the recorded left-derived pair gives a unique
isomorphism satisfying the displayed complex-counit equation.
-/
theorem pbcIsoOrdinaryDerivedComparison_exists :
    ∃! alpha : completedOrdinaryPullback f d ≅ pbcIsoAmbientPullback f d,
      ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        alpha.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcIsoModulePullback f d).mapDerivedCategoryFactors.hom.app P =
          completedOrdinaryPullbackComplexCounit f d P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (eqToIso (pbcIsoModulePullback_eq_completed f d)).symm (.up ℤ)).hom.app P) := by
  sorry

/-- The comparison fixed by the two derived counits on every complex.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoOrdinaryDerivedComparison :=
  (pbcIsoOrdinaryDerivedComparison_exists f d).exists.choose

include hf in
/-- The completed comparison is invertible on the stipulated integral complete objects.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: the exact inverse site functors preserve the K-injective resolutions of strict
towers, hence their derived inverse limits and normalized constant-tower units.
Finite coefficient projections identify the transported reduction tower with the
reduction tower of the exact inverse image. The completion unit is invertible on K;
transporting this unit identifies completedPullbackComparison with an isomorphism.
-/
@[instance] theorem pbcIsoCompletedComparison_isIso
    (K : PbcBoundedConstructibleComplete Y d) :
    IsIso (completedPullbackComparison f d K.obj) := by
  sorry

/-- Completed pullback is the same coefficient transport, with its normalized comparison.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoCompletedPullback_identification (K : PbcBoundedConstructibleComplete Y d) :
    completedPullbackObject f d K.obj ≅ (pbcIsoAmbientPullback f d).obj K.obj :=
  (asIso (completedPullbackComparison f d K.obj)).symm ≪≫
    (pbcIsoOrdinaryDerivedComparison f d).app K.obj

/-- Transport preserves the specified integral full subcategory.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: the exact site equivalence and its exact inverse preserve K-injective
resolutions of strict towers, so derived inverse limits transport. The finite
quotient projections identify the reduction towers including transitions.
Thus the Koszul completeness condition is preserved. Transport every stratum,
every common local bounded model, and every etale origin and its comparison.
All normalization equations are functorial images of the original equations;
bounds and the number of strata remain unchanged. -/
theorem pbcIsoAmbientPullback_preserves
    (K : PbcBoundedConstructibleComplete Y d) :
    PbcIsBoundedConstructibleComplete X d ((pbcIsoAmbientPullback f d).obj K.obj) := by
  sorry

/-- Restriction to the full subcategory, retaining all ambient derived morphisms.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoIntegralPullback :
    PbcBoundedConstructibleComplete Y d ⥤ PbcBoundedConstructibleComplete X d :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete X d)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y d) ⋙ pbcIsoAmbientPullback f d)
    (pbcIsoAmbientPullback_preserves f d)

/-- The inverse coefficient transport preserves the same integral conditions.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: apply the completed-transport preservation argument to the inverse
scheme isomorphism. Its unit and counit restrict to the full subcategories,
giving an inverse to this integral transport. -/
@[instance] theorem pbcIsoIntegralPullback_isEquivalence :
    (pbcIsoIntegralPullback f d).IsEquivalence := by
  sorry

/-- Coefficient transport is additive and linear for the original constant-section action.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: inverse image and scalar identification respect sums sectionwise. The
finite comparisons send each constant scalar to itself; their limit therefore
intertwines the recorded constant-section actions. The same equations hold on
complexes, descend to derived morphisms, and restrict to the full subcategories. -/
theorem pbcIsoIntegralPullback_linear :
    (pbcIsoIntegralPullback f d).Additive ∧ (pbcIsoIntegralPullback f d).Linear A := by
  sorry

/-- Additivity supplied by the named coefficient-transport theorem.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
instance pbcIsoIntegralPullback_additive : (pbcIsoIntegralPullback f d).Additive :=
  (pbcIsoIntegralPullback_linear f d).1

/-- Linearity supplied by the named constant-section compatibility theorem.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
instance pbcIsoIntegralPullback_isLinear : (pbcIsoIntegralPullback f d).Linear A :=
  (pbcIsoIntegralPullback_linear f d).2

/-- On the raw rationalization transport sends a tensor a tensor u to a tensor P(u).
This construction retains precisely the original integral object representatives.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
abbrev pbcRationalIsoPullback {T : Scheme.{u}} (e : Aut T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (p : A) :
    PbcRationalCategory T d p ⥤ PbcRationalCategory T d p :=
  ScalarLocalization.map A (PbcBoundedConstructibleComplete T d) p
    (pbcIsoIntegralPullback e.hom d)


variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {T : Scheme.{u}} (e : Aut T)
  {E F : Padic.FiniteCoefficientFields l Ω}

/-- Exact transport's right adjoints commute with restriction of coefficients.
The section equation fixes the comparison, not just its isomorphism class.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: both functors have exactly the same underlying sheaf, evaluated on the
postcomposition functor of the site isomorphism. The coefficient actions agree
by the finite constant comparisons and their limit projection equations.
Identity on sections gives the isomorphism and determines it uniquely. -/
theorem pbcIsoScalarRightComparison_exists (h : E ≤ F) :
    ∃! r :
      pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω E))) ≅
        proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω F))) ⋙
          pbcRestrict (pbcCompletedScalarMap l Ω T h),
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F)))
        (U : T.ProEtᵒᵖ) (x : ((pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω E)))).obj M).val.obj U),
        HEq ((r.hom.app M).val.app U x) x := by
  sorry

/-- The right-adjoint comparison fixed by identity on sections.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoScalarRightComparison (h : E ≤ F) :
    pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω E))) ≅
        proEtaleRingModuleDirectImage e.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω F))) ⋙
          pbcRestrict (pbcCompletedScalarMap l Ω T h) :=
  (pbcIsoScalarRightComparison_exists l Ω e h).exists.choose

/-- The ordinary comparison is the mate of the sectionwise identity comparison.
This pins down its tensor normalization.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoOrdinaryScalarComparison (h : E ≤ F) :
    pbcExtend (pbcCompletedScalarMap l Ω T h) ⋙
        pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T h) :=
  (conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction e.hom _ _
        (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω E)))).comp
      (pbcScalarAdjunction (pbcCompletedScalarMap l Ω T h)))
    ((pbcScalarAdjunction (pbcCompletedScalarMap l Ω T h)).comp
      (proEtaleRingModuleAdjunction e.hom _ _
        (asIso (completedCoefficientMap e.hom (pbcStageDatum.{u} l Ω F)))))).symm
    (pbcIsoScalarRightComparison l Ω e h)

/-- The ordinary comparison on nested complex functors, using the canonical
composition isomorphisms on both sides.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoOrdinaryComplexComparison (h : E ≤ F) :
    (pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω F)).mapHomologicalComplex
        (.up ℤ) ≅
      (pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex
        (.up ℤ) ⋙
        (pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcExtend (pbcCompletedScalarMap l Ω T h) ⋙
        pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω F))) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (pbcIsoOrdinaryScalarComparison l Ω e h) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T h))) (.up ℤ)).symm

/-- The ambient comparison is fixed by the ordinary tensor comparison and the
specified universal derived counits, on complexes before localization.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: finite freeness makes scalar extension exact. The site equivalence is
exact as well. The two derived counits below are therefore invertible. Compose
these counits and the ordinary comparison on complexes; the universal property
of localization descends their conjugation uniquely to the derived categories. -/
theorem pbcIsoAmbientScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcAmbientScalarExtension l Ω T h ⋙
        pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω T h,
      ∀ P : CochainComplex
          (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ,
        c.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcAmbientScalarExtension l Ω T h).map
            ((pbcIsoModulePullback e.hom
              (pbcStageDatum.{u} l Ω E)).mapDerivedCategoryFactors.hom.app P) ≫
          pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
            (((pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex
              (.up ℤ)).obj P) =
        (pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω F)).map
            (pbcComplexCounit (pbcCompletedScalarMap l Ω T h) P) ≫
          (pbcIsoModulePullback e.hom (pbcStageDatum.{u} l Ω F)).mapDerivedCategoryFactors.hom.app
              (((pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((pbcIsoOrdinaryComplexComparison l Ω e h).hom.app P) := by
  sorry

/-- The ambient Frobenius/scalar comparison with its representative normalization.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoAmbientScalarComparison (h : E ≤ F) :
    pbcAmbientScalarExtension l Ω T h ⋙
        pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoAmbientPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω T h :=
  (pbcIsoAmbientScalarComparison_exists l Ω e h).exists.choose

variable [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Fullness restricts the normalized ambient comparison uniquely.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: both tensor extension and transport preserve the defining full
subcategories. Lift ambient components and inverses by fullness; faithfulness
proves the naturality, inverse and uniqueness equations. -/
theorem pbcIsoIntegralScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcIntegralScalarExtension l Ω T hdim hl h,
      Functor.whiskerRight c.hom
          (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))) =
        Functor.whiskerLeft
          (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)))
          (pbcIsoAmbientScalarComparison l Ω e h).hom := by
  sorry

/-- The integral comparison retaining its ambient normalization.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoIntegralScalarComparison (h : E ≤ F) :
    pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcIntegralScalarExtension l Ω T hdim hl h :=
  (pbcIsoIntegralScalarComparison_exists l Ω e hdim hl h).exists.choose

/-- Integral localization commutes with the explicitly linear coefficient transport.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: both functors have the same object function. On morphisms they both send
1 tensor u to 1 tensor P(u); the base-change linear map defining transport gives
the asserted equality of functors. -/
theorem pbcIsoRationalization (E : Padic.FiniteCoefficientFields l Ω) :
    pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) =
      pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) := by
  sorry

/-- The rational comparison is fixed on every original integral object.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport).
Proof: conjugate rationalization of the integral comparison by the displayed
integral/localization comparisons. Naturality on fractions follows by inverting
the coefficient uniformizer; all objects are integral objects, so uniqueness follows. -/
theorem pbcIsoRationalScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcScalarExtension l Ω T hdim hl h ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F) ≅
      pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcScalarExtension l Ω T hdim hl h,
      ∀ K : PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E),
        c.hom.app
            ((pbcRationalization T (pbcStageDatum.{u} l Ω E)
              (pbcStageUniformizer.{u} l Ω E)).obj K) =
          (pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F)).map
            ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
          (eqToIso (pbcIsoRationalization l Ω e F)).hom.app
            ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
          (pbcRationalization T (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F)).map
            ((pbcIsoIntegralScalarComparison l Ω e hdim hl h).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω T hdim hl h).inv.app
            ((pbcIsoIntegralPullback e.hom (pbcStageDatum.{u} l Ω E)).obj K) ≫
          (pbcScalarExtension l Ω T hdim hl h).map
            ((eqToIso (pbcIsoRationalization l Ω e E)).inv.app K) := by
  sorry

/-- The Frobenius/scalar comparison determined by canonical tensor transport.
Source: blueprint order 2106 (blueprint: def-wf-automorphism-completed-transport). -/
def pbcIsoRationalScalarComparison (h : E ≤ F) :
    pbcScalarExtension l Ω T hdim hl h ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F) ≅
      pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcScalarExtension l Ω T hdim hl h :=
  (pbcIsoRationalScalarComparison_exists l Ω e hdim hl h).exists.choose

end AlgebraicGeometry.Scheme
