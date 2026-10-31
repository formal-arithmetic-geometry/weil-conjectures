/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperationPreservation
public import WeilConjectures.AlgebraicGeometry.CondensedVerdierBiduality
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.CtfStabilityDirectImages
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.SixFunctors.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ScalarSixDirectImage
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.SixFunctors.CondensedCompactSupportComposition
public import WeilConjectures.SecSmoothPurity.Transport
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.IntegralProperBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteProperBaseChange
public import WeilConjectures.AlgebraicGeometry.ProperBaseChangeRationalPushforward
public import WeilConjectures.SixFunctors.DetSfCompCompositionBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.IntrinsicSitePerfectHomWindow
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHomChange
public import WeilConjectures.AlgebraicGeometry.FiniteConstructibleHom
public import WeilConjectures.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.AlgebraicGeometry.InternalHomDualTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.SfBidualityClass
public import WeilConjectures.AlgebraicGeometry.CondensedSixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.CompactSupportRealizationCoordinates

/-! # The assembled ordinary condensed six operations

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
prop-functor-package.md, opening domain paragraph and clauses 1--7
(blueprint: prop-functor-package).

The fields retain the types of the published component statements. `type_of%` is
Lean's type elaborator: the field is the proposition proved by the named component,
including all its parameters and canonical maps; the proof is not part of the field's type.
The finite etale package is only the finite-coefficient part of this interface.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
  [Fact (ell ≠ D.p)]

/-- The existing covering-sieve site-perfect predicate, through the fixed
internal/sectionwise module equivalence. This is not the stronger scalar-model condition.
Source: latest blueprint package opening paragraph; Stacks 08G5
(blueprint: prop-functor-package). -/
def IsCondensedPackageSitePerfect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (K : moduleDerived Λ X) : Prop :=
  SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, u + 1, u + 2}
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X))
    ((ModuleRingedComparison.equivalence Λ X).functor.mapDerivedCategory.obj K)

/-- The canonical full inclusion of Dctf into Dbc.
Source: latest blueprint package, opening domain paragraph
(blueprint: prop-functor-package). -/
def condensedPackageDctfToBc
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Λ X ⥤ ConstantModelBoundedConstructible Λ X :=
  (constantModelBoundedConstructible Λ X).lift (dctfPred Λ X).ι (fun K ↦ K.property.1)

/-- The canonical Verdier exchange component: inverse projection, evaluation,
constructible exceptional transposition, the dualizing compositor, tensor-Hom
transposition and the ordinary pullback/direct-image adjunction.
Source: latest blueprint prop-functor-package (7) and its Yoneda proof
(blueprint: prop-functor-package). -/
def condensedDatumVerdierExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y B : Scheme.{u}} {f : X ⟶ Y} {aY : Y ⟶ B} {aX : X ⟶ B}
    {cf : Compactification f} {cY : Compactification aY} {cX : Compactification aX}
    (Sf : CondensedSixFunctorOperationDatum Λ cf)
    (SY : CondensedSixFunctorOperationDatum Λ cY)
    (SX : CondensedSixFunctorOperationDatum Λ cX)
    (α : Sf.support ⋙ SY.support ≅ SX.support)
    (N : ConstantModelBoundedConstructible Λ B)
    (K : ConstantModelBoundedConstructible Λ X)
    (ht : constantModelBoundedConstructible Λ X
      (K.obj ⊗ (moduleObjectDerivedPullback Λ f).obj
        (internalHomObj Λ Y (Sf.support.obj K).obj (SY.dualizing N))))
    (hPF : IsIso (exceptionalProjectionMorphismOfCompactification Λ cf K.obj
      (internalHomObj Λ Y (Sf.support.obj K).obj (SY.dualizing N)))) :
    internalHomObj Λ Y (Sf.support.obj K).obj (SY.dualizing N) ⟶
      (moduleObjectDerivedPushforward Λ f).obj
        (internalHomObj Λ X K.obj (SX.dualizing N)) :=
  letI := hPF
  (derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
    (MonoidalClosed.curry
      ((Sf.adjunction.homEquiv ⟨_, ht⟩ (SY.exceptional.obj N)
        ⟨inv (exceptionalProjectionMorphismOfCompactification Λ cf K.obj
            (internalHomObj Λ Y (Sf.support.obj K).obj (SY.dualizing N))) ≫
          (ihom.ev (Sf.support.obj K).obj).app (SY.dualizing N)⟩).hom ≫
        ((conjugateIsoEquiv (Sf.adjunction.comp SY.adjunction)
          SX.adjunction α.symm).hom.app N).hom))

/-- Seven-clause package on the actual ordinary pro-etale categories, using the
recorded coefficient, compactification, scalar and adjunction interfaces.
Source: latest blueprint prop-functor-package, whole statement
(blueprint: prop-functor-package). -/
structure CondensedFunctorPackage : Prop where
  /-- Opening paragraph: pullback, tensor and both direct images on Dctf. -/
  preservation : type_of% (constructibleFiniteTor_stability_direct_images ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k))
  /-- Opening paragraph: internal Hom, retaining its actual constructible domain. -/
  internalHom : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1})
    [MonObj Λ] [IsCommMonObj Λ],
    type_of% (@internalHom_stability.{u} Λ _ _ ell _ D.k _ _ _
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k))
  /-- General finite constructible Hom, including its dimension-dependent bound. -/
  finiteConstructibleHom : type_of%
    (@WeilConjectures.finite_constructible_derivedHom_proEtale.{u} D ell _ Fact.out)
  /-- The canonical finite quotient Hom comparison, evaluation and quotient cocycles. -/
  finiteHomChange : type_of%
    (@WeilConjectures.finiteCoefficient_derivedHom_change.{u} D ell _ Fact.out)
  /-- The sharper interval and the canonical dual-tensor comparison retain the
  covering-sieve site-perfect first variable, at every coefficient stage. -/
  perfectHom : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    ∀ (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
      [QuasiCompact X.hom] [IsSeparated X.hom]
      (K L : ConstantModelConstructibleFiniteTor Λ X.left),
      IsCondensedPackageSitePerfect Λ X.left K.obj →
      IsIso (MonoidalClosed.ihomUnitTensorToIhom K.obj L.obj) ∧
      ∀ a b c d : ℤ, a ≤ b → c ≤ d →
        _root_.DerivedCategory.torAmplitudeIn _ a b K.obj →
        _root_.DerivedCategory.torAmplitudeIn _ c d L.obj →
        _root_.DerivedCategory.torAmplitudeIn _ (c - b) (d - a)
          (internalHomObj Λ X.left K.obj L.obj)
  /-- Opening paragraph: the constructible exceptional adjunction, not an ambient one. -/
  exceptionalAdjunction : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1})
    [MonObj Λ] [IsCommMonObj Λ],
    type_of% (@exceptionalInverseImage_exists.{u} Λ _ _ ell _ D.k _ _ _
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k))
  /-- Clause 1: exact scalar extension and the canonical operation comparisons. -/
  coefficientExtension : type_of% (condensedCoefficientCompatibility.{u} ell)
  /-- Clause 1: object descent and the representatives-and-eventual-equality Hom formula. -/
  coefficientDescent : type_of% (finiteCoefficientDescentTwoColimit D.k (ringChar D.k) ell
    (Fact.out : (ringChar D.k).Prime).pos (Fact.out : ringChar D.k ≠ ell))
  /-- Clause 2: ordinary scalar pullback and its original coherence data. -/
  scalarPullback : type_of% (@scalarSixPullback.{u})
  /-- Clause 2 and opening paragraph: actual general internal-Hom coefficient comparison. -/
  scalarTensorHom : type_of% (@scalarSixTensorHom.{u} ell _ D.k _ _ _)
  /-- Clause 2: ordinary direct-image coefficient comparison and its cocycles. -/
  scalarDirectImage : type_of% (@scalarSixDirectImage.{u} ell _ D.k _ _ _
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k))
  /-- Clause 2: compact-support coefficient comparison and refinement normalization. -/
  scalarCompactSupport : type_of% (@scalarSixCompactSupport.{u} ell _ D.k _ _ _
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k))
  /-- Clause 7: the exceptional scalar mate on the constructible domain. -/
  scalarExceptional : type_of% (@scalarSixExceptional.{u} ell _ D.k _ _ _
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k))
  /-- Clauses 2--4: normalized refinement, composition, units, associativity and
  arbitrary compact-support base change, with their composition/exchange equation. -/
  compactSupport : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    CompactSupportComposition.Coherent Λ D.k
  /-- Clause 4: the specified arbitrary compact-support exchange on Loc and Dctf. -/
  compactBaseChange : type_of%
    (@det_sf_comp_composition_base_change.{u} ell _ (ringChar D.k) _ D.k _ rfl _ _ _)
  /-- Clause 4: proper or smooth ordinary exchange at every admissible coefficient.
  These are the original ordinary ambient arrows, on the constructible finite-Tor input. -/
  ordinaryBaseChange : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    ∀ {X Y X' Y' : Over (Spec (.of D.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
      (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y'.left ⟶ Y.left) (g' : X'.left ⟶ X.left)
      (sq : ChosenCartesianSquare g' f'.left f.left g),
      IsProper f.left ∨ Smooth g →
      ∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
        IsIso ((condensedAmbientExchange Λ sq).app K.obj)
  /-- The finite-stage proper alternative on bounded-below torsion complexes. -/
  finiteProperBoundedBelow : type_of%
    (@AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology.{u})
  /-- The finite-stage smooth alternative on bounded-below allowable torsion complexes. -/
  finiteSmoothBoundedBelow : type_of%
    (@AlgebraicGeometry.Etale.boundedBelow_derived_smooth_baseChange.{u})
  /-- Clause 3: proper coincidence, for every compactification on the stated domain. -/
  properCoincidence : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    ∀ {X Y : Over (Spec (.of D.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (f : X ⟶ Y) [IsProper f.left] (c : Compactification f.left),
      Nonempty ((dctfPred Λ X.left).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c ≅
        (dctfPred Λ X.left).ι ⋙ moduleObjectDerivedPushforward Λ f.left)
  /-- Clause 3: the compactly supported image of the original localization triangle.
  Its first two arrows are the images of the open counit and the closed unit. -/
  compactLocalization : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    ∀ {U Z : Scheme.{u}} {X Y : Over (Spec (.of D.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (j : U ⟶ X.left) [IsOpenImmersion j] [QuasiCompact j]
      (i : Z ⟶ X.left) [IsClosedImmersion i]
      (_hij : IsCompl (Set.range i.base) (Set.range j.base))
      (f : X ⟶ Y) (c : Compactification f.left)
      (K : ConstantModelConstructibleFiniteTor Λ X.left),
      ∃ δ, Triangle.mk
        ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).counit.app
          K.obj)
        ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K.obj) δ ∈ distTriang _ ∧
        (rightDerivedLowerShriekOfCompactification Λ c).mapTriangle.obj (Triangle.mk
          ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).counit.app
            K.obj)
          ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K.obj) δ) ∈ distTriang _
  /-- Clause 5: the original compactification projection arrow, with the finite-Tor
  condition on the second factor only. -/
  projection : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    ∀ {X Y : Over (Spec (.of D.k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [IsSeparated Y.hom] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
      [QuasiCompact f.left] [IsSeparated f.left] (c : Compactification f.left)
      (K : ConstantModelBoundedConstructible Λ X.left)
      (L : ConstantModelConstructibleFiniteTor Λ Y.left),
      IsIso (exceptionalProjectionMorphismOfCompactification Λ c K.obj L.obj)
  /-- Clause 6: smooth purity and its normalized trace and all scalar/base-change laws. -/
  purity : type_of% (PurityTransport.smooth_purity_transport ell D Fact.out)
  /-- Clause 7: ordinary evaluation-defined duality, on all four coefficient stages. -/
  biduality : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ],
    type_of% (condensed_verdier_biduality Λ ell D.k (Or.inr inferInstance)
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k))
  /-- The operation datum exists at every coefficient, on constructible categories. -/
  datumExists : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    ∀ {X Y : Over (Spec (.of D.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (f : X ⟶ Y) (c : Compactification f.left),
      ∃ S : CondensedSixFunctorOperationDatum Λ c,
        ∀ K : ConstantModelBoundedConstructible Λ Y.left,
          dctfPred Λ Y.left K.obj → dctfPred Λ X.left (S.exceptional.obj K).obj
  /-- Clause 7: the canonical ordinary exchange on Dctf. The compositor is supplied
  with the operation data; its adjunction mate determines the dualizing comparison. -/
  ordinaryVerdierExchange : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    ∀ {X Y : Over (Spec (.of D.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (f : X ⟶ Y) (cf : Compactification f.left)
      (cY : Compactification Y.hom) (cX : Compactification X.hom)
      (Sf : CondensedSixFunctorOperationDatum Λ cf)
      (SY : CondensedSixFunctorOperationDatum Λ cY)
      (SX : CondensedSixFunctorOperationDatum Λ cX)
      (α : Sf.support ⋙ SY.support ≅ SX.support)
      (N : ConstantModelBoundedConstructible Λ (Spec (.of D.k))),
      N.obj = 𝟙_ (moduleDerived Λ (Spec (.of D.k))) →
      ∃ ε : (condensedPackageDctfToBc Λ X.left ⋙ Sf.support).op ⋙
          (constantModelBoundedConstructible Λ Y.left).ι.op ⋙ SY.verdier N ≅
          (dctfPred Λ X.left).ι.op ⋙ SX.verdier N ⋙
            moduleObjectDerivedPushforward Λ f.left,
        ∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
          ∃ (ht : constantModelBoundedConstructible Λ X.left
            (K.obj ⊗ (moduleObjectDerivedPullback Λ f.left).obj
              (internalHomObj Λ Y.left (Sf.support.obj
                ((condensedPackageDctfToBc Λ X.left).obj K)).obj (SY.dualizing N))))
            (hPF : IsIso (exceptionalProjectionMorphismOfCompactification Λ cf K.obj
              (internalHomObj Λ Y.left (Sf.support.obj
                ((condensedPackageDctfToBc Λ X.left).obj K)).obj (SY.dualizing N)))),
            ε.hom.app (op K) = condensedDatumVerdierExchange Λ Sf SY SX α N
              ((condensedPackageDctfToBc Λ X.left).obj K) ht hPF
  /-- Clause 7: the exceptional functor is D_X f* D_Y on its constructible domain. -/
  exceptionalDualFormula : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ell Λ →
    ∀ {X Y : Over (Spec (.of D.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (f : X ⟶ Y) (cf : Compactification f.left)
      (cY : Compactification Y.hom) (cX : Compactification X.hom)
      (Sf : CondensedSixFunctorOperationDatum Λ cf)
      (SY : CondensedSixFunctorOperationDatum Λ cY)
      (SX : CondensedSixFunctorOperationDatum Λ cX)
      (_α : Sf.support ⋙ SY.support ≅ SX.support)
      (N : ConstantModelBoundedConstructible Λ (Spec (.of D.k))),
      N.obj = 𝟙_ (moduleDerived Λ (Spec (.of D.k))) →
      Nonempty (condensedPackageDctfToBc Λ Y.left ⋙ Sf.exceptional ⋙
          (constantModelBoundedConstructible Λ X.left).ι ≅
        (dctfPred Λ Y.left).ι ⋙ (SY.verdier N).rightOp ⋙
          (moduleObjectDerivedPullback Λ f.left).op ⋙ SX.verdier N)

/-- Assemble the coefficient and functor package in the global finite-field setting.
Source: latest blueprint prop-functor-package.proof.md (blueprint: prop-functor-package).
Proof: apply constructible stability and the constructible exceptional-existence theorem;
apply the scalar-six comparisons to the listed coefficient maps; use finite-extension
flatness and finite-coefficient descent for clause 1. Use the common-dense-refinement
cocycle, proper/open composition, their unit and associativity equations, and the original
open/closed localization triangle for clauses 2--3. Apply the proper and smooth exchange
results and compact-support exchange on their original domains for clause 4. The proper
projection mate and inverse open tensor comparison give clause 5. Transport the normalized
finite smooth-purity trace through the ordinary scalar comparisons for clause 6. Apply
Verdier exchange, constructible exceptional adjunction and ordinary condensed biduality
for clause 7. Restrict every comparison to its stated full subcategory; no domain is enlarged.
-/
theorem condensedFunctorPackage : CondensedFunctorPackage ell D := by
  sorry
end AlgebraicGeometry.ProEtale.CondensedRing
