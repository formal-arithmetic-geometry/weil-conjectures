/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.PointFiniteCohomologyComplexes
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.PointFgCompleteComplexes
public import Sheaf.Paper.PointFdComplexes
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Field.ULift

import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.DerivedComplete
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.RingTheory.DerivedCompleteModuleComplex
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Sheaf.RingTheory.NilpotentTorsionDerivedLimitComplete
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.RingTheory.DerivedCompleteModuleFinite
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-!
# Finiteness of sections over the algebraically closed coefficient point

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509,
its finite, integral and rational evaluation assertions
(blueprint: lem-weil-point-sections-finiteness).

All assertions are made for every complex representative of the derived object.
Sections are evaluated at the final small pro-etale object. The scalar maps are
actual constant-section maps, and rationalization is termwise scalar extension.
The section-exactness dependency makes these formulas independent of the representative.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- The constant-section coefficient map at the final object, given by sheafification's
unit, without choosing an identification of the section ring.
Source: blueprint order 1509; Stacks Tag 03CW
(blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointConstantSectionMap (k A : Type u) [Field k] [CommRing A] :
    ULift.{u + 1, u} A →+*
      (((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).obj.obj
            (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((CategoryTheory.toSheafify (ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (ProEt.mk (𝟙 (Spec (.of k))))))).hom

/-- Final-object evaluation with scalars restricted along the actual constant-section map.
Source: blueprint order 1509; Stacks Tag 03CW
(blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointFiniteSections (k A : Type u) [Field k] [CommRing A] :=
  pointModuleSections k
      ((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))) ⋙
    ModuleCat.restrictScalars (R := ULift.{u + 1, u} A) (pointConstantSectionMap k A)

/-- Evaluation and restriction of scalars are additive, allowing termwise sections.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable instance pointFiniteSectionsAdditive (k A : Type u) [Field k] [CommRing A] :
    (pointFiniteSections k A).Additive :=
  inferInstanceAs ((pointModuleSections k _ ⋙
    ModuleCat.restrictScalars (R := ULift.{u + 1, u} A) (pointConstantSectionMap k A)).Additive)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]

/-- Integral scalars act through the limit lift of their compatible constant reductions.
This is the canonical map O_E → Γ(s, completed O_E), with only the common universe lifted.
Source: blueprint order 1509 and completed coefficients, order 1455
(blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointIntegralSectionMap :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      (((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))).obj.obj
          (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  (((integralConstantToCompletion l E (Spec (.of k))).hom.app
    (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom).comp
      (pointConstantSectionMap k (Padic.coefficientExtensionIntegers l E))

/-- Completed-coefficient sections, retaining the canonical integral coefficient action.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointIntegralSections :=
  pointModuleSections k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) ⋙
    ModuleCat.restrictScalars (pointIntegralSectionMap l E k)

/-- Additivity of completed-coefficient sections and scalar restriction.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable instance pointIntegralSectionsAdditive :
    (pointIntegralSections l E k).Additive :=
  inferInstanceAs ((pointModuleSections k _ ⋙
    ModuleCat.restrictScalars (pointIntegralSectionMap l E k)).Additive)

/-- The original inclusion O_E ↪ E, transported through the common ULift.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointIntegralToField :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+* ULift.{u + 1, u} E :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Padic.coefficientExtensionIntegers l E).subtype.comp ULift.ringEquiv.toRingHom)

/-- Tensoring with E is additive by the extension-restriction adjunction.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable instance pointIntegralToFieldAdditive :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).left_adjoint_additive

/-- Sections of a finite-torsion constructible complex have bounded finite cohomology;
sections of an integral constructible complex are bounded, finitely generated and derived
complete; their termwise rationalization has bounded finite-dimensional cohomology.

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509
(blueprint: lem-weil-point-sections-finiteness).

Proof (the six steps of the node):
1. The finite residue field of O_E gives finitely many representatives modulo the
   uniformizer. Successive expansion in these representatives proves A_(E,n) finite.
   Finite-torsion constructible cohomology comes from a constructible etale sheaf.
   On Spec k the only nonempty locally closed subscheme is itself, and its algebraically
   closed geometric stalk is its sections. The finite-level comparison unit identifies
   these with pro-etale sections. Exact sections commute with cohomology, proving clause 1.
2. The coefficient DVR is Noetherian. Compatible residues modulo uniformizer powers
   have lifts forming a Cauchy sequence in E; completeness and the ultrametric bound
   give a unique limit in O_E. Thus O_E is complete for its uniformizer ideal.
3. Apply exact sections to the integral reduction Roos triangle. Exact countable products
   are sectionwise and their cohomology is coordinatewise. The common interval for all
   reductions bounds section cohomology, with at most one extra top degree. Nilpotent
   torsion in each quotient and the derived-limit completeness theorem give derived
   completeness over O_E, without surjective cohomology transitions.
4. The two-term free resolution [O_E --uniformizer--> O_E] of the residue field,
   completed constant-sheaf reduction and a K-flat representative give the principal
   reduction cone triangle. Exact sections give an injection of H^i/ uniformizer H^i
   into the finite cohomology of the first reduction, so this residue is finitely generated.
5. The Roos description and exact products show that each section cohomology module
   is derived complete. Apply the general derived-complete-module finiteness criterion
   over the complete Noetherian DVR to its finitely generated residue. This gives finite
   generation in every degree, and with step 3 proves clause 2, including completeness.
6. The DVR coefficient theorem identifies E as O_E[1/uniformizer]. Localization is flat,
   so termwise tensor commutes with cohomology. The finite integral generating sets span
   the rational cohomology over E and preserve its finite support, proving clause 3.

Complexes are arbitrary representatives, not bounded termwise or K-flat representatives.
The exact section functor and flat rationalization descend to the derived categories.
ULift changes only coefficient size, leaving the original rings and their actions intact. -/
theorem point_sections_finiteness (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ C : CochainComplex
        (SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology (Spec (.of D.k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
                (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))))) ℤ,
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) (DerivedCategory.Q.obj C) →
        DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          (DerivedCategory.Q.obj
            (((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex
              (.up ℤ)).obj C))) ∧
    (∀ C : CochainComplex (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ℤ,
      sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj C) →
        DerivedCategory.pointFgComplete (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})
          (DerivedCategory.Q.obj
            (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)) ∧
        DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars (pointIntegralToField l E)).mapHomologicalComplex
              (.up ℤ)).obj
              (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)))) := by
  sorry

end WeilConjectures
