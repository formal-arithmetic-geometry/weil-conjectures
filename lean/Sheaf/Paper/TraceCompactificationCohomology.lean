/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.RefinementComparisonIsomorphism
public import Sheaf.Paper.OrdinaryCompactWeilCohomology
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
import Sheaf.Paper.SfIntegralReductionTower
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.EtaleOriginDerivedCategory
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfCommonStageDirectImage
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek

/-!
# Cohomology on a chosen compactification

Source: Weil blueprint main-20261015, sec-trace-formula/sk-thm-trace-formula,
lem-trf-compactification-cohomology and its proof
(blueprint: lem-trf-compactification-cohomology).

The domain is the bounded constructible part of the recorded witness-retaining category.
The coefficient complex is the existing geometric-point fibre of the existing intrinsic
compact-support candidate. Its formula is also ordinary cohomology of extension by zero
on the proper ambient scheme. Refinement maps use the published canonical realization
comparisons; no arbitrary map or chosen etale antecedent is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- The coefficient quotient at the specified positive level is finite.
Source: blueprint coefficient conventions, proof Step 1
(blueprint: lem-trf-compactification-cohomology). -/
instance traceCompactificationCoefficientFinite (T : TraceFormulaCoefficientConventions.{u}) :
    Finite T.coefficientRing :=
  Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField T.level T.level_pos

/-- Forget the retained origin witness and realize the same complex over the intrinsic
constant coefficient sheaf. Both coefficient equivalences are the recorded ones.
Source: blueprint proof Steps 1--2 (blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationUnderlying (T : TraceFormulaCoefficientConventions.{u}) :
    RefinementFiniteLevelOrigin T.coefficients.l T.coefficientField T.level T.level_pos
        T.geometricBaseChange ⥤
      proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing :=
  letI : TopologicalSpace (ULift.{u + 1, u} T.coefficientRing) := ⊥
  letI : DiscreteTopology (ULift.{u + 1, u} T.coefficientRing) := discreteTopology_bot _
  etaleOriginForgetful T.geometricBaseChange (ULift.{u + 1, u} T.coefficientRing) ⋙
    (refinementCoefficientEquivalence T.geometricBaseChange
      (ULift.{u + 1, u} T.coefficientRing)).inverse ⋙
        (sfIntrinsicDerivedEquivalence T.geometricBaseChange T.coefficientRing).functor

/-- Restrict the recorded witnessed category to bounded constructible underlying complexes.
Morphisms remain all ambient morphisms; the antecedent and its isomorphism are retained.
Source: blueprint statement and proof Step 1
(blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationBounded (T : TraceFormulaCoefficientConventions.{u}) :
    ObjectProperty (RefinementFiniteLevelOrigin T.coefficients.l T.coefficientField T.level
      T.level_pos T.geometricBaseChange) :=
  fun O ↦ T.boundedConstructible ((traceCompactificationUnderlying T).obj O)

/-- Forget only the witness, landing in the already recorded bounded constructible category.
Source: blueprint proof Step 1 (blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationForgetful (T : TraceFormulaCoefficientConventions.{u}) :
    (traceCompactificationBounded T).FullSubcategory ⥤ T.boundedConstructible.FullSubcategory :=
  T.boundedConstructible.lift
    ((traceCompactificationBounded T).ι ⋙ traceCompactificationUnderlying T)
    (fun O ↦ O.property)

/-- The existing candidate with its recorded finite-level constructibility proof,
made functorial on all ambient input morphisms.
Source: blueprint proof Steps 3 and 6 (blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationImages (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap) :
    T.boundedConstructible.FullSubcategory ⥤
      (intrinsicFiniteTorsionConstructible T.coefficients.l T.coefficientField T.level
        T.level_pos (Spec (.of T.datum.k))).FullSubcategory := by
  letI : T.geometricBaseChange.Over (Spec (.of T.datum.k)) := ⟨T.structureMap⟩
  letI : LocallyOfFiniteType (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricFiniteType
  letI : QuasiCompact (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricQuasiCompact
  letI : IsSeparated (T.geometricBaseChange ↘ Spec (.of T.datum.k)) := T.geometricSeparated
  letI : (Spec (.of T.datum.k)).Over (Spec (.of T.datum.k)) := ⟨𝟙 _⟩
  letI : T.structureMap.IsOver (Spec (.of T.datum.k)) := ⟨Category.comp_id _⟩
  exact (intrinsicFiniteTorsionConstructible T.coefficients.l T.coefficientField T.level
    T.level_pos (Spec (.of T.datum.k))).lift
      (T.boundedConstructible.ι ⋙ sfIntrinsicCompactSupport c T.coefficientRing)
      (fun K ↦ ((finiteCompactSupportConstructibility T.coefficients.l T.coefficientField
        T.datum.k (finiteFieldDatumPrimeUnit T.datum T.coefficients.l T.coefficients.different)
        T.level T.level_pos T.structureMap).1 c).2 K.obj K.property)

/-- The existing compact-support complex, as a functor on witnessed bounded constructible
objects with values in D^b_fin(A). On a compactification c=(j,g), its underlying formula is
Fib_s(Rg_* j_! K), hence also RΓ(c.Z,j_! K). No Tor restriction is imposed.
Source: blueprint displayed comparison and proof Steps 3, 5--6
(blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationSections (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap) :
    (traceCompactificationBounded T).FullSubcategory ⥤
      (DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} T.coefficientRing)).FullSubcategory :=
  traceCompactificationForgetful T ⋙ traceCompactificationImages T c ⋙ T.pointFibre

/-- The prescribed refinement comparison in the intrinsic ambient category. The outer
isomorphisms are the published coefficient transports, and the middle is the existing
proper-composition/proper-open comparison with the retained witness.
Source: blueprint proof Steps 2 and 6 (blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationRefinementAmbient (T : TraceFormulaCoefficientConventions.{u})
    {c d : Compactification T.structureMap} (r : c ⟶ d)
    (O : RefinementFiniteLevelOrigin T.coefficients.l T.coefficientField T.level T.level_pos
      T.geometricBaseChange) :
    (sfIntrinsicCompactSupport c T.coefficientRing).obj
        ((traceCompactificationUnderlying T).obj O) ≅
      (sfIntrinsicCompactSupport d T.coefficientRing).obj
        ((traceCompactificationUnderlying T).obj O) :=
  letI : TopologicalSpace (ULift.{u + 1, u} T.coefficientRing) := ⊥
  letI : DiscreteTopology (ULift.{u + 1, u} T.coefficientRing) := discreteTopology_bot _
  (sfIntrinsicCompactSupportComparison T.coefficientRing c).app
      (refinementFiniteLevelFixedObject T.coefficients.l T.coefficientField T.level
        T.level_pos T.geometricBaseChange O) ≪≫
    (sfIntrinsicDerivedEquivalence (Spec (.of T.datum.k)) T.coefficientRing).functor.mapIso
      (refinementComparisonAtWitness (ULift.{u + 1, u} T.coefficientRing) r O) ≪≫
    (sfIntrinsicCompactSupportComparison T.coefficientRing d).symm.app
      (refinementFiniteLevelFixedObject T.coefficients.l T.coefficientField T.level
        T.level_pos T.geometricBaseChange O)

/-- Restrict the same ambient isomorphism to the already recorded constructible images.
Source: blueprint proof Step 3 (blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationRefinementImage (T : TraceFormulaCoefficientConventions.{u})
    {c d : Compactification T.structureMap} (r : c ⟶ d)
    (O : (traceCompactificationBounded T).FullSubcategory) :
    (traceCompactificationImages T c).obj ((traceCompactificationForgetful T).obj O) ≅
      (traceCompactificationImages T d).obj ((traceCompactificationForgetful T).obj O) :=
  (intrinsicFiniteTorsionConstructible T.coefficients.l T.coefficientField T.level
    T.level_pos (Spec (.of T.datum.k))).isoMk
      (traceCompactificationRefinementAmbient T r O.obj)

/-- The prescribed refinement comparison after the recorded geometric-point fibre.
The source and target are the actual finite cohomology complexes, not their direct images.
Source: blueprint proof Steps 6 and 8 (blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationRefinement (T : TraceFormulaCoefficientConventions.{u})
    {c d : Compactification T.structureMap} (r : c ⟶ d)
    (O : (traceCompactificationBounded T).FullSubcategory) :
    (traceCompactificationSections T c).obj O ≅ (traceCompactificationSections T d).obj O :=
  T.pointFibre.mapIso (traceCompactificationRefinementImage T r O)

/-- The common-refinement normalization and cocycle equations for the comparison family.
These are equations of forward maps, which determine the isomorphisms uniquely.
Source: blueprint proof Steps 7--8 (blueprint: lem-trf-compactification-cohomology). -/
def traceCompactificationComparisonLaws (T : TraceFormulaCoefficientConventions.{u})
    (C : ∀ c d : Compactification T.structureMap,
      traceCompactificationSections T c ≅ traceCompactificationSections T d) : Prop :=
  (∀ (c d e : Compactification T.structureMap) (r : e ⟶ c) (s : e ⟶ d)
          (O : (traceCompactificationBounded T).FullSubcategory),
        (C c d).hom.app O = (traceCompactificationRefinement T r O).inv ≫
          (traceCompactificationRefinement T s O).hom) ∧
      (∀ c d e : Compactification T.structureMap,
        (C c d).hom ≫ (C d e).hom = (C c e).hom)

/-- The canonical natural comparison C_(j,K), simultaneously for all compactifications.
For the compactification c₀ used to define Ra_X!, the component (C c₀ c).app O is
RΓ_c(X,K) ≅ RΓ(c.Z,c.i_! K). The normalization uses every common refinement, so the
comparison is independent of its choice and is the specified comparison on refinements.
The cocycle equation expresses compatibility with changes and their compositions.

Source: Weil blueprint main-20261015, lem-trf-compactification-cohomology,
statement and proof (blueprint: lem-trf-compactification-cohomology).

Proof:
1. The conventions give A=A_(E,n), n≥1, the algebraically closed geometric base k,
   and a separated finite-type structure map. The retained witness places every
   input in the recorded etale-origin category; bounded constructibility is imposed
   by traceCompactificationBounded. The compact-support candidate is Rg_* j_!.
2. Apply prop-compactification-coherence-detailed to the chosen and given
   compactifications. Its natural comparisons are independent of common refinement
   and equal the prescribed refinementComparisonIsomorphism on refinement arrows.
3. By prop-finite-compact-support-constructibility the two candidate values belong
   to D^b_c(s,A). Invariance under isomorphisms is
   lem-weil-proetale-dbc-triangulated.
4. The open immersion j is quasi-compact because a_X is finite type and g is
   separated (lemma-nagata-open-immersion-qc-over-separated-target), hence finite type
   (lem-weil-pbc-qc-open-immersion-finite-type); open immersions are separated.
5. Apply compactification coherence to j and its compactification (j,id). The
   candidate there is R(id)_* j_! ≅ j_!. Apply the constructibility restriction to j
   and invariance under isomorphism to see that j_! K is bounded constructible.
6. Apply the recorded geometric-point fibre to the comparison. It preserves the
   isomorphism and its inverse; def-weil-ordinary-compact-cohomology identifies the
   endpoints with RΓ_c(X,K) and RΓ(c.Z,c.i_! K). The existing realization comparison
   gives exactly traceCompactificationRefinement in intrinsic coordinates.
7. Functoriality of the fibre sends the naturality square to the asserted natural
   isomorphism, for every ambient morphism between the witnessed objects.
8. Apply the same functor to the common-refinement formula and cocycle identity.
   These give the displayed normalization and composition law, including identities,
   repeated compactifications and any further change of common refinement. -/
theorem trace_compactification_cohomology (T : TraceFormulaCoefficientConventions.{u}) :
    ∃ C : ∀ c d : Compactification T.structureMap,
        traceCompactificationSections T c ≅ traceCompactificationSections T d,
      traceCompactificationComparisonLaws T C := by
  sorry

end WeilConjectures
