/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientConventions
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.RefinementComparisonIsomorphism
public import WeilConjectures.AlgebraicGeometry.OrdinaryCompactWeilCohomology
public import WeilConjectures.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteCompactSupportConstructibility
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.AlgebraicGeometry.CompactificationCoherence
import WeilConjectures.Compactification.CategoryBaseChange

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

set_option backward.isDefEq.respectTransparency true

private theorem trace_span_precomp {C D : Type*} [Category* C] [Category* D]
    (F : C → D) (theta : ∀ {a b : C}, (a ⟶ b) → (F a ≅ F b))
    (hcomp : ∀ {a b c : C} (r : a ⟶ b) (s : b ⟶ c),
      theta (r ≫ s) = theta r ≪≫ theta s)
    {a b d e : C} (r : d ⟶ a) (s : d ⟶ b) (q : e ⟶ d) :
    (theta r).symm ≪≫ theta s = (theta (q ≫ r)).symm ≪≫ theta (q ≫ s) := by
  rw [hcomp, hcomp]
  ext
  simp

private theorem trace_span_independent {C D : Type*} [Category* C] [Category* D]
    [IsCofiltered C] (F : C → D)
    (theta : ∀ {a b : C}, (a ⟶ b) → (F a ≅ F b))
    (hcomp : ∀ {a b c : C} (r : a ⟶ b) (s : b ⟶ c),
      theta (r ≫ s) = theta r ≪≫ theta s)
    {a b d e : C} (r : d ⟶ a) (s : d ⟶ b) (r' : e ⟶ a) (s' : e ⟶ b) :
    (theta r).symm ≪≫ theta s = (theta r').symm ≪≫ theta s' := by
  obtain ⟨z, q, q', h₁, h₂⟩ := IsCofiltered.bowtie r r' s s'
  rw [trace_span_precomp F theta hcomp r s q,
    trace_span_precomp F theta hcomp r' s' q', h₁, h₂]

private theorem trace_cofiltered_comparisons {C D : Type*} [Category* C] [Category* D]
    [IsCofiltered C] (F : C → D)
    (theta : ∀ {a b : C}, (a ⟶ b) → (F a ≅ F b))
    (hcomp : ∀ {a b c : C} (r : a ⟶ b) (s : b ⟶ c),
      theta (r ≫ s) = theta r ≪≫ theta s) :
    ∃ comparison : ∀ a b : C, F a ≅ F b,
      (∀ (a b d : C) (r : d ⟶ a) (s : d ⟶ b),
        comparison a b = (theta r).symm ≪≫ theta s) ∧
      (∀ a b c : C, comparison a b ≪≫ comparison b c = comparison a c) := by
  let comparison (a b : C) : F a ≅ F b :=
    (theta (IsCofiltered.minToLeft a b)).symm ≪≫
      theta (IsCofiltered.minToRight a b)
  have h (a b d : C) (r : d ⟶ a) (s : d ⟶ b) :
      comparison a b = (theta r).symm ≪≫ theta s :=
    trace_span_independent F theta hcomp _ _ r s
  refine ⟨comparison, h, ?_⟩
  intro a b c
  let d := IsCofiltered.min (IsCofiltered.min a b) c
  let r : d ⟶ a := IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft a b
  let s : d ⟶ b := IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight a b
  let t : d ⟶ c := IsCofiltered.minToRight _ _
  rw [h a b d r s, h b c d s t, h a c d r t]
  ext
  simp

set_option maxHeartbeats 10000000 in
-- Coefficient realizations contain several nested derived functor equivalences.
private theorem trace_ambient_coherence (T : TraceFormulaCoefficientConventions.{u}) :
    ∃ theta : ∀ (c d : Compactification T.structureMap) (_r : c ⟶ d),
        traceCompactificationUnderlying T ⋙ sfIntrinsicCompactSupport c T.coefficientRing ≅
          traceCompactificationUnderlying T ⋙ sfIntrinsicCompactSupport d T.coefficientRing,
      (∀ (c d : Compactification T.structureMap) (r : c ⟶ d) O,
        (theta c d r).app O = traceCompactificationRefinementAmbient T r O) ∧
      (∀ (c d e : Compactification T.structureMap) (r : c ⟶ d) (s : d ⟶ e),
        theta c e (r ≫ s) = theta c d r ≪≫ theta d e s) := by
  classical
  let : T.geometricBaseChange.Over (Spec (.of T.datum.k)) := ⟨T.structureMap⟩
  let : (Spec (.of T.datum.k)).Over (Spec (.of T.datum.k)) := ⟨𝟙 _⟩
  let : LocallyOfFiniteType (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricFiniteType
  let : QuasiCompact (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricQuasiCompact
  let : T.structureMap.IsOver (Spec (.of T.datum.k)) := ⟨Category.comp_id _⟩
  let : TopologicalSpace (ULift.{u + 1, u} T.coefficientRing) := ⊥
  let : DiscreteTopology (ULift.{u + 1, u} T.coefficientRing) := discreteTopology_bot _
  let F := etaleOriginForgetful T.geometricBaseChange
      (ULift.{u + 1, u} T.coefficientRing) ⋙
    (refinementCoefficientEquivalence T.geometricBaseChange
      (ULift.{u + 1, u} T.coefficientRing)).inverse
  let q := (sfIntrinsicDerivedEquivalence (Spec (.of T.datum.k)) T.coefficientRing).functor
  let B (c : Compactification T.structureMap) :
      traceCompactificationUnderlying T ⋙ sfIntrinsicCompactSupport c T.coefficientRing ≅
        compactificationOriginCandidate T.coefficients.l T.coefficientField
          T.level T.level_pos c ⋙ q :=
    Functor.isoWhiskerLeft F (sfIntrinsicCompactSupportComparison T.coefficientRing c)
  obtain ⟨theta, htheta, _, hcomp, _⟩ := compactification_coherence T.datum.k
    T.coefficients.l
    (finiteFieldDatumPrimeUnit T.datum T.coefficients.l T.coefficients.different)
    T.coefficientField T.level T.level_pos T.structureMap
  let theta' (c d : Compactification T.structureMap) (r : c ⟶ d) :=
    B c ≪≫ Functor.isoWhiskerRight (theta c d r) q ≪≫ (B d).symm
  refine ⟨theta', ?_, ?_⟩
  · intro c d r O
    change (B c).app O ≪≫ q.mapIso ((theta c d r).app O) ≪≫ ((B d).app O).symm = _
    rw [htheta]
    rfl
  · intro c d e r s
    dsimp only [theta']
    rw [hcomp]
    simp only [Functor.isoWhiskerRight_trans]
    apply Iso.ext
    simp

set_option maxHeartbeats 10000000 in
-- The underlying functor maps contain nested coefficient and full-subcategory transports.
private theorem trace_refinement_naturality
    (T : TraceFormulaCoefficientConventions.{u})
    {c d : Compactification T.structureMap} (r : c ⟶ d)
    (O P : (traceCompactificationBounded T).FullSubcategory) (k : O ⟶ P) :
    (traceCompactificationImages T c).map
        ((traceCompactificationForgetful T).map k) ≫
      (traceCompactificationRefinementImage T r P).hom =
    (traceCompactificationRefinementImage T r O).hom ≫
      (traceCompactificationImages T d).map
        ((traceCompactificationForgetful T).map k) := by
  obtain ⟨theta, htheta, _⟩ := trace_ambient_coherence T
  have h := (theta c d r).hom.naturality k.hom
  apply ObjectProperty.hom_ext
  change (sfIntrinsicCompactSupport c T.coefficientRing).map
      ((traceCompactificationUnderlying T).map k.hom) ≫
        (traceCompactificationRefinementAmbient T r P.obj).hom =
    (traceCompactificationRefinementAmbient T r O.obj).hom ≫
      (sfIntrinsicCompactSupport d T.coefficientRing).map
        ((traceCompactificationUnderlying T).map k.hom)
  simpa only [Functor.comp_map, ← Iso.app_hom, htheta] using h

set_option maxHeartbeats 10000000 in
-- Checking the coefficient transports unfolds large derived-category functor expressions.
private noncomputable def traceCompactificationTheta
    (T : TraceFormulaCoefficientConventions.{u})
    {c d : Compactification T.structureMap} (r : c ⟶ d) :
    traceCompactificationSections T c ≅ traceCompactificationSections T d :=
  NatIso.ofComponents (fun O ↦ traceCompactificationRefinement T r O) (by
    intro O P k
    change T.pointFibre.map ((traceCompactificationImages T c).map
          ((traceCompactificationForgetful T).map k)) ≫
        T.pointFibre.map (traceCompactificationRefinementImage T r P).hom =
      T.pointFibre.map (traceCompactificationRefinementImage T r O).hom ≫
        T.pointFibre.map ((traceCompactificationImages T d).map
          ((traceCompactificationForgetful T).map k))
    rw [← T.pointFibre.map_comp, ← T.pointFibre.map_comp]
    exact congrArg (fun q ↦ T.pointFibre.map q)
      (trace_refinement_naturality T r O P k))

set_option maxHeartbeats 10000000 in
-- The component equation compares maps in the recorded derived full subcategories.
private theorem traceCompactificationTheta_comp
    (T : TraceFormulaCoefficientConventions.{u})
    {c d e : Compactification T.structureMap} (r : c ⟶ d) (s : d ⟶ e) :
    traceCompactificationTheta T (r ≫ s) =
      traceCompactificationTheta T r ≪≫ traceCompactificationTheta T s := by
  obtain ⟨theta, htheta, hcomp⟩ := trace_ambient_coherence T
  apply Iso.ext
  apply NatTrans.ext
  funext O
  change T.pointFibre.map (traceCompactificationRefinementImage T (r ≫ s) O).hom =
    T.pointFibre.map (traceCompactificationRefinementImage T r O).hom ≫
      T.pointFibre.map (traceCompactificationRefinementImage T s O).hom
  rw [← T.pointFibre.map_comp]
  apply congrArg (fun q ↦ T.pointFibre.map q)
  apply ObjectProperty.hom_ext
  change (traceCompactificationRefinementAmbient T (r ≫ s) O.obj).hom =
    (traceCompactificationRefinementAmbient T r O.obj).hom ≫
      (traceCompactificationRefinementAmbient T s O.obj).hom
  have h := congrArg (fun n ↦ n.app O.obj) (hcomp c d e r s)
  simp only [NatIso.trans_app, htheta] at h
  exact congrArg Iso.hom h

set_option maxHeartbeats 10000000 in
-- Checking the coefficient transports unfolds large derived-category functor expressions.
private theorem traceCompactificationComparison
    (T : TraceFormulaCoefficientConventions.{u}) :
    ∃ C : ∀ c d : Compactification T.structureMap,
        traceCompactificationSections T c ≅ traceCompactificationSections T d,
      (∀ (c d e : Compactification T.structureMap) (r : e ⟶ c) (s : e ⟶ d),
        C c d = (traceCompactificationTheta T r).symm ≪≫
          traceCompactificationTheta T s) ∧
      (∀ c d e : Compactification T.structureMap,
        C c d ≪≫ C d e = C c e) := by
  classical
  let : T.geometricBaseChange.Over (Spec (.of T.datum.k)) := ⟨T.structureMap⟩
  let : LocallyOfFiniteType (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricFiniteType
  let : QuasiCompact (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricQuasiCompact
  let : IsSeparated (T.geometricBaseChange ↘ Spec (.of T.datum.k)) := T.geometricSeparated
  let : IsCofiltered (Compactification T.structureMap) :=
    Compactification.isCofiltered_of_field
      (T.geometricBaseChange ↘ Spec (.of T.datum.k))
      (𝟙 (Spec (.of T.datum.k))) T.structureMap
      (by change T.structureMap = T.structureMap; rfl)
  exact trace_cofiltered_comparisons
    (C := Compactification T.structureMap)
    (D := ((traceCompactificationBounded T).FullSubcategory ⥤
      (DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} T.coefficientRing)).FullSubcategory))
    (fun c ↦ traceCompactificationSections T c)
    (fun {_ _} r ↦ traceCompactificationTheta T r)
    (by intro c d e r s; exact traceCompactificationTheta_comp T r s)

set_option maxHeartbeats 10000000 in
-- Evaluating the functor isomorphisms checks the full coefficient realization.
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
  obtain ⟨C, hC, hCocycle⟩ := traceCompactificationComparison T
  refine ⟨C, ?_⟩
  constructor
  · intro c d e r s O
    have h := congrArg (fun n ↦ n.hom.app O) (hC c d e r s)
    simpa [traceCompactificationTheta] using h
  · intro c d e
    exact congrArg Iso.hom (hCocycle c d e)

end WeilConjectures
