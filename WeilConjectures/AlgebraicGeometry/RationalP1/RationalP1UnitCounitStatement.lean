/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveNormalizedUnitCounitRestriction
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitInversionCondition
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1CounitInversionCondition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingTwist
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LocalizingPreservation
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperProjectionFormulaField

/-! # Rational projective-line unit and counit statement

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-unit-counit.md,
definition clauses (1)--(3) and final exact-functor assertion
(blueprint: det-prop-p1-adjunction-rational-unit-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

-- Keep the ordinary derived categories visible to instance search.
attribute [local instance 30000] instCategoryDerivedCategory CategoryTheory.Mod.instCategory
attribute [local instance 1] ProjectionMorphismData.category
attribute [local irreducible] coefficient line secondLineComparison
  firstProjection secondProjection square condensedAmbientExchange
  tensorShiftIso twist rationalTwistFunctor projectionMateMap
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CondensedRing.upperStar CondensedRing.lowerStar

private theorem rational_closure_eq
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] :
    localizingClosureProEtale (coefficient l c).X Z =
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X Z) := by
  have hc :
      Nonempty (coefficient l c ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[l])) ∨
      Nonempty (coefficient l c ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[l])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (coefficient l c ≅ Mon.mk (Profinite.padicIntegersRingObj l E)) ∨
        Nonempty (coefficient l c ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (coefficient l c ≅ Mon.mk (Profinite.padicAlgClRingObj l)) := by
    cases c with
    | none =>
      unfold coefficient
      exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
    | some E =>
      unfold coefficient
      exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))
  unfold localizingClosureProEtale
  rw [(integral_ctf_equals_bc l Z (coefficient l c) hc).2.2.2]

-- The fixed left projection is the symmetry conjugate of the published right mate.
attribute [-instance] internalMonoidal in
private theorem trace_projection_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X))
    (h : IsIso (moduleObjectProjectionMate Λ f N K)) :
    IsIso (traceProjection Λ f K N) := by
  have := h
  unfold traceProjection
  infer_instance

private theorem normalized_left_projection_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X))
    (h : IsIso (moduleObjectProjectionMate Λ f N K)) : IsIso (a f K N) := by
  unfold ProjectionNormalized ProjectionFamily internalMonoidal
    internalTensorBundle nativeTensorBundle at *
  dsimp only at ha
  rw [eq_of_heq (ha f K N)]
  exact trace_projection_isIso Λ f K N h

attribute [-instance] internalMonoidal in
private theorem left_projection_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X))
    (h : IsIso (moduleObjectProjectionMap Λ f N K)) :
    IsIso (projectionMap Λ f K N) := by
  have hm : IsIso (moduleObjectProjectionMate Λ f N K) := by
    unfold moduleObjectProjectionMate moduleObjectDerivedTensorComparison
    exact h
  exact normalized_left_projection_isIso Λ _ (projection_existsUnique Λ).exists.choose_spec
    f K N hm

set_option maxHeartbeats 1000000 in
-- Specializing the field projection formula elaborates the bundled derived functors.
private theorem counit_inversion_current
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (K : rationalLocalizingCategory (coefficient l c).X Y) :
    CounitInversionCondition (coefficient l c).X Y (line l c) K.obj := by
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ l) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  have h := localizingPreservationChecks l c k p hpl Y
  have := h.geometry.qcqsY.1
  have := h.geometry.qcqsY.2
  have := h.geometry.qcqsP.1
  have := h.geometry.qcqsP.2
  let : (ProjectiveLine Y).Over (Spec (.of k)) :=
    ⟨(ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k)))
  have : QuasiCompact (Over.mk (Y ↘ Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
  have : IsSeparated (Over.mk (Y ↘ Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
  have : LocallyOfFiniteType (Over.mk (ProjectiveLine Y ↘ Spec (.of k))).hom :=
    h.geometry.standingP.2.1
  have : QuasiCompact (Over.mk (ProjectiveLine Y ↘ Spec (.of k))).hom :=
    h.geometry.standingP.2.2
  have : IsSeparated (Over.mk (ProjectiveLine Y ↘ Spec (.of k))).hom :=
    h.geometry.standingP.1
  let q : Over.mk (ProjectiveLine Y ↘ Spec (.of k)) ⟶ Over.mk (Y ↘ Spec (.of k)) :=
    Over.homMk (ProjectiveLine Y ↘ Y) rfl
  have : IsProper q.left := h.geometry.properQ
  have hc : (∃ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk (coefficient l c).X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk (coefficient l c).X ≅ Mon.mk (Profinite.padicAlgClRingObj l)) := by
    cases c with
    | none =>
      unfold coefficient
      exact Or.inr ⟨Iso.refl _⟩
    | some E =>
      unfold coefficient
      exact Or.inl ⟨E, ⟨Iso.refl _⟩⟩
  have hloc := (localizingClosure_exists (coefficient l c).X (ProjectiveLine Y)
    (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))).2.2.2
  have := hloc.1.1
  have hline := ObjectProperty.le_shift
    (CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))) (2 : ℤ) _
    (hloc.2.1 _ h.objectsP.positiveLine)
  unfold CounitInversionCondition
  apply left_projection_isIso
  apply (projectionFormulaField l (k := k) (X := Over.mk (ProjectiveLine Y ↘ Spec (.of k)))
    (Y := Over.mk (Y ↘ Spec (.of k))) (coefficient l c).X hc).2 q
  · change localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y) _
    rw [rational_closure_eq l c (ProjectiveLine Y)]
    exact hline
  · change localizingClosureProEtale (coefficient l c).X Y _
    rw [rational_closure_eq l c Y]
    exact K.property

set_option maxHeartbeats 4000000 in
-- The displayed localizing-category lifts and their component normalizations require
-- unfolding several existing derived-functor interfaces during statement elaboration.
/--
The diagonal tensor isomorphism, the section identification, and the normalized
unit/counit formulas for the rational projective line.  The two coefficient cases
are represented by the canonical continuous finite-extension ring or the canonical
finite-subextension-valued algebraic-closure ring.  The component normalizations
are exactly the displayed diagonal insertion and trace contraction; no triangle
identity is asserted here.

Source document: `literature/blueprint/latest/blueprint/part-six-operations/`
`sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/`
`sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-unit-counit.md`,
clauses (1)--(3) and final sentence; proof in the adjacent `.proof.md` document
(blueprint: det-prop-p1-adjunction-rational-unit-counit).

Proof:
1. The canonical diagonal tensor map restricts to the identity comparison on the
   diagonal, since the first projection composed with the diagonal is the identity.
   On the open complement its source and target vanish. These restrictions jointly
   detect isomorphisms, so the map is invertible. Its construction is natural in
   the complex, giving the stated natural isomorphism with the prescribed components.
2. The second projection composed with the diagonal is the identity, giving the
   section identification. Tensor with the fixed diagonal class and push forward;
   the proper base-change isomorphism for the self-cartesian square, followed by
   the Tate-line comparison, gives the displayed unit on the localizing category.
3. Invert the fixed projection-formula isomorphism and compose with tensoring the
   trace. This is the displayed counit. Naturality of tensor, proper base change,
   and the projection formula proves naturality of both composites. Preservation
   of the localizing subcategories lifts their components to the full subcategories.
4. The localizing closures are triangulated, and restriction of the ambient exact
   functors gives `RestrictionExact` for the specified lifts. Each normalized
   component is the fixed ambient composite, so faithful full inclusions and
   componentwise equality give uniqueness of the natural-transformation pair.
-/
theorem rationalUnitCounitStatement
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (_hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (_hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (_hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (family : Family l Y) (_reference : Reference l Y δ family) :
    let P : ObjectProperty (DerivedCategory
        (Modules (coefficient l c).X (ProjectiveLine Y))) :=
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))
    let Q : ObjectProperty (DerivedCategory (Modules (coefficient l c).X Y)) :=
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X Y)
    (∃ a : moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y) ⋙
          tensorRight ((moduleObjectDerivedPushforward (coefficient l c).X
            (diagonalImmersion Y)).obj (unit (coefficient l c).X (ProjectiveLine Y))) ≅
          moduleObjectDerivedPushforward (coefficient l c).X (diagonalImmersion Y),
        ∀ M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)),
          a.hom.app M = diagonalTensorMap (coefficient l c).X Y M) ∧
    ∃ (hF : ∀ M : P.FullSubcategory,
        Q ((moduleObjectDerivedPushforward (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj M.obj))
      (hG : ∀ K : Q.FullSubcategory,
        P ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y) ⋙
          twist (coefficient l c).X (ProjectiveLine Y)
            (line l c (ProjectiveLine Y))).obj K.obj))
      (F : P.FullSubcategory ⥤ Q.FullSubcategory)
      (G : Q.FullSubcategory ⥤ P.FullSubcategory),
      F = Q.lift (P.ι ⋙ moduleObjectDerivedPushforward (coefficient l c).X
          (ProjectiveLine Y ↘ Y)) hF ∧
      G = P.lift (Q.ι ⋙ moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y) ⋙ twist (coefficient l c).X
            (ProjectiveLine Y) (line l c (ProjectiveLine Y))) hG ∧
      ∃ (hP : P.IsTriangulated) (hQ : Q.IsTriangulated),
        letI : P.IsTriangulated := hP
        letI : Q.IsTriangulated := hQ
        RestrictionExact P Q F ∧ RestrictionExact Q P G ∧
        ∃! a : (𝟭 P.FullSubcategory ⟶ F ⋙ G) ×
            (G ⋙ F ⟶ 𝟭 Q.FullSubcategory),
          (∀ M : P.FullSubcategory,
            UnitComponentNormalized (coefficient l c).X Y (line l c)
              (diagram l c Y family) (secondLineComparison l c k p hpl Y)
              M.obj (a.1.app M).hom) ∧
          (∀ K : Q.FullSubcategory,
            CounitComponentNormalized (coefficient l c).X Y (line l c)
              (diagram l c Y family) K.obj (a.2.app K).hom) := by
  have h := localizingPreservationChecks l c k p hpl Y
  let P : ObjectProperty (DerivedCategory
      (Modules (coefficient l c).X (ProjectiveLine Y))) :=
    CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))
  let Q : ObjectProperty (DerivedCategory (Modules (coefficient l c).X Y)) :=
    CategoryTheory.localizingClosure (constantModelBoundedConstructible (coefficient l c).X Y)
  change _ ∧ _
  have hP : P.IsTriangulated := h.pushQ.sourceTriangulated
  have hQ : Q.IsTriangulated := h.pushQ.targetTriangulated
  let := hP
  let := hQ
  have : P.IsClosedUnderIsomorphisms :=
    (localizingClosure_exists (coefficient l c).X (ProjectiveLine Y)
      (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))).2.2.2.1.2.1
  have : Q.IsClosedUnderIsomorphisms :=
    (localizingClosure_exists (coefficient l c).X Y
      (constantModelBoundedConstructible (coefficient l c).X Y)).2.2.2.1.2.1
  have hF := fun M : P.FullSubcategory ↦ h.pushQ.preserves M.obj M.property
  have hG := fun K : Q.FullSubcategory ↦ h.twistedPullQ.preserves K.obj K.property
  let F := Q.lift (P.ι ⋙ moduleObjectDerivedPushforward (coefficient l c).X
    (ProjectiveLine Y ↘ Y)) hF
  let G := P.lift (Q.ι ⋙ moduleObjectDerivedPullback (coefficient l c).X
    (ProjectiveLine Y ↘ Y) ⋙
    twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))) hG
  obtain ⟨sF, htF⟩ := h.pushQ.exactRestriction
  obtain ⟨sG, htG⟩ := h.twistedPullQ.exactRestriction
  let := sF
  let := sG
  let := htF.1
  let := htG.1
  have hFE : RestrictionExact P Q F := by
    exact ⟨inferInstance, inferInstance⟩
  have hGE : RestrictionExact Q P G := by
    exact ⟨inferInstance, inferInstance⟩
  have := h.geometry.closedDiagonal
  have := h.geometry.quasiCompactComplement
  obtain ⟨ha, _, hu⟩ := projective_normalized_unit_counit_restriction
    (coefficient l c).X Y (diagonalImmersion Y).openComplement.toScheme
    (diagonalImmersion Y).openComplement.ι
    (by rw [Scheme.Opens.range_ι]; rfl)
    (line l c) (diagram l c Y family) (secondLineComparison l c k p hpl Y)
    P Q hF hG F G rfl rfl hFE hGE
    (unitInversions l c k p hpl Y)
    (counit_inversion_current l c k p hpl Y)
  exact ⟨ha, hF, hG, F, G, rfl, rfl, hP, hQ, hFE, hGE, hu⟩

end AlgebraicGeometry.ProEtale.RationalP1
