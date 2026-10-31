/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedExceptionalReconstructionData
import WeilConjectures.AlgebraicGeometry.CondensedExceptionalSystemRecognition
import WeilConjectures.AlgebraicGeometry.CondensedExceptionalCounitRepresentation
import WeilConjectures.AlgebraicGeometry.CondensedExceptionalRealizationProperties
import WeilConjectures.AlgebraicGeometry.CondensedExceptionalRefinementCounits

/-! # Assembly of condensed exceptional reconstruction

Source: current blueprint sec-smooth-purity, sk-prop-sp-integral-adjunction,
sk-prop-sp-rational, sk-thm-sp-qbar, sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local instance high] CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [local instance high] AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_additive
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_limits
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_colimits
  SheafOfModules.CoefficientSystemOrdinaryImage.systemInverseAdditive
  SheafOfModules.CoefficientSystemOrdinaryImage.inverseAdditive
  WeilConjectures.PurityFiniteSetting.ClopenSequenceRealizationData.ordinaryAdditive
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] CategoryTheory.mateEquiv CategoryTheory.conjugateEquiv
attribute [local irreducible] DerivedCategory.Q
  CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] AlgebraicGeometry.ProEtale.SemilinearProperOpen.J
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.R
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.adj
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.rightAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting
variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
attribute [local instance] CondensedERealization.At.encodingAdditive
  CondensedERealization.At.encodingInverseAdditive
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] WeilConjectures.purCoefficientModel
attribute [local irreducible] Datum.condensedCounit Datum.extendedCounit Datum.projectedCounit
  Datum.realizedCounit condensedScalar condensedProjection realization Datum.LimitMap
variable {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
  [f.IsOver (Spec (.of k))] {c : Compactification f}

private theorem transpose_isIso
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) {M : A} {L : B} (t : F.obj M ⟶ L)
    (h : ∀ Z : A, Function.Bijective (fun a : Z ⟶ M ↦ F.map a ≫ t)) :
    IsIso (adj.homEquiv M L t) := by
  apply isIso_of_yoneda_map_bijective
  intro Z
  have he : (fun a : Z ⟶ M ↦ a ≫ adj.homEquiv M L t) =
      fun a ↦ adj.homEquiv Z L (F.map a ≫ t) := by
    funext a
    exact (adj.homEquiv_naturality_left a t).symm
  rw [he]
  exact (adj.homEquiv Z L).bijective.comp (h Z)

private theorem transpose_naturality
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) {M M' : A} {L L' : B}
    (t : F.obj M ⟶ L) (t' : F.obj M' ⟶ L') (a : M ⟶ M') (b : L ⟶ L')
    (h : F.map a ≫ t' = t ≫ b) :
    a ≫ adj.homEquiv M' L' t' = adj.homEquiv M L t ≫ G.map b := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right, h]

private def comparison_result
    (D : CondensedERealization.Data l (Field.{u} l) k)
    {P : Context l k X Y f c}
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (d : Datum l k P) (hd : d.Admissible l k) (s : SystemIdentification l k d hd)
    (h : ∀ Z : Omega l X.scheme,
      Function.Bijective (fun a : Z ⟶ (realization l k D X).obj
          (d.integral l k hd.reconstructs) ↦
        (CondensedRing.boundedConstructibleLowerShriekOfCompactification l (f := X.map Y f) c).map a ≫
            d.condensedCounit l k D hd.reconstructs A s.reduction s.theta
              s.originUnit s.originSupport)) : Conclusion l k D d hd A where
  theta := s.theta
  supplied := s.supplied
  brownBound := s.brownBound
  levels := s.levels
  reduction := s.reduction
  originUnit := s.originUnit
  originSupport := s.originSupport
  invertible := by
    unfold Datum.comparison
    exact transpose_isIso
      (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction l (f := X.map Y f) c) _ h



private theorem comparisons_exist
    (D : CondensedERealization.Data l (Field.{u} l) k)
    (P : Context l k X Y f c)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c) :
    Nonempty (AtCompactification l k D P A) := by
  obtain ⟨S⟩ := condensed_exceptional_system_recognition l k P
  obtain ⟨hb, hn⟩ := condensed_exceptional_counit_representation l k P D A
  let q := fun d hd ↦ comparison_result l k D A d hd (S.result d hd) (hb d hd (S.result d hd))
  refine ⟨{ result := q, naturality := ?_, singleDegreeMaps := ?_ }⟩
  · intro d e hd he b a ha
    unfold Conclusion.iso
    dsimp only [asIso, comparison_result]
    unfold Datum.comparison
    exact transpose_naturality
      (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction l (f := X.map Y f) c) _ _ _ _
      (hn d e hd he (S.result d hd) (S.result e he) b a ha)
  · intro d e hd he r b a hr hs
    exact S.singleDegree d e hd he r b a hr hs



@[irreducible] private def chosenComparison
    (D : CondensedERealization.Data l (Field.{u} l) k)
    (P : Context l k X Y f c)
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c) :
    AtCompactification l k D P A :=
  (comparisons_exist l k D P A).some


private theorem assemble_family
    (C : CompactSupportCondensedRealization.ComparisonFamily l k)
    (context : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c : Compactification f), Context l k X Y f c)
    (hcontext : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c : Compactification f),
      (context X Y f c).reduction = (C.coefficient (Field.{u} l)).reduction)
    (properties : RealizationProperties l k (C.coefficient (Field.{u} l)).realization)
    (q : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c : Compactification f),
      AtCompactification l k (C.coefficient (Field.{u} l)).realization (context X Y f c)
        (specifiedSupport l k C (context X Y f c) (hcontext X Y f c)))
    (h : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c d : Compactification f) (r : c.Refinement d)
      (v : Datum l k (context X Y f c)) (w : Datum l k (context X Y f d))
      (hv : v.Admissible l k) (hw : w.Admissible l k) (b : v.L ≅ w.L),
      RefinementCompatibility l k (C.coefficient (Field.{u} l)).realization X Y f c d r
        (context X Y f c) (context X Y f d)
        (specifiedSupport l k C (context X Y f c) (hcontext X Y f c))
        (specifiedSupport l k C (context X Y f d) (hcontext X Y f d))
        (q X Y f c) (q X Y f d) v w hv hw b) :
    Nonempty (Family l k C context hcontext) :=
  ⟨{ properties := properties, comparison := q, refinement := h }⟩


attribute [local irreducible] ComparisonNaturality SingleDegreeCompatibility
  RefinementCompatibility specifiedSupport

/-- Reconstruction identifies the supplied finite exceptional system with the exact chosen
condensed constructible right adjoint, preserving the specified counit, system maps,
compactification refinements, the coefficient unit, and shifts.

Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical; upstream UpperShriek.lean,
`boundedConstructibleUpperShriekOfCompactification` and its specifying adjunction.
(blueprint: lem-pur-condensed-exceptional-reconstruction).

Proof plan:
1. Apply lem-pur-integral-reduction-uniform-tor to the integral input and all integral
   test reductions. They lie in the common bounded constructible finite-Tor domains;
   these bounds require no smoothness.
2. Apply lem-pur-etale-tower-brown-adjunction for the ordinary etale Brown adjunction,
   then lem-pur-brown-tower-finite-site-comparison to the reduction of L. The bounds
   supplied by phi give bounded-below site transport, its actual counit, and the
   finite exceptional coefficient-mate transitions. Normalize the equivalent strict
   system presentations on sections and complex representatives.
3. Apply lem-pur-integral-reconstructed-representing-pair. Alternative (a) retains the
   specified theta. In (b), good truncation identifies both systems with their
   degree-r cohomology diagrams, and the compatible phi_n give theta there. The
   same-degree full faithfulness makes level squares sufficient for system naturality.
   The actual total limit represents Hom(P_R K,L), with precisely the finite counits.
4. Apply lem-pur-reconstructed-pair-finite-scalar-extension at each finite coefficient
   extension. Transpose the extended counit to construct the Brown-system comparison,
   also at ramified extensions; do not lift arbitrary diagrams of derived maps.
   The resulting finite-field representing bijections preserve the specified counits.
5. Apply lem-pur-filtered-condensed-representing-pair. The compatible finite-field
   bijections give the closure-coefficient representing bijection. Transpose its
   extended counit under the exact chosen bounded constructible adjunction. The
   represented Hom bijection makes this transpose invertible and natural in supplied
   actual system maps; its hom is the comparison defined above.
6. Apply lem-pur-reconstructed-pair-refinement-coherence to the actual system
   comparisons. Its reconstructed counit equation gives the displayed refinement
   square. Ordinary mate pasting gives the corresponding condensed right-adjoint
   equation, including common-refinement independence and the refinement cocycle.
7. The realization J is derived scalar extension. Tensor multiplication identifies
   B tensor_A A with B, with inverse b mapped to b tensor 1. Extending to the
   finite-subfield-valued closure gives U of the completed coefficient equal to the
   condensed unit. K-flat change of rings and exact condensed coefficient extension
   commute with shifts, giving the displayed natural shift comparisons. -/
theorem condensed_exceptional_reconstruction
    (C : CompactSupportCondensedRealization.ComparisonFamily l k)
    (context : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c : Compactification f), Context l k X Y f c)
    (hcontext : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c : Compactification f),
      (context X Y f c).reduction = (C.coefficient (Field.{u} l)).reduction) :
    Nonempty (Family l k C context hcontext) := by
  classical
  let q : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c : Compactification f),
      AtCompactification l k (C.coefficient (Field.{u} l)).realization (context X Y f c)
        (specifiedSupport l k C (context X Y f c) (hcontext X Y f c)) :=
    fun X Y f _ c ↦ chosenComparison l k (C.coefficient (Field.{u} l)).realization
      (context X Y f c) (specifiedSupport l k C (context X Y f c) (hcontext X Y f c))
  exact assemble_family l k C context hcontext
    (condensed_exceptional_realization_properties l k
      (C.coefficient (Field.{u} l)).realization).some q
    (fun X Y f _ c d r v w hv hw b ↦
      condensed_exceptional_refinement_counits l k C X Y f c d r
        (context X Y f c) (context X Y f d) (hcontext X Y f c) (hcontext X Y f d)
        (q X Y f c) (q X Y f d) v w hv hw b)

end WeilConjectures.CondensedExceptionalReconstruction
