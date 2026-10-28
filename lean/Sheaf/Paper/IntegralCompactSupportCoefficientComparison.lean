/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.IntegralCompactSupportScalarTensor

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.CompactSupportRepresentativeIndependence
public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Sheaf.CategoryTheory.CompactSupportRoosCofinality
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.SixFunctors.ExactLocalizationInverseMate
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import all WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import all Sheaf.Paper.WfConstructibleTensorKoszulUnit
import Sheaf.Paper.ProjectionTensorCoefficientComparison
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.OrdinaryCompletedIntegralPullback
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField
import Sheaf.Paper.IntegralCompactSupportRestrictionShift
import Sheaf.Paper.FiniteProperComparisonIso
import Sheaf.Paper.CompletedQuotientProperMate

/-! # Integral compact-support coefficient comparison

Source: Weil blueprint, sk-thm-purity-transport, Step 3; Bhatt--Scholze,
Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).

## Main statements

* `recordedComparisonIso`: the canonical comparison on the recorded support functors.
* `comparisonIso`: its ambient proper/open presentation on the finite-Tor domain.
* `integralCoefficientComparison`: invertibility and constructible completeness.
* `comparison_reduction`, `comparison_quotients`, `comparison_strict_towers`:
  the actual finite maps and strict Roos presentations.
* `comparison_projection`, `comparison_commShift`, `comparison_refinement`:
  projection, shift and normalized compactification compatibility.
* `comparison_identity`, `comparison_composition`: the scalar unit and associativity laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures.PurCompactSupport
attribute [local instance 100000] CategoryTheory.HasSheafify.isRightAdjoint
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
attribute [local irreducible] CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Localization.Monoidal.tensorBifunctor
  HasDerivedCategory.standard CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

attribute [local instance 100000] coefficientSiteSmall coefficientRingSheafify
  coefficientAbSheafify coefficientAbLocallyBijective

private theorem scalarKanCommShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

-- The comparison determines the shift structure by Kan uniqueness, degree by degree.
private theorem scalarRightKanShift_unique
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ]
    {E : Type*} [Category* E] [HasShift E ℤ]
    (F : C ⥤ E) [F.CommShift ℤ] (Q : C ⥤ D) [Q.CommShift ℤ]
    (LF : D ⥤ E) (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α]
    (s t : LF.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift α ℤ)
    (ht : letI := t; NatTrans.CommShift α ℤ) : s = t := by
  have square (q : LF.CommShift ℤ) (hq : letI := q; NatTrans.CommShift α ℤ)
      (n : ℤ) (X : C) :
      LF.map ((Q.commShiftIso n).hom.app X) ≫
          (Functor.commShiftIso LF (self := q) n).hom.app (Q.obj X) ≫
            (shiftFunctor E n).map (α.app X) =
        α.app ((shiftFunctor C n).obj X) ≫ (F.commShiftIso n).hom.app X := by
    let := q
    have := hq
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm α n X
  have he (n : ℤ) : Functor.commShiftIso LF (self := s) n =
      Functor.commShiftIso LF (self := t) n := by
    apply Iso.ext
    apply Functor.kanShiftHom_ext F Q LF α n
    intro X
    apply (cancel_epi (LF.map ((Q.commShiftIso n).hom.app X))).1
    simpa only [Category.assoc] using (square s hs n X).trans (square t ht n X).symm
  exact scalarKanCommShift_ext s t he

private theorem inverse_mate_shift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ D} {H : E ⥤ F} {L₁ : C ⥤ E} {R₁ : E ⥤ C}
    {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) [a.CommShift ℤ] [b.CommShift ℤ]
    (t : TwoSquare R₁ H G R₂) [NatTrans.CommShift t.natTrans ℤ] :
    NatTrans.CommShift ((mateEquiv a b).symm t).natTrans ℤ := by
  change NatTrans.CommShift
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight a.unit (G ⋙ L₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
      Functor.whiskerRight (Functor.whiskerLeft L₁ t.natTrans) L₂ ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L₁ ⋙ H) b.counit ≫
      (Functor.rightUnitor _).hom) ℤ
  infer_instance

/-- Normalization of a shift structure by the actual universal scalar counit.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def IsScalarShiftNormalized {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (s : (pbcDerivedExtend a).CommShift ℤ) : Prop :=
  letI := s
  (pbcExtensionCounit a).CommShift ℤ

/-- The derived scalar counit uniquely normalizes its shift structure.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: ordinary additive scalar extension commutes with shifts degreewise. The
universal left-derived counit lifts this square uniquely to the localization.
The lifted squares satisfy zero and addition because their composites with the
universal counit do. This gives existence, and the same uniqueness gives uniqueness. -/
theorem scalarCommShift_existsUnique {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ∃! s : (pbcDerivedExtend a).CommShift ℤ, IsScalarShiftNormalized a s := by
  have := pbcDerivedExtension_universal a
  have hkan := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (pbcDerivedExtend a) (pbcExtensionCounit a)
    (HomotopyCategory.quasiIso (pbcModules W R) (.up ℤ))
  have := hkan
  obtain ⟨s, hs⟩ := Functor.rightKanExtension_coherentShift _
    DerivedCategory.Qh (pbcDerivedExtend a) (pbcExtensionCounit a) hkan
  exact ⟨s, hs, fun t ht ↦ scalarRightKanShift_unique _ _ _ _ t s ht hs⟩

/-- The scalar shift is fixed by its universal derived counit.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
instance scalarCommShift {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (pbcDerivedExtend a).CommShift ℤ :=
  (scalarCommShift_existsUnique a).exists.choose

/-- The shift on compact support is exact open descent followed by the canonical
K-injective proper-image shift. Source: Stacks Tags 03DI, 070K
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
instance imageCommShift (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (image R c).CommShift ℤ := by
  unfold image
  infer_instance

/-- The scalar mate commutes with the canonical shift comparisons.
Source: Stacks Tag 07A6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: on complexes the coefficient maps are degreewise and commute with shift without
an extra sign. The exact open comparison and the right-derived proper comparison
preserve their universal counits and units. Transpose this identity under the derived
scalar adjunctions; the triangle identities give precisely NatTrans.CommShift. -/
theorem comparison_commShift {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (comparison a c).CommShift ℤ := by
  letI : (pbcDerivedRestrict (a.map X)).CommShift ℤ :=
    (pbcDerivedScalarAdjunction (a.map X)).rightAdjointCommShift ℤ
  letI : (pbcDerivedRestrict (a.map Y)).CommShift ℤ :=
    (pbcDerivedScalarAdjunction (a.map Y)).rightAdjointCommShift ℤ
  have hAdjX := (pbcDerivedScalarAdjunction (a.map X)).commShift_of_leftAdjoint ℤ
  have hAdjY := (pbcDerivedScalarAdjunction (a.map Y)).commShift_of_leftAdjoint ℤ
  letI : (pbcDerivedScalarAdjunction (a.map X)).CommShift ℤ := hAdjX
  letI : (pbcDerivedScalarAdjunction (a.map Y)).CommShift ℤ := hAdjY
  letI : (image R c).CommShift ℤ := imageCommShift R c
  letI : (image S c).CommShift ℤ := imageCommShift S c
  have hres : NatTrans.CommShift (restriction a c).hom ℤ :=
    restriction_commShift a c
  unfold comparison
  exact inverse_mate_shift
    (pbcDerivedScalarAdjunction (a.map X))
    (pbcDerivedScalarAdjunction (a.map Y))
    (TwoSquare.mk _ _ _ _ (restriction a c).hom)
/-- Ordinary tensor associativity, fixed by the two tensor-unit normalized adjunctions.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def tensorComposition {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (d : R ⟶ T) (h : a ≫ b = d) :
    pbcDerivedExtend a ⋙ pbcDerivedExtend b ≅ pbcDerivedExtend d :=
  (((pbcDerivedScalarAdjunction a).comp (pbcDerivedScalarAdjunction b)).ofNatIsoRight
    (pbcDerivedRestrictComp a b d h)).leftAdjointUniq (pbcDerivedScalarAdjunction d)

/-- Scalar composition, including quotient reductions, for the specified mates.
Source: Stacks Tag 07A6, mate pasting
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: transpose under the scalar adjunctions. The tensor-composition maps carry the
successive units to the direct unit. The proper restriction comparisons compose
because their ordinary maps are identity on sections and their derived units agree.
The open comparisons compose by their unit normalization. Thus the two transposes
are equal. The Hom adjunction is bijective, which proves the displayed equality. -/
theorem comparison_composition {R S T : Coefficients.{u}}
    (a : Change R S) (b : Change S T) (d : Change R T)
    (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (pbcDerivedExtend (b.map Y)).map ((comparison a c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
        (image T c).map ((tensorComposition (a.map X) (b.map X) (d.map X) (h X)).hom.app M) =
      (tensorComposition (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
          ((image R c).obj M) ≫ (comparison d c).app M := by
  sorry

/-- Identity scalar restriction has the identity section functions, uniquely.
Source: Stacks Tag 03DA
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: the restricted action along identity is the original action. Identity on the
underlying abelian sheaf is linear and natural. Sectionwise faithfulness gives uniqueness. -/
theorem restrictIdentity_existsUnique {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    ∃! e : pbcRestrict (𝟙 R) ≅ 𝟭 _,
      ∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (e.hom.app M).val.app U x = x := by
  let eM (M : pbcModules W R) : (pbcRestrict (𝟙 R)).obj M ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App (RingHom.id (R.obj.obj U)) rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))
  let e : pbcRestrict (𝟙 R) ≅ 𝟭 _ :=
    NatIso.ofComponents eM (fun f ↦ by ext U x; rfl)
  refine ⟨e, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e' he'
    apply Iso.ext
    ext M U x
    exact he' M U x

/-- The multiplication unit C_R,R is conjugate to identity scalar restriction.
Source: Stacks Tags 03DA, 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def tensorIdentity {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    pbcDerivedExtend (𝟙 R) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (pbcDerivedScalarAdjunction (𝟙 R))
    (Adjunction.id : (𝟭 (DerivedCategory (pbcModules W R))) ⊣ 𝟭 _)).symm
      (Functor.mapDerivedCategoryNatIso (restrictIdentity_existsUnique R).exists.choose ≪≫
        Functor.mapDerivedCategoryIdIso _)).symm

/-- Multiplication normalizes the identity coefficient comparison.
Source: Stacks Tags 03DA, 07A6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: transpose the identity coefficient square. Its section maps are identities,
its proper derived comparison preserves the derived unit, and its open mate
preserves the open unit. The scalar multiplication iso is their conjugate, so the
two composites have identical transposes and hence are equal. -/
theorem comparison_identity {R : Coefficients.{u}} (a : Change R R)
    (h : ∀ W : Scheme.{u}, a.map W = 𝟙 (R.ring W))
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (comparison a c).app M ≫ (image R c).map
        ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h X)) ≪≫
          tensorIdentity (R.ring X)).hom.app M) =
      (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h Y)) ≪≫
        tensorIdentity (R.ring Y)).hom.app ((image R c).obj M) := by
  sorry

attribute [local irreducible] scalarTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Proper derived composition is the conjugate of this normalized pullback composition.
Source: Stacks Tag 0D6D
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def geometricPushComposition (R : Coefficients.{u})
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction k (R.ring W) (R.ring V) (R.pull k)).comp
      (proEtaleRingDerivedAdjunction h (R.ring V) (R.ring U) (R.pull h)))
    (proEtaleRingDerivedAdjunction (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)))
    (geometricPullComposition R h k hc)

/-- Pullback pasting along a refinement, including the equation of its open triangle.
Source: Stacks Tags 03D8, 0D6D
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def refinementPull (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i)) :
    pull R d.i ≅ pull R r.hom ⋙ pull R c.i :=
  eqToIso (congrArg (fun g : X ⟶ d.Z ↦ pull R g) r.i_hom.symm) ≪≫
    geometricPullComposition R c.i r.hom hc

/-- Restricting the proper refinement image to X, via the proper counit.
This is the normalization used to specify the proper-open comparison.
Source: blueprint prop-compactification-coherence, proof part (a)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def refinementRestriction (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (pull R d.i).obj ((push R r.hom).obj
        ((openExtension R c.i).mapDerivedCategory.obj M)) ⟶
      (pull R c.i).obj ((openExtension R c.i).mapDerivedCategory.obj M) :=
  (refinementPull R r hc).hom.app _ ≫
    (pull R c.i).map ((proEtaleRingDerivedAdjunction r.hom
      (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app _)

/-- The canonical scalar/pullback comparison is the unique left-adjoint comparison
conjugate to the normalized proper-image restriction square.
Source: Stacks Tags 03D8, 06YY, 07A6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def scalarPull {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    pull R g ⋙ pbcDerivedExtend (a.map U) ≅ pbcDerivedExtend (a.map V) ⋙ pull S g :=
  (((proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)).comp
    (pbcDerivedScalarAdjunction (a.map U))).ofNatIsoRight
      (proEtaleRingRestrictionDerivedDirectImage g
        (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).symm).leftAdjointUniq
          ((pbcDerivedScalarAdjunction (a.map V)).comp
            (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g)))

/-- Arithmetic restriction retains precisely the positive exponents e(n+1).
Source: Stacks Tags 0941, 0H9K
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
abbrev retainedTower {A : Type a} [Category.{b} A] [Abelian A]
    (e : ℕ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  CategoryTheory.StrictTowerArithmetic.index e ⋙ T

/-- Both signed Roos coordinates specify the canonical cofinal map; the shifted
coordinate is the block sum, rather than just the selected tower evaluations.
Source: Stacks Tags 0941, 0H9K
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def IsCofinalRoosMap {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (e : ℕ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (ρ : integralOperationsRoos T ⟶ integralOperationsRoos (retainedTower e T)) : Prop :=
  ∀ i : ℤ,
    ρ.f i ≫ (CochainComplex.mappingCocone.fst
        (scalarRoosBoundary (retainedTower e T))).f i =
      (CochainComplex.mappingCocone.fst
        (scalarRoosBoundary T)).f i ≫
          (CategoryTheory.StrictTowerArithmetic.selection e T).f i ∧
    ρ.f i ≫ (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary (retainedTower e T))).v
          i (i - 1) (sub_eq_add_neg i (1 : ℤ)).symm =
      (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary T)).v
          i (i - 1) (sub_eq_add_neg i (1 : ℤ)).symm ≫
            (CategoryTheory.StrictTowerArithmetic.block e T).f (i - 1)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The actual completed coefficient inclusion, with its residue-normalized pullback square.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def completedChange : Change (completed l E) (completed l F) where
  map := completedCoefficientMap l E F i
  square := completedChange_square l E F i

/-- The proper coefficient arrow: its scalar-adjunction mate is the canonical
K-injective restriction comparison. Equivalently its proper-adjunction transpose is
pullback/tensor balancing followed by scalar extension of the proper counit.
Source: Stacks Tags 07A6, 0B56
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def properComparison {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g) ⋙
        pbcDerivedExtend (a.map V) ⟶
      pbcDerivedExtend (a.map U) ⋙
        proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g) :=
  ((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
    (pbcDerivedScalarAdjunction (a.map V))).symm
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv)).natTrans

/-- The open coefficient arrow is the mate of the open-unit normalized restriction square.
Source: Stacks Tag 0E8I
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def openComparison {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (openExtension R j).mapDerivedCategory ⋙ pbcDerivedExtend (a.map V) ⟶
      pbcDerivedExtend (a.map U) ⋙ (openExtension S j).mapDerivedCategory :=
  ((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
    (pbcDerivedScalarAdjunction (a.map V))).symm
      (TwoSquare.mk _ _ _ _ (openRestriction a j).hom)).natTrans

private theorem doubleInverseMate_isIso
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    IsIso ((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))).natTrans := by
  have h := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))
  rw [h]
  change IsIso ((conjugateEquiv (a.comp x) (u.comp b)).symm q.inv)
  infer_instance

/-- The canonical open coefficient arrow is an identification, without a flatness
hypothesis on the coefficient map.
Source: Stacks Tag 0E8I
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: the exact-localization mate theorem identifies the specified open restriction
square with the inverse mate of the canonical pullback/restriction isomorphism.
The scalar inverse mate defining openComparison is consequently a double inverse
mate. The iterated-mate identity identifies it with conjugation under the composite
scalar/open adjunctions. Conjugation preserves isomorphisms, as do evaluation functors. -/
theorem openComparison_isIso {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (M : DerivedCategory (pbcModules U (R.ring U))) :
    IsIso ((openComparison a j).app M) := by
  let φ := proEtaleRingRestrictionPullbackInv
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  have : IsIso φ := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  let q := (asIso φ).symm
  have : IsIso ((mateEquiv (openAdjunction S j) (openAdjunction R j)).symm
      (TwoSquare.mk _ _ _ _ q.hom)).natTrans := by
    change IsIso (openRestrictionMap a j)
    infer_instance
  have h := (exact_localization_inverse_mate
    (openAdjunction S j) (openAdjunction R j) q).2.1
  have h' : ((mateEquiv (openDerivedAdjunction S j) (openDerivedAdjunction R j)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso q).hom)).natTrans =
        (openRestriction a j).hom := h
  unfold openComparison
  rw [← h']
  have hi := doubleInverseMate_isIso
    (pbcDerivedScalarAdjunction (a.map U)) (pbcDerivedScalarAdjunction (a.map V))
    (openDerivedAdjunction S j) (openDerivedAdjunction R j)
    (Functor.mapDerivedCategorySquareIso q).symm
  exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hi M


/-- The ordered proper/open factorization holds before any inverse limit is taken.
It is applied below to each ramified finite quotient.
Source: Stacks Tags 07A6, 0E8I
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: expand the mate defining comparison. Naturality moves the open square across
the proper scalar unit, and the scalar triangle identities cancel the middle counit
and unit. The remaining composite is the proper mate followed by the proper image
of the open mate. These are equations of natural transformations. -/
theorem comparison_factorization {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (pbcModules X (R.ring X))) :
    (comparison a c).app K =
      (properComparison a c.g).app ((openExtension R c.i).mapDerivedCategory.obj K) ≫
        (proEtaleRingDerivedDirectImage c.g (S.ring Y) (S.ring c.Z) (S.pull c.g)).map
          ((openComparison a c.i).app K) := by
  let α := TwoSquare.mk _ _ _ _ (openRestriction a c.i).hom
  let β := TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionDerivedDirectImage c.g
      (R.ring Y) (S.ring Y) (R.ring c.Z) (S.ring c.Z)
      (a.map Y) (a.map c.Z) (R.pull c.g) (S.pull c.g) (a.square c.g)).inv
  let adjX := pbcDerivedScalarAdjunction (a.map X)
  let adjZ := pbcDerivedScalarAdjunction (a.map c.Z)
  let adjY := pbcDerivedScalarAdjunction (a.map Y)
  have hv : TwoSquare.vComp α β = (restriction a c).hom := by
    ext K
    simp only [TwoSquare.vComp, α, β, restriction, TwoSquare.mk, TwoSquare.natTrans,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
  have h := mateEquiv_vcomp adjX adjZ adjY
    ((mateEquiv adjX adjZ).symm α) ((mateEquiv adjZ adjY).symm β)
  simp only [Equiv.apply_symm_apply, hv] at h
  have h' := congrArg (fun t ↦ ((mateEquiv adjX adjY).symm t).app K) h
  simpa only [Equiv.symm_apply_apply, α, β, adjX, adjZ, adjY,
    comparison, image, properComparison, openComparison, TwoSquare.hComp, TwoSquare.mk,
    TwoSquare.natTrans, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id] using h'.symm

attribute [local irreducible] properComparison openComparison

/-- The ramification hypothesis identifies ideals, and does not equate the chosen
uniformizers. Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def Ramification (e : ℕ) : Prop :=
  Ideal.map (integralScalarIntegerInclusion l E F i)
      (Padic.coefficientExtensionIdeal l E 1) =
    Padic.coefficientExtensionIdeal l F e

/-- A source uniformizer power is killed in the retained target quotient.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: map the source principal ideal through the integer inclusion and use the
ramification ideal equality. Taking nth powers gives the ideal generated by the
eth times nth target uniformizer power. Its image in the displayed quotient is zero. -/
theorem ramifiedKernel (e : ℕ) (he : Ramification l E F i e) (n : ℕ)
    (x : Padic.coefficientExtensionIntegers l E)
    (hx : x ∈ Padic.coefficientExtensionIdeal l E n) :
    Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (e * n))
      (integralScalarIntegerInclusion l E F i x) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmap : Ideal.map (integralScalarIntegerInclusion l E F i)
      (Padic.coefficientExtensionIdeal l E n) =
        Padic.coefficientExtensionIdeal l F (e * n) := by
    have he' := he
    change Ideal.map (integralScalarIntegerInclusion l E F i)
      (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1) =
        Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ e at he'
    simp only [pow_one] at he'
    simp only [Padic.coefficientExtensionIdeal, Ideal.map_pow, he', pow_mul]
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hx

/-- The actual retained quotient inclusion A_E,n to A_F,en.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def ramifiedMap (e : ℕ) (he : Ramification l E F i e) (n : ℕ) :
    Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l F (e * n) :=
  Ideal.Quotient.lift (Padic.coefficientExtensionIdeal l E n)
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (e * n))).comp
      (integralScalarIntegerInclusion l E F i))
    (ramifiedKernel l E F i e he n)

/-- The constant-sheaf map induced by the ramified quotient inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def ramifiedSheafMap (e : ℕ) (he : Ramification l E F i e) (n : ℕ)
    (W : Scheme.{u}) :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ramifiedMap l E F i e he n).ulift.{u + 1, u + 1})

/-- The quotient inclusion commutes with the actual constant-ring inverse-image maps.
Source: Stacks Tag 03CO
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: both maps carry a constant section represented by x to the constant section
represented by i(x). Inverse image and sheafification preserve that identity; constant
sections locally generate the constant sheaves, so the maps agree. -/
theorem finiteChange_square (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) (hn : 1 ≤ n) {U V : Scheme.{u}} (g : U ⟶ V) :
    ((finite l E n hn).pull g).hom ≫ ramifiedSheafMap l E F i e he n U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (ramifiedSheafMap l E F i e he n V) ≫
          ((finite l F (e * n) (Nat.mul_pos hepos hn)).pull g).hom := by
  exact (proEtaleConstantInverseImageMap_naturality g
    (CommRingCat.ofHom (ramifiedMap l E F i e he n).ulift.{u + 1, u + 1})).symm

/-- The specified finite coefficient change for the retained levels.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteChange (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) (hn : 1 ≤ n) :
    Change (finite l E n hn) (finite l F (e * n) (Nat.mul_pos hepos hn)) where
  map := ramifiedSheafMap l E F i e he n
  square := finiteChange_square l E F i e he hepos n hn

/-- Completed projections commute with the actual inverse-image identifications.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: under the inverse-image adjunction both maps are the same finite projection
of the canonical completed structure map. The finite projection normalization of
completedPullMap identifies them. -/
theorem projection_square (n : ℕ) (hn : 1 ≤ n)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ((completed l E).pull g).hom ≫ projection l E n hn U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (projection l E n hn V) ≫
        ((finite l E n hn).pull g).hom := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ n =>
    let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
    change (adj.homEquiv _ _).symm (sfCompletedCoefficientMap l E g) ≫
        completedIntegralCommRingProjectionUnrestricted l E U n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (completedIntegralCommRingProjectionUnrestricted l E V n) ≫
        (adj.homEquiv _ _).symm
          (proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1)))
    rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_left_symm]
    exact congrArg (adj.homEquiv _ _).symm
      ((sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec n)

/-- Reduction means ordinary derived tensor along the specified limit projection.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def reduction (n : ℕ) (hn : 1 ≤ n) : Change (completed l E) (finite l E n hn) where
  map := projection l E n hn
  square := projection_square l E n hn

private theorem quotientSheafFactor (m n k : ℕ) (hn : n ≤ m) (h : k = m + 1)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l F k)
    (hφ : ∀ x : Padic.coefficientExtensionIntegers l E,
      φ (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F k)
          (integralScalarIntegerInclusion l E F i x)) (W : Scheme.{u}) :
    integralScalarQuotientSheafMap l E F i W m =
      compactSupportLevelSheafQuotient l E W m n hn ≫
        (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom φ.ulift.{u + 1, u + 1}) ≫
        eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
          (Padic.coefficientExtensionRing l F k)) h) := by
  subst k
  simp only [eqToHom_refl, Category.comp_id, integralScalarQuotientSheafMap,
    compactSupportLevelSheafQuotient]
  rw [← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  apply ULift.ext
  induction x using Quotient.inductionOn' with
  | h x => exact (hφ x).symm

/-- The completed inclusion reduces to the specified retained quotient inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: evaluate the two maps on constant integral sections. Both take x to i(x)
modulo the eth times nth target uniformizer power. The quotient lift and the completed
map are normalized by precisely these sections, so the maps agree. -/
theorem ramified_reduction_square (e : ℕ) (he : Ramification l E F i e)
    (hepos : 1 ≤ e) (n : ℕ) (hn : 1 ≤ n) (W : Scheme.{u}) :
    (completedChange l E F i).map W ≫ projection l F (e * n) (Nat.mul_pos hepos hn) W =
      projection l E n hn W ≫ (finiteChange l E F i e he hepos n hn).map W := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ n =>
    have hm : 1 ≤ e * (n + 1) := Nat.mul_pos hepos (Nat.le_add_left 1 n)
    have hmn : n ≤ e * (n + 1) - 1 := by
      have h : n + 1 ≤ e * (n + 1) := by
        calc
          n + 1 = 1 * (n + 1) := (one_mul _).symm
          _ ≤ e * (n + 1) := Nat.mul_le_mul_right _ hepos
      omega
    have hq : integralScalarQuotientSheafMap l E F i W (e * (n + 1) - 1) =
        compactSupportLevelSheafQuotient l E W (e * (n + 1) - 1) n hmn ≫
          ramifiedSheafMap l E F i e he (n + 1) W ≫
          eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
            (Padic.coefficientExtensionRing l F k)) (Nat.sub_add_cancel hm).symm) := by
      exact quotientSheafFactor l E F i _ n _ hmn (Nat.sub_add_cancel hm).symm
        (ramifiedMap l E F i e he (n + 1)) (fun _ ↦ rfl) W
    change completedCoefficientMap l E F i W ≫
        (completedIntegralCommRingProjectionUnrestricted l F W (e * (n + 1) - 1) ≫ _) = _
    have hp : completedCoefficientMap l E F i W ≫
        completedIntegralCommRingProjectionUnrestricted l F W (e * (n + 1) - 1) =
        completedIntegralCommRingProjectionUnrestricted l E W (e * (n + 1) - 1) ≫
          integralScalarQuotientSheafMap l E F i W (e * (n + 1) - 1) :=
      (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec _
    let q : proEtaleConstantRing W (Padic.coefficientExtensionRing l F (e * (n + 1))) ≅
        integralCoefficientCommRingSheaf l F W (e * (n + 1) - 1) :=
      eqToIso (congrArg (fun k ↦ proEtaleConstantRing W
        (Padic.coefficientExtensionRing l F k)) (Nat.sub_add_cancel hm).symm)
    let pE := completedIntegralCommRingProjectionUnrestricted l E W (e * (n + 1) - 1)
    let pF := completedIntegralCommRingProjectionUnrestricted l F W (e * (n + 1) - 1)
    let r := compactSupportLevelSheafQuotient l E W (e * (n + 1) - 1) n hmn
    let φ := ramifiedSheafMap l E F i e he (n + 1) W
    change completedCoefficientMap l E F i W ≫ (pF ≫ q.inv) =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫ φ
    calc
      _ = (completedCoefficientMap l E F i W ≫ pF) ≫ q.inv :=
        (Category.assoc _ _ _).symm
      _ = (pE ≫ integralScalarQuotientSheafMap l E F i W (e * (n + 1) - 1)) ≫
          q.inv := congrArg (fun v : completedIntegralCommRingSheafUnrestricted l E W ⟶
            integralCoefficientCommRingSheaf l F W (e * (n + 1) - 1) ↦ v ≫ q.inv) hp
      _ = (pE ≫ (r ≫ φ ≫ q.hom)) ≫ q.inv :=
        congrArg (fun v : integralCoefficientCommRingSheaf l E W
            (e * (n + 1) - 1) ⟶ integralCoefficientCommRingSheaf l F W
            (e * (n + 1) - 1) ↦ (pE ≫ v) ≫ q.inv) hq
      _ = (pE ≫ r) ≫ φ := by
        simp only [Category.assoc, q.hom_inv_id, Category.comp_id]
      _ = _ := congrArg (fun v : completedIntegralCommRingSheafUnrestricted l E W ⟶
          integralCoefficientCommRingSheaf l E W n ↦ v ≫ φ)
        (compactSupportProjection_comp l E W (e * (n + 1) - 1) n hmn)


/-- Tensor balancing for a commutative coefficient square, with ordinary associators.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def tensorSquare {W : Scheme.{u}}
    {R S A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : A ⟶ B) (r : R ⟶ A) (s : S ⟶ B) (h : a ≫ s = r ≫ b) :
    pbcDerivedExtend a ⋙ pbcDerivedExtend s ≅ pbcDerivedExtend r ⋙ pbcDerivedExtend b :=
  tensorComposition a s (a ≫ s) rfl ≪≫ (tensorComposition r b (a ≫ s) h.symm).symm

private theorem comparisonSquare {R S A B : Coefficients.{u}}
    (a : Change R S) (b : Change A B) (r : Change R A) (s : Change S B)
    (h : ∀ W, a.map W ≫ s.map W = r.map W ≫ b.map W)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (pbcDerivedExtend (s.map Y)).map ((comparison a c).app M) ≫
        (comparison s c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
        (image B c).map
          ((tensorSquare (a.map X) (b.map X) (r.map X) (s.map X) (h X)).hom.app M) =
      (tensorSquare (a.map Y) (b.map Y) (r.map Y) (s.map Y) (h Y)).hom.app
          ((image R c).obj M) ≫
        (pbcDerivedExtend (b.map Y)).map ((comparison r c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (r.map X)).obj M) := by
  let d : Change R B :=
    { map := fun W ↦ a.map W ≫ s.map W
      square := fun g ↦ by
        rw [← Category.assoc, a.square g, Category.assoc, s.square g,
          Functor.map_comp, Category.assoc] }
  have ha := comparison_composition a s d (fun _ ↦ rfl) c M
  have hr := comparison_composition r b d (fun W ↦ (h W).symm) c M
  let PX := tensorComposition (a.map X) (s.map X) (d.map X) rfl
  let PY := tensorComposition (a.map Y) (s.map Y) (d.map Y) rfl
  let QX := tensorComposition (r.map X) (b.map X) (d.map X) (h X).symm
  let QY := tensorComposition (r.map Y) (b.map Y) (d.map Y) (h Y).symm
  let x := (pbcDerivedExtend (s.map Y)).map ((comparison a c).app M) ≫
    (comparison s c).app ((pbcDerivedExtend (a.map X)).obj M)
  let y := (pbcDerivedExtend (b.map Y)).map ((comparison r c).app M) ≫
    (comparison b c).app ((pbcDerivedExtend (r.map X)).obj M)
  suffices hh : x ≫ (image B c).map (PX.hom.app M ≫ QX.inv.app M) =
      (PY.hom.app ((image R c).obj M) ≫ QY.inv.app ((image R c).obj M)) ≫ y by
    simpa only [x, y, PX, PY, QX, QY, d, tensorSquare, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Category.assoc] using hh
  have ha' : x ≫ (image B c).map (PX.hom.app M) =
      PY.hom.app ((image R c).obj M) ≫ (comparison d c).app M := by
    simpa only [x, PX, PY, Category.assoc] using ha
  have hr' : y ≫ (image B c).map (QX.hom.app M) =
      QY.hom.app ((image R c).obj M) ≫ (comparison d c).app M := by
    simpa only [y, QX, QY, Category.assoc] using hr
  calc
    _ = (x ≫ (image B c).map (PX.hom.app M)) ≫
        (image B c).map (QX.inv.app M) := by simp only [Functor.map_comp, Category.assoc, x]
    _ = (PY.hom.app ((image R c).obj M) ≫ (comparison d c).app M) ≫
        (image B c).map (QX.inv.app M) := by rw [ha']
    _ = (PY.hom.app ((image R c).obj M) ≫ QY.inv.app ((image R c).obj M)) ≫
        (QY.hom.app ((image R c).obj M) ≫ (comparison d c).app M) ≫
        (image B c).map (QX.inv.app M) := by simp only [Category.assoc,
          Iso.inv_hom_id_app_assoc]
    _ = (PY.hom.app ((image R c).obj M) ≫ QY.inv.app ((image R c).obj M)) ≫
        (y ≫ (image B c).map (QX.hom.app M)) ≫
        (image B c).map (QX.inv.app M) := by rw [hr']
    _ = _ := by
      rw [Category.assoc, Category.assoc, ← (image B c).map_comp,
        Iso.hom_inv_id_app]
      erw [(image B c).map_id, Category.comp_id]
      simp only [Category.assoc]

/-- The exact ramified reduction square, including both canonical reduction maps.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def ReductionComparisonEquation (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) : Prop :=
    let a := completedChange l E F i
    let b := finiteChange l E F i e he hepos n hn
    let r := reduction l E n hn
    let s := reduction l F (e * n) (Nat.mul_pos hepos hn)
    let α := fun W ↦ tensorSquare (a.map W) (b.map W) (r.map W) (s.map W)
      (ramified_reduction_square l E F i e he hepos n hn W)
    (pbcDerivedExtend (s.map Y)).map ((comparison a c).app M) ≫
        (comparison s c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
        (image (finite l F (e * n) (Nat.mul_pos hepos hn)) c).map ((α X).hom.app M) =
      (α Y).hom.app ((image (completed l E) c).obj M) ≫
        (pbcDerivedExtend (b.map Y)).map ((comparison r c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (r.map X)).obj M)

/-- Reduction of the integral comparison is precisely the finite comparison, under
canonical compact-support reduction and ordinary tensor balancing. This is an equality
of actual morphisms, stronger than an identification of their isomorphism classes.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: apply comparison_composition to the two paths of the completed/finite coefficient
square. Its paths have equal composite by ramified_reduction_square. The ordinary tensor
associators identify the direct composites and give exactly the displayed equation.
All comparison maps here have the proper-then-open factorization of
comparison_factorization, so this identifies the specified finite coefficient map. -/
theorem comparison_reduction (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    ReductionComparisonEquation l E F i e he hepos n hn c M := by
  exact comparisonSquare (completedChange l E F i)
    (finiteChange l E F i e he hepos n hn) (reduction l E n hn)
    (reduction l F (e * n) (Nat.mul_pos hepos hn))
    (ramified_reduction_square l E F i e he hepos n hn) c M

/-- Source of the specified finite coefficient comparison, at the positive exponent n+1.
Source: blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteTensorSource (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :=
  (pbcDerivedExtend ((finiteChange l E F i e he hepos (n + 1)
    (Nat.le_add_left 1 n)).map Y)).obj
      ((image (finite l E (n + 1) (Nat.le_add_left 1 n)) c).obj
        ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M))

/-- Target of the same finite comparison, before any total inverse limit.
Source: blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteTensorTarget (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :=
  (image (finite l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).obj
    ((pbcDerivedExtend ((finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)).map X)).obj
        ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M))

/-- The finite map itself is the ordered proper mate followed by proper image of the
open coefficient identification. This definition contains both arrows explicitly.
Source: Stacks Tags 07A6, 0B56, 0E8I; blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteTensorMap (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    finiteTensorSource l E F i e he hepos n c M ⟶
      finiteTensorTarget l E F i e he hepos n c M :=
  (properComparison (finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)) c.g).app
      ((openExtension (finite l E (n + 1) (Nat.le_add_left 1 n)) c.i).mapDerivedCategory.obj
        ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M)) ≫
    (proEtaleRingDerivedDirectImage c.g
      ((finite l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring Y)
      ((finite l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring c.Z)
      ((finite l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n))).pull c.g)).map
      ((openComparison (finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)) c.i).app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M))

/-- The canonical finite projection of C_Y P_E: tensor reassociation, compact-support
reduction, and the tensor/restriction unit. It is fixed independently of a tower model.
Source: Bhatt--Scholze Definition 6.7.6; blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteSourceProjection (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj
        ((image (completed l E) c).obj M) ⟶
      (pbcDerivedRestrict (projection l F (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).obj
          (finiteTensorSource l E F i e he hepos n c M) :=
  (pbcDerivedScalarAdjunction (projection l F (e * (n + 1))
      (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).unit.app _ ≫
    (pbcDerivedRestrict (projection l F (e * (n + 1))
      (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).map
      ((tensorSquare (completedCoefficientMap l E F i Y)
        ((finiteChange l E F i e he hepos (n + 1) (Nat.le_add_left 1 n)).map Y)
        (projection l E (n + 1) (Nat.le_add_left 1 n) Y)
        (projection l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)
        (ramified_reduction_square l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n) Y)).hom.app ((image (completed l E) c).obj M) ≫
        (pbcDerivedExtend ((finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map Y)).map
            ((comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M))

/-- The canonical finite projection of P_F C_X, including the same tensor associator
used in the ramified reduction square. It is the adjoint of the fixed reduction map.
Source: Bhatt--Scholze Definition 6.7.6; blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteTargetProjection (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (image (completed l F) c).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) ⟶
      (pbcDerivedRestrict (projection l F (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).obj
          (finiteTensorTarget l E F i e he hepos n c M) :=
  (pbcDerivedScalarAdjunction (projection l F (e * (n + 1))
      (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).unit.app _ ≫
    (pbcDerivedRestrict (projection l F (e * (n + 1))
      (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).map
      ((comparison (reduction l F (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) ≫
        (image (finite l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).map
          ((tensorSquare (completedCoefficientMap l E F i X)
            ((finiteChange l E F i e he hepos (n + 1) (Nat.le_add_left 1 n)).map X)
            (projection l E (n + 1) (Nat.le_add_left 1 n) X)
            (projection l F (e * (n + 1)) (Nat.mul_pos hepos (Nat.le_add_left 1 n)) X)
            (ramified_reduction_square l E F i e he hepos (n + 1)
              (Nat.le_add_left 1 n) X)).hom.app M))

/-- The actual projection from the strict product/cone model, before localization.
Source: Stacks Tag 0941 (blueprint: lem-pur-compact-support-integral-coefficient-comparison).
-/
def strictLevelProjection {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (T : ℕᵒᵖ ⥤ CochainComplex (pbcModules W R) ℤ) (n : ℕ) :
    integralOperationsRoos T ⟶ T.obj (op n) :=
  CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫
    Pi.π (fun k : ℕ ↦ T.obj (op k)) n

/-- The identified constant-coefficient pushforward has exactly the canonical
constant-section structural map. Equality is of the actual module functors.
Source: Stacks Tags 03DA and 03D6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: transpose the constant inverse-image map under the sheaf adjunction. Its
transpose is the constant direct-image map by the triangle identity. Both module
functors are SheafOfModules.pushforward with this same structure map and base-change
functor; congruence gives the displayed equality, on objects and on maps. -/
theorem finiteDirectImage_eq (n : ℕ) {U V : Scheme.{u}} (g : U ⟶ V) :
    proEtaleRingModuleDirectImage g
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring V)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull g) =
      proEtaleConstantModuleDirectImage g (Padic.coefficientExtensionRing l E (n + 1)) := by
  have h : proEtaleRingDirectImageMap g
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring V)
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull g) =
      proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1)) := by
    exact ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  unfold proEtaleRingModuleDirectImage proEtaleConstantModuleDirectImage
  rw [h]

/-- The canonical pullback presentation comparison, preserving its constant-section
adjunction. Source: Stacks Tags 03D3 and 03D6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finitePullbackIso (n : ℕ) {U V : Scheme.{u}} (g : U ⟶ V) :=
  ((proEtaleRingModuleAdjunction g
    ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring V)
    ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
    ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull g)).ofNatIsoRight
      (eqToIso (finiteDirectImage_eq l E n g))).leftAdjointUniq
        (sfIntrinsicConstantModuleAdjunction g (Padic.coefficientExtensionRing l E (n + 1)))

/-- The canonical open presentation comparison, determined by the actual open units.
Source: Stacks Tag 03DI
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteOpenIso (n : ℕ) {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
  ((openAdjunction (finite l E (n + 1) (Nat.le_add_left 1 n)) j).ofNatIsoRight
    (finitePullbackIso l E n j)).leftAdjointUniq
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)

/-- The finite proper/open realization isomorphism, preserving the open unit and
separately derived proper-image unit. Source: Stacks Tags 03DI and 0D6E
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteImageIso (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    image (finite l E (n + 1) (Nat.le_add_left 1 n)) c ≅
      sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c :=
  letI := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).1
  letI := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  letI := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  letI := (proEtaleConstantModuleDirectImage_additive_leftExact c.g
    (Padic.coefficientExtensionRing l E (n + 1))).1
  Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso (finiteOpenIso l E n c.i)) _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorNatIso (eqToIso (finiteDirectImage_eq l E n c.g)))

attribute [local irreducible] finiteImageIso

/-- The two derived quotient tensors are identified by their tensor-unit normalized
adjunctions to exactly the same scalar restriction, including positive-index transport.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteReductionIso (W : Scheme.{u}) (n : ℕ) :
    pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) W) ≅
      scalarReductionDerivedExtension l E W n :=
  (pbcDerivedScalarAdjunction (projection l E (n + 1) (Nat.le_add_left 1 n) W)).leftAdjointUniq
    (derivedScalarExtensionRestrictionAdjunction l E W n).choose

attribute [local irreducible] finiteReductionIso

/-- The actual quotient between arbitrary positive exponents, using the recorded
strict-tower quotient and only reindexing its positive-level convention.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteQuotient (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m)
    (W : Scheme.{u}) : (finite l E m hm).ring W ⟶ (finite l E n hn).ring W :=
  eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
    (Padic.coefficientExtensionRing l E k)) (Nat.sub_add_cancel hm).symm) ≫
  compactSupportLevelSheafQuotient l E W (m - 1) (n - 1) (Nat.sub_le_sub_right h 1) ≫
  eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
    (Padic.coefficientExtensionRing l E k)) (Nat.sub_add_cancel hn))

private theorem finiteQuotient_eq_map (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : n ≤ m) (W : Scheme.{u}) :
    finiteQuotient l E m n hm hn h W =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom
          (show Padic.coefficientExtensionRing l E m →+*
              Padic.coefficientExtensionRing l E n from
            Ideal.Quotient.factor (Ideal.pow_le_pow_right h)).ulift.{u + 1, u + 1}) := by
  cases m with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hm)
  | succ m =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
    | succ n => rfl

/-- Finite quotient maps commute with inverse-image identifications.
Source: Stacks Tag 03CO
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: both composites take each locally constant section represented by an integer
x to its residue at exponent n. These sections locally generate the constant ring
sheaf, and inverse image and sheafification preserve this equality. -/
theorem finiteQuotient_square (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ((finite l E m hm).pull g).hom ≫ finiteQuotient l E m n hm hn h U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (finiteQuotient l E m n hm hn h V) ≫ ((finite l E n hn).pull g).hom := by
  rw [finiteQuotient_eq_map, finiteQuotient_eq_map]
  exact (proEtaleConstantInverseImageMap_naturality g _).symm

/-- The coefficient change for a further quotient, with its canonical section map.
Source: Stacks Tag 06YY
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def finiteQuotientChange (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m) :
    Change (finite l E m hm) (finite l E n hn) where
  map := finiteQuotient l E m n hm hn h
  square := finiteQuotient_square l E m n hm hn h

/-- The retained ramified quotient square commutes for every further quotient,
including the identity quotient m=n.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: evaluate on a representative x in the source integer ring. Along either path
its image is the class of i(x) modulo the eth times nth power. Quotient induction
proves the ring-map equality, and constant sheafification preserves it. -/
theorem ramified_quotient_square (e : ℕ) (he : Ramification l E F i e)
    (hepos : 1 ≤ e) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m)
    (W : Scheme.{u}) :
    (finiteChange l E F i e he hepos m hm).map W ≫
        finiteQuotient l F (e * m) (e * n) (Nat.mul_pos hepos hm)
          (Nat.mul_pos hepos hn) (Nat.mul_le_mul_left e h) W =
      finiteQuotient l E m n hm hn h W ≫
        (finiteChange l E F i e he hepos n hn).map W := by
  rw [finiteQuotient_eq_map, finiteQuotient_eq_map]
  change (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map _ ≫
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map _ =
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map _ ≫
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  apply ULift.ext
  induction x using Quotient.inductionOn' with
  | h x => rfl

/-- The exact coefficient-square equation, with its ordinary tensor associators.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def ComparisonSquareEquation {R S A B : Coefficients.{u}}
    (a : Change R S) (b : Change A B) (r : Change R A) (s : Change S B)
    (h : ∀ W, a.map W ≫ s.map W = r.map W ≫ b.map W)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (pbcModules X (R.ring X))) : Prop :=
  let α := fun W ↦ tensorSquare (a.map W) (b.map W) (r.map W) (s.map W) (h W)
  (pbcDerivedExtend (s.map Y)).map ((comparison a c).app M) ≫
      (comparison s c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
      (image B c).map ((α X).hom.app M) =
    (α Y).hom.app ((image R c).obj M) ≫
      (pbcDerivedExtend (b.map Y)).map ((comparison r c).app M) ≫
      (comparison b c).app ((pbcDerivedExtend (r.map X)).obj M)

/-- Naturality of the actual finite comparisons under every further quotient.
The two vertical arrows here are themselves the canonical compact-support quotient
comparisons, rather than arbitrary identifications of the reduced objects.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: apply comparison_composition to the two paths of ramified_quotient_square.
Their composite coefficient maps agree. Cancel the common ordinary tensor associator
using its inverse. The resulting equality is precisely ComparisonSquareEquation,
including both proper/open quotient comparisons. The argument also covers m=n. -/
theorem comparison_quotients (e : ℕ) (he : Ramification l E F i e)
    (hepos : 1 ≤ e) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (pbcModules X ((finite l E m hm).ring X))) :
    ComparisonSquareEquation
      (finiteChange l E F i e he hepos m hm) (finiteChange l E F i e he hepos n hn)
      (finiteQuotientChange l E m n hm hn h)
      (finiteQuotientChange l F (e * m) (e * n) (Nat.mul_pos hepos hm)
        (Nat.mul_pos hepos hn) (Nat.mul_le_mul_left e h))
      (ramified_quotient_square l E F i e he hepos m n hm hn h) c M := by
  exact comparisonSquare (finiteChange l E F i e he hepos m hm)
    (finiteChange l E F i e he hepos n hn) (finiteQuotientChange l E m n hm hn h)
    (finiteQuotientChange l F (e * m) (e * n) (Nat.mul_pos hepos hm)
      (Nat.mul_pos hepos hn) (Nat.mul_le_mul_left e h))
    (ramified_quotient_square l E F i e he hepos m n hm hn h) c M

/-- The finite maps are invertible on every input, including zero and negative shifts.
Source: Stacks Tags 0GL5, 0GL6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: B_n is finite free over A_n by the ramification ideal equality and the finite
free integer-ring theorem. Use a basis only to test the canonical mates. They become
finite biproduct maps, which commute with additive proper direct image and exact open
extension. Thus both factors and their displayed ordered composite are invertible. -/
theorem finiteComparison_isIso (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (pbcModules X ((finite l E n hn).ring X))) :
    IsIso ((comparison (finiteChange l E F i e he hepos n hn) c).app K) := by
  have hp := finiteProperComparison_isIso
    (finiteChange l E F i e he hepos n hn) c.g
    ((openExtension (finite l E n hn) c.i).mapDerivedCategory.obj K)
  letI : IsIso ((properComparison (finiteChange l E F i e he hepos n hn) c.g).app
      ((openExtension (finite l E n hn) c.i).mapDerivedCategory.obj K)) := by
    simpa [properComparison, finiteProperComparison] using hp
  have ho := openComparison_isIso (finiteChange l E F i e he hepos n hn) c.i K
  letI := ho
  rw [comparison_factorization]
  infer_instance

/-- The coefficient prime is a unit in the geometric base field.
Source: blueprint def-pur-conventions
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: the finite field k0 has characteristic p because its cardinality is p^a,
and its algebraic closure has the same characteristic. A prime l different from p
therefore has nonzero image in the field k, hence is a unit. -/
theorem coefficientPrimeUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  let : Fintype D.k₀ := Fintype.ofFinite _
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : l.Prime) hl.symm)

/-- On the asserted finite-Tor domain the canonical integral coefficient comparison
is invertible, and its actual source and target are constructible complete objects.
The map is ordinary derived tensor, defined above by the normalized scalar adjunction.
The last clause identifies the ambient proper/open realization with the recorded
integral compact-support value, without selecting a new arbitrary limit vertex.
Source: blueprint sk-thm-purity-transport, Step 3; Bhatt--Scholze,
Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).

Proof:
1. The integer ring of F is finite free over that of E: completeness and finiteness
modulo the uniformizer imply finiteness, and torsion-free finite DVR modules are free.
An integral basis simultaneously checks finite freeness at every retained level en.
2. Finite-free-completed-scalar-comparison identifies ordinary tensor with the specified
strict-tower scalar extension, including its completion unit. Constant-completion
equivalence transports the calculation to discrete integral coefficients.
3. At every level the proper comparison is the counit-tensor mate and the open
comparison is the open-unit mate. Finite free tensor is exact; additive proper image
preserves the resulting finite biproducts, proving both finite maps invertible.
4. Construct these mates on the small ringed diagram sites using simultaneous K-flat
replacements and separately derived proper image. Thus their composite is a strict
system map and respects the quotient transitions before taking any limit.
5. The total strict inverse-limit functor, its normalized Roos comparison and the
explicit arithmetic-subsequence block map give the integral comparison. Finite free
tensor commutes with its products and cone. Levelwise cones are zero; exact total
limit therefore makes the comparison invertible.
6. Normalized DVR tower effectivity identifies every projection adjunct with the
specified finite comparison. The finite coefficient-change theorem supplies the
normalization, and its transition cocycle supplies further quotient compatibility.
7. Scalar tensor preserves the uniform Tor interval by balancing against any module
over any target quotient. Integral scalar and compact-support constructibility give
the stated complete constructible source and target.
8. Common compactification refinements commute with the strict mates by their proper
counit and open-unit normalizations; applying total limit proves independence.
9. The completed projection reflector computation identifies the integral proper
projection with the limit of the finite ones, preserving its completion unit.
10. Completed extension by zero and direct-image/limit coherence identify the open
factor and the proper factor. Consequently the scalar comparison intertwines the
actual integral compact-support projection, without inferring equality from reductions.
11. The coefficient composite is strict tensor balancing on both proper and open
factors. Diagram-site mates and total limit preserve its associativity and unit.
12. Derived adjunction shifts make the proper counit comparison commute with shifts;
the degreewise open map has no added sign. This descends through the same strict limit.
13. For F=E the tensor multiplication and completeness units give identity; for three
fields mate pasting gives precisely the displayed coefficient composition law. -/
theorem integralCoefficientComparison
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) ∧
      sfIntegralConstructible l E Y ((image (completed l E) c).obj M) ∧
      sfIntegralConstructible l F Y
        ((image (completed l F) c).obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ∧
      IsIso ((comparison (completedChange l E F i) c).app M) ∧
      Nonempty ((image (completed l E) c).obj M ≅
        (sfIntegralCompactSupportValue l E D.k
          (coefficientPrimeUnit l D hl) c ⟨M, hM.1⟩).obj) := by
  sorry

/-- Completed coefficient multiplication is identity for the identity field inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: every finite projection of the displayed map is the same projection, because
the quotient ring map induced by the identity is identity. Joint monicity proves equality. -/
theorem completedMap_identity (W : Scheme.{u}) :
    completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W = 𝟙 _ := by
  apply (completedCoefficientMap_existsUnique l E E (AlgHom.id ℚ_[l] E) W).unique
    (completedCoefficientMap_existsUnique l E E (AlgHom.id ℚ_[l] E) W).exists.choose_spec
  intro n
  have hq : integralScalarQuotientMap l E E (AlgHom.id ℚ_[l] E) n = RingHom.id _ := by
    ext x
    rfl
  have hs : integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) W n = 𝟙 _ := by
    unfold integralScalarQuotientSheafMap
    rw [hq]
    convert (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) using 1 <;> rfl
  simp only [hs, Category.id_comp, Category.comp_id]

/-- Field towers give the actual composite completed inclusion, not a chosen comparison.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: after each target projection, successive quotient inclusions and direct
inclusion both send the class of x to the class of j(i(x)). The defining residue
normalization and joint monicity of projections prove equality. -/
theorem completedMap_composition (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (j : F →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    completedCoefficientMap l E F i W ≫ completedCoefficientMap l F L j W =
      completedCoefficientMap l E L (j.comp i) W := by
  apply (completedCoefficientMap_existsUnique l E L (j.comp i) W).unique
  · intro n
    have hj : completedCoefficientMap l F L j W ≫
        completedIntegralCommRingProjectionUnrestricted l L W n = _ :=
      (completedCoefficientMap_existsUnique l F L j W).exists.choose_spec n
    have hi : completedCoefficientMap l E F i W ≫
        completedIntegralCommRingProjectionUnrestricted l F W n = _ :=
      (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec n
    rw [Category.assoc,
      hj,
      ← Category.assoc,
      hi,
      Category.assoc]
    congr 1
    have hq : (integralScalarQuotientMap l F L j n).comp
        (integralScalarQuotientMap l E F i n) =
        integralScalarQuotientMap l E L (j.comp i) n := by
      apply RingHom.ext
      intro x
      induction x using Quotient.inductionOn' with
      | h x => rfl
    unfold integralScalarQuotientSheafMap
    rw [← Functor.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact congrArg ULift.up (RingHom.congr_fun hq x.down)
  · exact (completedCoefficientMap_existsUnique l E L (j.comp i) W).exists.choose_spec

/-- The two actual routes around the integral projection/coefficient square.
Their source is C_Y(P_E M tensor N); their target is P_F(C_X M tensor f_F^* C_Y N).
Source: blueprint def-exchange-projection and sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def ProjectionComparisonEquation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (aX : ProEtaleTensorModel X ((completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((completed l E).ring Y))
    (bX : ProEtaleTensorModel X ((completed l F).ring X))
    (bZ : ProEtaleTensorModel c.Z ((completed l F).ring c.Z))
    (bY : ProEtaleTensorModel Y ((completed l F).ring Y))
    (M : DerivedCategory (scalarReductionSource l E X))
    (N : DerivedCategory (scalarReductionSource l E Y)) : Prop :=
    let a := completedChange l E F i
    let CX := pbcDerivedExtend (a.map X)
    let CY := pbcDerivedExtend (a.map Y)
    let PE := image (completed l E) c
    let PF := image (completed l F) c
    let πE := projectionMap (completed l E) c aX aZ aY (completedPull_comp l E c.i c.g)
    let πF := projectionMap (completed l F) c bX bZ bY (completedPull_comp l F c.i c.g)
    CY.map ((πE.app M).app N) ≫
        (comparison a c).app (aX.tensor.obj (M, (pull (completed l E) f).obj N)) ≫
        PF.map ((scalarTensor (a.map X) aX bX).hom.app
          (M, (pull (completed l E) f).obj N) ≫
            bX.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a f).hom.app N))) =
      (scalarTensor (a.map Y) aY bY).hom.app (PE.obj M, N) ≫
        bY.tensor.map (Prod.mkHom ((comparison a c).app M) (𝟙 _)) ≫
          (πF.app (CX.obj M)).app (CY.obj N)

attribute [local irreducible] ordinaryIntegralModulePull ordinaryIntegralModuleAdjunction
  ordinaryIntegralDirectRingMap
  proEtaleRingModulePullback proEtaleRingModuleAdjunction
  HasProEtaleTorAmplitude

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem projectionTensorConstructible (W : Scheme.{u})
    [IsNoetherian W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)]
    (hdim : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (hunit : IsUnit (l : Γ(W, ⊤)))
    (a : ProEtaleTensorModel W ((completed l E).ring W))
    (M N : DerivedCategory (integralTowerModules.{u, u} l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N) :
    sfIntegralConstructible l E W (a.tensor.obj (M, N)) := by
  have hInv (w : W) : IsUnit (l : W.presheaf.stalk w) := by
    simpa only [map_natCast] using hunit.map (W.presheaf.germ ⊤ w trivial).hom
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) :=
    (pbcIntegralUniformComplete_isTriangulated l E W hdim hInv).1
  let M' : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E) :=
    ⟨(integralDetailedTransport W l E).obj M,
      (integralStratifiedPerfectDetailed W l E hdim hunit M).mp hM⟩
  let N' : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E) :=
    ⟨(integralDetailedTransport W l E).obj N,
      (integralStratifiedPerfectDetailed W l E hdim hunit N).mp hN⟩
  have h := transported_tensor_constructible W l E hdim hunit M' N'
  apply (integralStratifiedPerfectDetailed W l E hdim hunit _).mpr
  exact ObjectProperty.prop_of_iso
    (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E))
    ((ProjectionTensorCoefficient.ordinaryComparison l E W a).app (M, N)).symm h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem projectionPullConstructible {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    (hXd : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hYd : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (hXi : IsUnit (l : Γ(X, ⊤))) (hYi : IsUnit (l : Γ(Y, ⊤)))
    (L : DerivedCategory (integralTowerModules l E Y)) (hL : sfIntegralConstructible l E Y L) :
    sfIntegralConstructible l E X
      ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj L) := by
  have hmap : (⟨Functor.whiskerRight (sfCompletedCoefficientMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
        completedIntegralCoefficientSheafUnrestricted l E Y ⟶
          (proEtaleSheafDirectImage f RingCat.{u + 1}).obj
            (completedIntegralCoefficientSheafUnrestricted l E X)) =
      ordinaryIntegralDirectRingMap l E f := by
    apply (ordinaryIntegralDirectRingMap_existsUnique l E f).unique
    · intro n
      exact congrArg ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
        ((sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec n)
    · simpa only [ordinaryIntegralDirectRingMap] using
        (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec
  have hadj : proEtaleRingDirectImageMap f
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedCoefficientMap l E f := by
    exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)
  let e : proEtaleRingModuleDirectImage f
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      ((PurCompactSupport.completed l E).pull f) ≅ ordinaryIntegralModulePush l E f := by
    unfold proEtaleRingModuleDirectImage ordinaryIntegralModulePush
    rw [hadj]
    exact SheafOfModules.pushforwardCongr hmap
  let P : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
    proEtaleRingModulePullback f (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X) ((completed l E).pull f)
  let F : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
    ordinaryIntegralModulePull l E f
  obtain ⟨a⟩ : Nonempty (P ⊣ ordinaryIntegralModulePush l E f) :=
    ⟨(proEtaleRingModuleAdjunction f (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X) ((completed l E).pull f)).ofNatIsoRight e⟩
  let b : P ≅ F := a.leftAdjointUniq (ordinaryIntegralModuleAdjunction l E f)
  have hPAdd : P.Additive := proEtaleRingModulePullback_additive f _ _ _
  have hPLim : PreservesFiniteLimits P :=
    proEtaleRingModulePullback_preservesFiniteLimits f _ _ _
  have hPColim : PreservesFiniteColimits P :=
    proEtaleRingModulePullback_preservesFiniteColimits f _ _ _
  have hFAdd : F.Additive := ordinaryIntegralModulePull_additive l E f
  have hFLim : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso b
  have hFColim : PreservesColimits F :=
    (ordinaryIntegralModuleAdjunction l E f).leftAdjoint_preservesColimits
  let d := Functor.mapDerivedCategoryNatIso b
  let : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh
  let : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E f)
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) := by
    unfold ordinaryIntegralDerivedPull ordinaryIntegralPullCounit
    infer_instance
  obtain ⟨c⟩ : Nonempty (ordinaryIntegralDerivedPull l E f ≅ F.mapDerivedCategory) :=
    ⟨Functor.leftDerivedUnique F.mapDerivedCategory (ordinaryIntegralDerivedPull l E f)
      (ordinaryIntegralPullCounit l E f) F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))⟩
  exact (sfIntegralConstructible l E X).prop_of_iso
    (d.app L ≪≫ (c.app L).symm).symm
    (ordinaryCompletedIntegralPullback l E f hXd hYd hXi hYi L hL).1


section Refinements

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))] [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- The ambient natural transformation is invertible on the full finite-Tor domain.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: each component is invertible by integralCoefficientComparison. A natural
transformation is invertible if all its components are; their inverses are natural. -/
theorem comparisonOnFiniteTor_isIso (c : Compactification f) :
    IsIso (Functor.whiskerLeft (finiteTorConstructibleIntegral l E X).ι
      (comparison (completedChange l E F i) c)) := by
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (fun M ↦ (integralCoefficientComparison l E F i D hl f c M.obj M.property).2.2.2.1)

/-- The requested canonical natural isomorphism with source C_Y P_E and target P_F C_X.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def comparisonIso (c : Compactification f) :
    (finiteTorConstructibleIntegral l E X).ι ⋙ image (completed l E) c ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i Y) ≅
      (finiteTorConstructibleIntegral l E X).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙ image (completed l F) c :=
  @asIso _ _ _ _ (Functor.whiskerLeft (finiteTorConstructibleIntegral l E X).ι
    (comparison (completedChange l E F i) c))
      (comparisonOnFiniteTor_isIso l E F i D hl f c)


/-- Inclusion of the actual uniform finite-Tor domain into the recorded integral category.
Source: blueprint definition 1464
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
-/
def finiteTorIntegralInclusion (W : Scheme.{u}) :
    finiteTorConstructibleIntegralCategory l E W ⥤ sfIntegralConstructibleCategory l E W where
  obj M := ⟨M.obj, M.property.1⟩
  map v := ObjectProperty.homMk v.hom

/-- The fixed compact-support functor on the asserted domain, with the object and map
normalizations of the recorded strict-tower realization, followed by ambient inclusion.
Source: blueprint definitions 1490, 1494
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def recordedSupport (c : Compactification f) :
    finiteTorConstructibleIntegralCategory l E X ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  finiteTorIntegralInclusion l E X ⋙
    sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c E ⋙
      (sfIntegralConstructible l E Y).ι

/-- The normalization against the fixed Roos projections of the recorded functor.
The right side is the actual coefficient-adjunction mate of the proper/open comparison;
no unspecified isomorphism between reduction objects enters this condition.
Source: blueprint definitions 1490, 1494, and proof of sk-thm-purity-transport Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def IsRecordedIdentification (c : Compactification f)
    (τ : (finiteTorConstructibleIntegral l E X).ι ⋙ image (completed l E) c ≅
      recordedSupport l E D hl f c) : Prop :=
  ∀ (M : finiteTorConstructibleIntegralCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E Y n).map (τ.hom.app M) ≫
        (sfCompactSupportFiniteReductionIso l D.k (coefficientPrimeUnit l D hl)
          c E ⟨M.obj, M.property.1⟩ n).hom =
      (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj M.obj) ≫
        (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M.obj ≫
        (finiteImageIso l E n c).hom.app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj M.obj) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((finiteReductionIso l E X n).hom.app M.obj)

/-- The natural identification with the recorded compact-support functor is normalized
by its chosen Roos projections, simultaneously in every input and positive level.
Source: Bhatt--Scholze Definition 6.7.6; blueprint definitions 1490, 1494
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: use the recorded coherent compact-support reduction functor and its total
right-derived inverse limit, including its universal unit. Exact completed open
extension is identified with the limit of its reductions by the completion unit.
Proper direct image commutes with that total limit by its right-adjunction comparison.
The resulting natural isomorphism carries the actual proper/open reduction mates to
the projections in the recorded realization. Conjugate by the recorded natural gamma,
which transports those projections to the chosen Roos vertex defining the value.
The same universal comparisons on strict tower resolutions give uniqueness with
this normalization; no claim that arbitrary integral maps are determined by their
reductions is used. This also proves naturality on roofs, not just on objects. -/
theorem recordedIdentification_existsUnique (c : Compactification f) :
    ∃! τ : (finiteTorConstructibleIntegral l E X).ι ⋙ image (completed l E) c ≅
      recordedSupport l E D hl f c,
      IsRecordedIdentification l E D hl f c τ := by
  sorry

/-- The normalized natural identification; its determining proposition is displayed
in IsRecordedIdentification and refers to the recorded chosen projections.
Source: blueprint definitions 1490, 1494
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def recordedIdentification (c : Compactification f) :
    (finiteTorConstructibleIntegral l E X).ι ⋙ image (completed l E) c ≅
      recordedSupport l E D hl f c :=
  (recordedIdentification_existsUnique l E D hl f c).exists.choose

/-- Scalar extension as a functor on the actual uniform finite-Tor domain.
Source: Bhatt--Scholze Lemma 6.8.2(1)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def scalarFiniteTor (c : Compactification f) :
    finiteTorConstructibleIntegralCategory l E X ⥤
      finiteTorConstructibleIntegralCategory l F X where
  obj M := ⟨(pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj,
    (integralCoefficientComparison l E F i D hl f c M.obj M.property).1⟩
  map v := ObjectProperty.homMk
    ((pbcDerivedExtend (completedCoefficientMap l E F i X)).map v.hom)

/-- The requested canonical natural isomorphism on the recorded compact-support
functors themselves. Both endpoint transports are the normalized natural identifications.
Source: blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def recordedComparisonIso (c : Compactification f) :
    recordedSupport l E D hl f c ⋙ pbcDerivedExtend (completedCoefficientMap l E F i Y) ≅
      scalarFiniteTor l E F i D hl f c ⋙ recordedSupport l F D hl f c :=
  Functor.isoWhiskerRight (recordedIdentification l E D hl f c).symm
      (pbcDerivedExtend (completedCoefficientMap l E F i Y)) ≪≫
    comparisonIso l E F i D hl f c ≪≫
      Functor.isoWhiskerLeft (scalarFiniteTor l E F i D hl f c)
        (recordedIdentification l F D hl f c)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Compact support commutes with the actual finite quotient reduction on this domain.
Source: Bhatt--Scholze, Definition 6.7.6; Stacks Tags 06YY, 0GL6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: write the positive exponent as n+1. The normalized quotient projection
formula makes the proper scalar mate invertible at the completed open extension.
The open scalar comparison is already invertible on every input. The factorization
of the actual compact-support mate is their ordered composite after proper direct
image, so functorial preservation and composition of isomorphisms finish. -/
theorem reductionComparison_isIso (c : Compactification f) (n : ℕ) (hn : 1 ≤ n)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    IsIso ((comparison (reduction l E n hn) c).app M) := by
  cases n with
  | zero => omega
  | succ n =>
    have hp := completedQuotientProperMate l E c.g n
      (reduction l E (n + 1) hn) (fun _ ↦ rfl)
      ((openExtension (completed l E) c.i).mapDerivedCategory.obj M)
    letI : IsIso ((properComparison (reduction l E (n + 1) hn) c.g).app
        ((openExtension (completed l E) c.i).mapDerivedCategory.obj M)) := by
      simpa only [properComparison, finiteProperComparison] using hp
    have := openComparison_isIso (reduction l E (n + 1) hn) c.i M
    rw [comparison_factorization]
    infer_instance

/-- The proper-open comparison is uniquely specified by the open unit and proper counit.
The restriction map in the normalization is the actual pullback-composition/counit map.
Source: blueprint prop-compactification-coherence, proof part (a)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: proper base change after restriction to the open identifies the proper image
of extension by zero with M, using the clopen section over X. Off X all finite
reductions vanish by proper base change. The same assertions for completed coefficients
follow on the normalized strict towers. The open adjunction determines the displayed
map uniquely from its transpose; the normalization is the identity over X. Its cone
has zero reductions everywhere and is complete, so it is zero, proving invertibility. -/
theorem refinementProperOpen_existsUnique {c d : Compactification f} (r : c.Refinement d)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    ∃! e : (openExtension (completed l E) d.i).mapDerivedCategory.obj M ≅
        (push (completed l E) r.hom).obj
          ((openExtension (completed l E) c.i).mapDerivedCategory.obj M),
      (openDerivedAdjunction (completed l E) d.i).homEquiv _ _ e.hom ≫
          refinementRestriction (completed l E) r (completedPull_comp l E c.i r.hom) M =
        (openDerivedAdjunction (completed l E) c.i).unit.app M := by
  sorry

/-- The normalized proper-open comparison; only its uniqueness-determining proof is delayed.
Source: blueprint prop-compactification-coherence, proof part (a)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def refinementProperOpen {c d : Compactification f} (r : c.Refinement d)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :=
  (refinementProperOpen_existsUnique l E D hl f r M hM).exists.choose

/-- The specified compact-support refinement: inverse proper composition followed by
proper pushforward of the inverse proper-open comparison. No arbitrary iso is chosen.
Source: blueprint prop-compactification-coherence, proof part (b)
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
def refinementComparison {c d : Compactification f} (r : c.Refinement d)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    (image (completed l E) c).obj M ≅ (image (completed l E) d).obj M :=
  ((geometricPushComposition (completed l E) r.hom d.g
      (completedPull_comp l E r.hom d.g) ≪≫
    eqToIso (congrArg (fun g : c.Z ⟶ Y ↦ push (completed l E) g) r.hom_g)).symm.app _) ≪≫
      (push (completed l E) d.g).mapIso (refinementProperOpen l E D hl f r M hM).symm

/-- Independence of the compactification uses precisely the normalized refinement maps.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: at every finite level paste the canonical proper counit squares and open unit
squares. Their transposes are the same coefficient pullback map, so the squares commute.
They are strict tower maps before taking limits. The unit-normalized cofinal Roos
comparison identifies their total limits with the displayed integral maps, preserving
both coordinates and the proper-open normalization; it gives the asserted equality. -/
theorem comparison_refinement {c d : Compactification f} (r : c.Refinement d)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    (pbcDerivedExtend (completedCoefficientMap l E F i Y)).map
        (refinementComparison l E D hl f r M hM).hom ≫
        (comparison (completedChange l E F i) d).app M =
      (comparison (completedChange l E F i) c).app M ≫
        (refinementComparison l F D hl f r
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
          (integralCoefficientComparison l E F i D hl f c M hM).1).hom := by
  sorry

/-- The normalized refinements are unital and transitive. Together with common
refinements this makes the preceding equation independent of all refinement choices.
Source: blueprint prop-compactification-coherence
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: transpose the identity and the pasted refinement maps under the open adjunction.
The proper counit triangle identities and associativity of sectionwise pullback pasting
give the same normalized transpose. The uniqueness clause of refinementProperOpen
then gives identity and composition, and the proper compositor transports them to image.
For two common refinements take a further one and equalize the parallel arrows; the
composition identity cancels these additional isomorphisms. -/
theorem refinementComparison_coherence
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    (∀ c : Compactification f,
      refinementComparison l E D hl f (Compactification.Refinement.id c) M hM = Iso.refl _) ∧
    (∀ (c d b : Compactification f) (r : c.Refinement d) (s : d.Refinement b),
      refinementComparison l E D hl f (r.comp s) M hM =
        refinementComparison l E D hl f r M hM ≪≫
          refinementComparison l E D hl f s M hM) := by
  sorry

/-- The already recorded strict identity scalar tower, in the completed F-module category.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
abbrev identityReductionTower (P : CochainComplex (scalarReductionSource l F Y) ℤ) :=
  (integralScalarTowerFunctor l F F (AlgHom.id ℚ_[l] F) Y).obj P

/-- Its strict morphism, before any derived inverse limit is formed.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
abbrev identityReductionMap {P Q : CochainComplex (scalarReductionSource l F Y) ℤ}
    (v : P ⟶ Q) :=
  (integralScalarTowerFunctor l F F (AlgHom.id ℚ_[l] F) Y).map v

/-- The specified comparison is induced by a strict reduction-tower map and its total
Roos map, including both cofinal coordinates and the independently fixed completion units.
The epsilon comparisons identify the retained evaluations with the actual finite
source and target. Their normalization equations fix them by the coefficient-adjunction
units. The last evaluation equation identifies the strict map itself with the ordered
proper/open composite at every level, before its full or cofinal Roos map is applied.
Source: Bhatt--Scholze, Definition 6.7.6; Stacks Tags 08TC, 0941
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: choose simultaneous flat K-flat representatives for the source, target and
comparison, using the equivalence of the resolving subcategory with the derived category.
Apply the actual strict quotient-tensor functor to the chain map. Its naturality is
compatibility with every quotient before localization. The completed source and target
make the independently normalized identity completion units invertible. Their naturality
gives the equality of full Roos maps. Arithmetic cofinality gives the selection/block
maps, which are quasi-isomorphisms by the explicit contracting homotopy between retained
indices. Both coordinates commute with the strict map; composing gives the last equation.
Construct the source and target reductions and the proper/open coefficient mates in
the ringed diagram category, with simultaneous replacements. Evaluation of its proper
part preserves the derived unit. Its open part is the exact tensor identification.
Hence evaluation of this same strict map is exactly finiteTensorMap, not just an
isomorphism between the same endpoints. The two epsilon normalizations are the
adjunctions of those diagram projections. They remain compatible with the actual
quotient transitions. These strict equalities induce the asserted full Roos equality;
they are not inferred from that equality or from faithfulness of reduction. -/
theorem comparison_strict_towers (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) (e : ℕ)
    (heRam : Ramification l E F i e) (he : 1 ≤ e) :
    ∃ (P Q : CochainComplex (scalarReductionSource l F Y) ℤ) (v : P ⟶ Q)
      (a₀ : (pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj
        ((image (completed l E) c).obj M) ≅ DerivedCategory.Q.obj P)
      (a₁ : (image (completed l F) c).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) ≅ DerivedCategory.Q.obj Q),
      proEtaleFlatRepresentatives Y ((completed l F).ring Y) P ∧
      proEtaleFlatRepresentatives Y ((completed l F).ring Y) Q ∧
      (comparison (completedChange l E F i) c).app M ≫ a₁.hom =
        a₀.hom ≫ DerivedCategory.Q.map v ∧
      IsIso (DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y).app P)) ∧
      IsIso (DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y).app Q)) ∧
      (∀ (m n : ℕᵒᵖ) (h : m ⟶ n),
        (identityReductionMap l F v).app m ≫ (identityReductionTower l F Q).map h =
          (identityReductionTower l F P).map h ≫ (identityReductionMap l F v).app n) ∧
      (∃ (ε₀ : ∀ n : ℕ,
          DerivedCategory.Q.obj ((identityReductionTower l F P).obj (op (e * (n + 1) - 1))) ≅
            (pbcDerivedRestrict (projection l F (e * (n + 1))
              (Nat.mul_pos he (Nat.le_add_left 1 n)) Y)).obj
                (finiteTensorSource l E F i e heRam he n c M))
        (ε₁ : ∀ n : ℕ,
          DerivedCategory.Q.obj ((identityReductionTower l F Q).obj (op (e * (n + 1) - 1))) ≅
            (pbcDerivedRestrict (projection l F (e * (n + 1))
              (Nat.mul_pos he (Nat.le_add_left 1 n)) Y)).obj
                (finiteTensorTarget l E F i e heRam he n c M)),
        (∀ n : ℕ,
          a₀.hom ≫ DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y).app P) ≫
              DerivedCategory.Q.map (strictLevelProjection (identityReductionTower l F P)
                (e * (n + 1) - 1)) ≫ (ε₀ n).hom =
            finiteSourceProjection l E F i e heRam he n c M) ∧
        (∀ n : ℕ,
          a₁.hom ≫ DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y).app Q) ≫
              DerivedCategory.Q.map (strictLevelProjection (identityReductionTower l F Q)
                (e * (n + 1) - 1)) ≫ (ε₁ n).hom =
            finiteTargetProjection l E F i e heRam he n c M) ∧
        (∀ n : ℕ,
          DerivedCategory.Q.map
              ((identityReductionMap l F v).app (op (e * (n + 1) - 1))) ≫ (ε₁ n).hom =
            (ε₀ n).hom ≫
              (pbcDerivedRestrict (projection l F (e * (n + 1))
                (Nat.mul_pos he (Nat.le_add_left 1 n)) Y)).map
                  (finiteTensorMap l E F i e heRam he n c M))) ∧
      ∃ (ρ₀ : integralOperationsRoos (identityReductionTower l F P) ⟶
          integralOperationsRoos (retainedTower e (identityReductionTower l F P)))
        (ρ₁ : integralOperationsRoos (identityReductionTower l F Q) ⟶
          integralOperationsRoos (retainedTower e (identityReductionTower l F Q))),
        IsCofinalRoosMap e (identityReductionTower l F P) ρ₀ ∧
        IsCofinalRoosMap e (identityReductionTower l F Q) ρ₁ ∧ QuasiIso ρ₀ ∧ QuasiIso ρ₁ ∧
        (comparison (completedChange l E F i) c).app M ≫ a₁.hom ≫
            DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y).app Q) ≫
            DerivedCategory.Q.map ρ₁ =
          a₀.hom ≫ DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y).app P) ≫
            DerivedCategory.Q.map ρ₀ ≫ DerivedCategory.Q.map
              (integralOperationsRoosMap
                (Functor.whiskerLeft (CategoryTheory.StrictTowerArithmetic.index e)
                  (identityReductionMap l F v))) := by
  sorry

/-- Scalar extension intertwines the actual compact-support projection transformations.
All tensor maps here are the representative-normalized ones, and the proper/open
projection is the existing def-exchange-projection composite, with its counit first.
Source: blueprint sk-thm-purity-transport, Step 3; Stacks Tags 07A6, 0E48
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: the canonical scalar/pullback tensor square commutes on pure tensors. Transpose
the proper projection square under the proper adjunction; unit/counit normalization
reduces both transposes to the same tensor map. The open square similarly reduces to
the open unit. Pasting gives the finite diagram. On completed coefficients the
completion-reflector unit identifies the completed tensor comparisons with these
ordinary ones on the constructible finite-Tor inputs. This is the normalized reflector
argument, rather than faithfulness of reductions. The strict tower maps and their
total limits preserve that unit and the two factors, giving the displayed equality. -/
theorem comparison_projection (c : Compactification f)
    (aX : ProEtaleTensorModel X ((completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((completed l E).ring Y))
    (bX : ProEtaleTensorModel X ((completed l F).ring X))
    (bZ : ProEtaleTensorModel c.Z ((completed l F).ring c.Z))
    (bY : ProEtaleTensorModel Y ((completed l F).ring Y))
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M)
    (N : DerivedCategory (scalarReductionSource l E Y))
    (hN : finiteTorConstructibleIntegral l E Y N) :
    ProjectionComparisonEquation l E F i c aX aZ aY bX bZ bY M N := by
  sorry

/-- The tensors occurring in the integral projection diagram are already complete and
constructible on the asserted domain, so their canonical completion units are invertible.
This identifies the ordinary presentation in comparison_projection with completed tensor.
Source: Bhatt--Scholze, Section 6.5; Stacks Tags 099N, 099G
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).
Proof: use flat perfect local models for the uniform finite-Tor constructible inputs.
Tensoring a complete complex with such a bounded finite-projective model preserves
its completion unit, bounds and constructible reductions. Pullback preserves the
models. Integral compact-support constructibility supplies PE M, with one uniform
bound. Gluing the finite strata proves both displayed complete constructible assertions.
The reflector unit is consequently invertible by the complete-object unit criterion. -/
theorem projectionDomain_complete (c : Compactification f)
    (aX : ProEtaleTensorModel X ((completed l E).ring X))
    (aY : ProEtaleTensorModel Y ((completed l E).ring Y))
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M)
    (N : DerivedCategory (scalarReductionSource l E Y))
    (hN : finiteTorConstructibleIntegral l E Y N) :
    sfIntegralConstructible l E Y (aY.tensor.obj ((image (completed l E) c).obj M, N)) ∧
      sfIntegralConstructible l E X (aX.tensor.obj (M, (pull (completed l E) f).obj N)) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  have primeUnit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
      IsUnit (l : Γ(W, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using (coefficientPrimeUnit l D hl).map ρ.hom
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        ((primeUnit X).map (X.presheaf.germ ⊤ x trivial).hom).map (X.residue x).hom).invertible
  let (y : Y) : Invertible (l : Y.residueField y) :=
    (show IsUnit (l : Y.residueField y) from by
      simpa only [map_natCast] using
        ((primeUnit Y).map (Y.presheaf.germ ⊤ y trivial).hom).map (Y.residue y).hom).invertible
  have hPM := (integralCoefficientComparison l E E (AlgHom.id ℚ_[l] E) D hl f c M hM).2.1
  have hPN := projectionPullConstructible l E f
    (exists_topologicalKrullDim_le (X ↘ Spec (.of D.k)))
    (exists_topologicalKrullDim_le (Y ↘ Spec (.of D.k)))
    (primeUnit X) (primeUnit Y) N hN.1
  exact ⟨projectionTensorConstructible l E Y
      (exists_topologicalKrullDim_le (Y ↘ Spec (.of D.k))) (primeUnit Y) aY _ N hPM hN.1,
    projectionTensorConstructible l E X
      (exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))) (primeUnit X) aX M _ hM.1 hPN⟩

end Refinements

end WeilConjectures.PurCompactSupport
