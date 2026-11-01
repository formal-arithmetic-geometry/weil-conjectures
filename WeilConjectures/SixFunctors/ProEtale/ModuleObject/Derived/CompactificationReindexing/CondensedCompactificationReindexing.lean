/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.AlgebraicGeometry.Open.OpenSectionClopen
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTensorLocalization
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedOpenRestrictedCounit
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange

/-!
# Native condensed compactification reindexing

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, paragraphs 1--3.
(blueprint: lem-fix-condensed-compactification-reindexing).

All operations below are aliases or composites of the native ordinary unbounded
internal-module operations. The clopen adjunction is uniquely normalized by the
inverse open unit; its unit is the projection onto the distinguished component.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Keep native proof elaboration sequential to control peak memory.
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp pullbackSquareComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Native ambient category, with coefficients pulled back from the point.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev D (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj Λ T))

/-- Native ordinary derived pullback, without completion.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev P {A B : Scheme.{u}} (a : A ⟶ B) : D Λ B ⥤ D Λ A :=
  (upperStar Λ a).leftDerivedFunctor

/-- Native ordinary derived direct image.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev R {A B : Scheme.{u}} (a : A ⟶ B) : D Λ A ⥤ D Λ B :=
  (lowerStar Λ a).rightDerivedFunctor

/-- Native exact open extension on the derived category.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev J {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] : D Λ A ⥤ D Λ B :=
  (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- The supplied compactification model, not the derived underived composite.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev F {A B : Scheme.{u}} {f : A ⟶ B} (c : Compactification f) : D Λ A ⥤ D Λ B :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- The native open adjunction, with total derived pullback as right adjoint.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev oa {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] : J Λ j ⊣ P Λ j :=
  derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j

/-- Invertibility of the native open unit.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: exact extension by zero is fully faithful, with restriction its right adjoint.
Its unit is the identity on sections on the open. Localization and the native
exact-to-total-derived identification preserve this unit and its inverse. -/
theorem openUnit_isIso {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] :
    IsIso (oa Λ j).unit := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := inferInstance
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hff := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  exact (oa Λ j).unit_isIso_of_L_fully_faithful

/-- The inverse direction of the open exchange, with its native mate normalization.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def openMate {A B A' B' : Scheme.{u}}
    {j : A ⟶ B} {j' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : CommSq w j' j v) :
    P Λ w ⋙ J Λ j' ⟶ J Λ j ⋙ P Λ v :=
  ((mateEquiv (oa Λ j) (oa Λ j')).symm
    (TwoSquare.mk _ _ _ _ (pullbackSquareComparison Λ sq).inv)).natTrans

/-- Arbitrary-open base change, transported from the literal fibre product.
Source: the source proof, paragraph 1; arbitrary condensed open base change
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: identify the Cartesian square with the literal pullback. The normalized mate
is the termwise localization of `condensedOpenBaseChangeMap`. That map is invertible
on all module sheaves, and exact descent preserves its inverse. Square coherence
identifies the transported mate, including all coefficient identifications. -/
theorem openMate_isIso {A B A' B' : Scheme.{u}}
    {j : A ⟶ B} {j' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback w j' j v) :
    IsIso (openMate Λ sq.toCommSq) := by
  sorry

/-- The open comparison is exactly the inverse of the normalized open mate.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def beta {A B A' B' : Scheme.{u}}
    {j : A ⟶ B} {j' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback w j' j v) :
    J Λ j ⋙ P Λ v ≅ P Λ w ⋙ J Λ j' :=
  @Iso.symm _ _ _ _ (@asIso _ _ _ _ (openMate Λ sq.toCommSq) (openMate_isIso Λ sq))

/-- A compactification square retains its actual open Cartesian square and its
proper-factor square; no invertibility of the latter exchange is part of the data.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
structure Square {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f') (w : X' ⟶ X) (v : Y' ⟶ Y) where
  middle : c'.Z ⟶ c.Z
  openSquare : IsPullback w c'.i c.i middle
  properSquare : CommSq middle c'.g c.g v

/-- The specified proper/open exchange on a supplied diagram, including noninvertible faces.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def squareExchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {c : Compactification f} {c' : Compactification f'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : Square c c' w v) : F Λ c ⋙ P Λ v ⟶ P Λ w ⋙ F Λ c' :=
  CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (J Λ c.i) (J Λ c'.i) (P Λ c.g) (R Λ c.g)
    (derivedUpperStarLowerStarAdjunction Λ c.g)
    (P Λ c'.g) (R Λ c'.g) (derivedUpperStarLowerStarAdjunction Λ c'.g)
    (P Λ v) (P Λ w) (P Λ sq.middle)
    (pullbackSquareComparison Λ sq.properSquare) (beta Λ sq.openSquare)

/-- Proper exchange followed by proper image of the open comparison.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def exchange {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) :
    F Λ c ⋙ P Λ v ⟶ P Λ (pullback.fst f v) ⋙ F Λ (c.baseChange v) :=
  squareExchange Λ
    { middle := pullback.fst c.g v
      openSquare := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
      properSquare := (IsPullback.of_hasPullback c.g v).toCommSq }

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- The section of the pullback of the target open along a proper refinement.
Source: the source proof, paragraph 1, clopen refinement construction
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def refinementSection {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (u : c₁.Refinement c₂) : X ⟶ pullback c₂.i u.hom :=
  pullback.lift (𝟙 X) c₁.i (by simpa using u.i_hom.symm)

/-- The distinguished section is open and closed, even with an extra component.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: its composite with the open pullback immersion is the source open immersion,
so it is open. It is a section of a separated proper map, hence closed. This includes
the empty open and imposes neither density nor a Cartesian refinement square. -/
theorem section_clopen {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :
    IsOpenImmersion (refinementSection u) ∧ IsClosed (Set.range (refinementSection u)) := by
  let p := pullback.fst c₂.i u.hom
  have hs : refinementSection u ≫ p = 𝟙 X := by
    dsimp [refinementSection, p]
    simp
  have hopen : IsOpenImmersion (refinementSection u) := by
    have hcomp : IsOpenImmersion
        (refinementSection u ≫ pullback.snd c₂.i u.hom) := by
      rw [show refinementSection u ≫ pullback.snd c₂.i u.hom = c₁.i by
        dsimp [refinementSection]
        simp]
      infer_instance
    exact IsOpenImmersion.of_comp (refinementSection u) (pullback.snd c₂.i u.hom)
  exact ⟨hopen, (open_section_clopen p (refinementSection u) hs).1.isClosed⟩

private theorem normalizedReverseAdjunction {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {P : D ⥤ C} (a : J ⊣ P) [IsIso a.unit] (b : P ⊣ J) :
    ∃! c : P ⊣ J, c.counit = inv a.unit := by
  have ff := a.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : IsIso b.counit := b.counit_isIso_of_R_fully_faithful
  let t : 𝟭 C ≅ 𝟭 C := asIso a.unit ≪≫ asIso b.counit
  let e : J ≅ J := (Functor.leftUnitor J).symm ≪≫
    Functor.isoWhiskerRight t J ≪≫ Functor.leftUnitor J
  let c := b.ofNatIsoRight e
  have hc : c.counit = inv a.unit := by
    ext N
    change P.map (e.inv.app N) ≫ b.counit.app N = (inv a.unit).app N
    simp only [e, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
      Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
    have hn := b.counit.naturality (t.inv.app N)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn]
    simp [t]
  refine ⟨c, hc, ?_⟩
  intro z hz
  exact Adjunction.ext_counit (hz.trans hc.symm)

/-- The uniquely normalized reverse adjunction on a clopen immersion.
Source: the source proof, paragraph 1, clopen projection
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: decompose sheaves and complexes into the selected clopen and its complement.
Restriction is first projection and extension by zero is zero insertion. These form
an adjunction whose counit is the inverse native open unit. The counit determines the
adjunction uniquely by the adjunction triangles, so the choice below determines real
data up to equality, not an unspecified object. Localization preserves this calculation. -/
theorem clopenAdjunction_existsUnique {A B : Scheme.{u}}
    (s : A ⟶ B) [IsOpenImmersion s] (hs : IsClosed (Set.range s)) :
    ∃! a : P Λ s ⊣ J Λ s,
      a.counit = @inv _ _ _ _ (oa Λ s).unit (openUnit_isIso Λ s) := by
  have := openUnit_isIso Λ s
  let b := (WeilConjectures.CompactSupportCondensedRealization.clopenExtensionRightAdjunction
    Λ s hs).mapDerivedCategoryAdjunction
  let b' : P Λ s ⊣ J Λ s := b.ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ s).symm
  exact normalizedReverseAdjunction (oa Λ s) b'

/-- The right adjunction fixed uniquely by its counit, hence the projector (1,0).
Source: the source proof, paragraph 1, clopen projection
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def clopenAdjunction {A B : Scheme.{u}}
    (s : A ⟶ B) [IsOpenImmersion s] (hs : IsClosed (Set.range s)) :
    P Λ s ⊣ J Λ s :=
  (clopenAdjunction_existsUnique Λ s hs).exists.choose

/-- Transport open extension along an equality using its native adjunction.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def jCongr {A B : Scheme.{u}} {j i : A ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion i] (h : j = i) : J Λ j ≅ J Λ i :=
  (oa Λ j).leftAdjointUniq
    ((oa Λ i).ofNatIsoRight (eqToIso (congrArg (P Λ) h.symm)))

/-- Composition of native open extensions, normalized by pullback composition.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def jComp {A B C : Scheme.{u}} (j : A ⟶ B) (i : B ⟶ C)
    [IsOpenImmersion j] [IsOpenImmersion i] : J Λ j ⋙ J Λ i ≅ J Λ (j ≫ i) :=
  ((conjugateIsoEquiv ((oa Λ j).comp (oa Λ i)) (oa Λ (j ≫ i))).symm
    (leftDerivedUpperStarComp Λ j i).symm).symm

/-- Pull back the target open, apply the specified clopen projector, and compose opens.
Source: the source proof, paragraph 1, displayed refinement construction
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def refinementAdjunct {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :
    J Λ c₂.i ⋙ P Λ u.hom ⟶ J Λ c₁.i :=
  letI := (section_clopen u).1
  let i := pullback.snd c₂.i u.hom
  let t := pullback.fst c₂.i u.hom
  let s := refinementSection u
  let st : s ≫ t = 𝟙 X := pullback.lift_fst _ _ _
  let si : s ≫ i = c₁.i := pullback.lift_snd _ _ _
  let q : P Λ t ⋙ P Λ s ≅ 𝟭 (D Λ X) :=
    (leftDerivedUpperStarComp Λ s t).symm ≪≫
      eqToIso (congrArg (P Λ) st) ≪≫ leftDerivedUpperStarId Λ X
  (beta Λ (IsPullback.of_hasPullback c₂.i u.hom)).hom ≫
    Functor.whiskerLeft (P Λ t)
      (Functor.whiskerRight (clopenAdjunction Λ s (section_clopen u).2).unit (J Λ i)) ≫
    (Functor.isoWhiskerRight q (J Λ s ⋙ J Λ i)).hom ≫
    (Functor.leftUnitor _).hom ≫ (jComp Λ s i).hom ≫
    (jCongr Λ si).hom

/-- Adjunction transpose of the clopen construction, then the direct compositor.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) : F Λ c₂ ⟶ F Λ c₁ :=
  let m : J Λ c₂.i ⟶ J Λ c₁.i ⋙ R Λ u.hom :=
    ((derivedUpperStarLowerStarAdjunction Λ u.hom).whiskerRight _).homEquiv _ _
      (refinementAdjunct Λ u)
  Functor.whiskerRight m (R Λ c₂.g) ≫
    Functor.whiskerLeft (J Λ c₁.i) ((rightDerivedLowerStarComp Λ u.hom c₂.g).hom ≫
      (eqToIso (congrArg (R Λ) u.hom_g)).hom)

set_option maxHeartbeats 1600000 in
-- Native derived endpoints require additional unification time.
/-- Direct exchanges in an isomorphism cube, with arbitrary face base maps.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: paste the front face with the two adjacent isomorphism faces in either order.
Pullback square coherence identifies the two pasted comparisons. Taking mates and
using both pasting laws gives the equation. Only vertex comparisons are inverted;
no face exchange is inverted. -/
theorem direct_cube {X Y X' Y' A B A' B' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    {g : A ⟶ B} {g' : A' ⟶ B'} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : CommSq w f' f v) (back : CommSq w₀ g' g v₀)
    (left : CommSq a g f b) (right : CommSq a' g' f' b')
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b) (K : D Λ X) :
    (P Λ b').map ((baseChangeMap Λ front).app K) ≫
        (baseChangeMap Λ right).app ((P Λ w).obj K) ≫
        (R Λ g').map ((pullbackSquareComparison Λ top).inv.app K) =
      (pullbackSquareComparison Λ bottom).inv.app ((R Λ f).obj K) ≫
        (P Λ v₀).map ((baseChangeMap Λ left).app K) ≫
        (baseChangeMap Λ back).app ((P Λ a).obj K) := by
  sorry

set_option maxHeartbeats 1600000 in
-- The endpoints of the native derived adjunctions require additional unification time.
/-- A common-refinement comparison, using only inverses of refinement components.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def comparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (h₁ : d.Refinement c₁) (h₂ : d.Refinement c₂)
    (K : D Λ X) [h₁iso : IsIso ((refinement Λ h₁).app K)]
    [h₂iso : IsIso ((refinement Λ h₂).app K)] : (F Λ c₁).obj K ≅ (F Λ c₂).obj K :=
  @asIso _ _ _ _ ((refinement Λ h₁).app K) h₁iso ≪≫
    (@asIso _ _ _ _ ((refinement Λ h₂).app K) h₂iso).symm

set_option maxHeartbeats 1600000 in
-- Functor-category comparisons retain the native derived endpoints.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Compute only the tensorator field of the native monoidal structure.
set_option maxHeartbeats 1600000 in
-- Match the two adjoint transposes after identifying their tensorator fields.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- Native pullback comparison for an isomorphism followed by its inverse.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def pInverse {A B : Scheme.{u}} (a : A ⟶ B) [IsIso a] :
    P Λ a ⋙ P Λ (inv a) ≅ 𝟭 (D Λ B) :=
  (leftDerivedUpperStarComp Λ (inv a) a).symm ≪≫
    eqToIso (congrArg (P Λ) (IsIso.inv_hom_id a)) ≪≫ leftDerivedUpperStarId Λ B

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- The actual inverse-diagram compact exchange, without choosing another inverse.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply compact pasting to the square and its inverse. The middle ambient
isomorphisms cancel, and compact identity gives the displayed equation. Swapping
the diagrams proves the reverse inverse equation. Only vertex exchanges are inverted. -/
theorem compact_inverse {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} [IsIso w] [IsIso v]
    (s : Square c c' w v) [IsIso s.middle]
    (s' : Square c' c (inv w) (inv v)) (h : s'.middle = inv s.middle) (K : D Λ X) :
    (P Λ (inv v)).map ((squareExchange Λ s).app K) ≫
        (squareExchange Λ s').app ((P Λ w).obj K) ≫
        (F Λ c).map ((pInverse Λ w).hom.app K) =
      (pInverse Λ v).hom.app ((F Λ c).obj K) := by
  sorry

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
end AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
