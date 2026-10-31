/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SecSmoothPurity.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.AlgebraicGeometry.OpenSectionClopen
import WeilConjectures.AlgebraicGeometry.InternalSectionTensorLocalization
import all WeilConjectures.AlgebraicGeometry.CondensedOpenRestrictedCounit
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

/-- The canonical projection map of a compactification, already defined natively.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def pf {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : D Λ X) (L : D Λ Y) :
    (F Λ c).obj K ⊗ L ⟶ (F Λ c).obj (K ⊗ (P Λ f).obj L) :=
  exceptionalProjectionMorphismOfCompactification Λ c K L

/-- The two monoidal input comparisons used in the compact-support projection square.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def tensorInput {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (v : Y' ⟶ Y)
    (K : D Λ X) (L : D Λ Y) :
    (P Λ (pullback.fst f v)).obj (K ⊗ (P Λ f).obj L) ⟶
      (P Λ (pullback.fst f v)).obj K ⊗
        (P Λ (pullback.snd f v)).obj ((P Λ v).obj L) :=
  ((leftDerivedUpperStarTensor Λ (pullback.fst f v)).app K).app ((P Λ f).obj L) ≫
    (𝟙 _ ⊗ₘ (pullbackSquareComparison Λ
      (IsPullback.of_hasPullback f v).toCommSq).inv.app L)

private theorem directExchange_isIso {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    [IsIso w] [IsIso v] (sq : CommSq w f' f v) :
    IsIso (baseChangeMap Λ sq) := by
  have : (P Λ w).IsEquivalence := inferInstance
  have : (P Λ v).IsEquivalence := inferInstance
  exact Adjunction.isIso_exchangeRight_of_isEquivalence
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq)

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- Isomorphism squares have invertible native exchanges on all ambient inputs.
Together with the identity and pasting equations this identifies the exchange of
the inverse diagram with the inverse exchange, not merely some inverse map.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: paste the diagram with its scheme-theoretic inverse in both orders. The
identity and pasting equations show that its specified inverse exchange is both a
left and a right inverse, after the native identity/composition identifications. -/
theorem square_isIso {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} [IsIso w] [IsIso v]
    (s : Square c c' w v) [IsIso s.middle]
    (sq : CommSq w f' f v) :
    IsIso (baseChangeMap Λ sq) ∧ IsIso (squareExchange Λ s) := by
  refine ⟨directExchange_isIso Λ sq, ?_⟩
  have : (P Λ v).IsEquivalence := inferInstance
  have : (P Λ s.middle).IsEquivalence := inferInstance
  have := isIso_mateEquiv_of_isEquivalence
    (derivedUpperStarLowerStarAdjunction Λ c.g)
    (derivedUpperStarLowerStarAdjunction Λ c'.g)
    (TwoSquare.mk (P Λ v) (P Λ c.g) (P Λ c'.g) (P Λ s.middle)
      (pullbackSquareComparison Λ s.properSquare).hom)
  unfold squareExchange
    CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
  infer_instance

/-- Scheme isomorphisms make the specified direct and compact exchanges invertible.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: base change of a scheme isomorphism is an isomorphism. Paste the square with
its inverse; native pullback coherence and mate pasting identify their exchanges
with identity. The proper/open composite is then a composite of isomorphisms. -/
theorem exchange_isIso {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) [IsIso v] :
    IsIso (baseChangeMap Λ (IsPullback.of_hasPullback f v).toCommSq) ∧
      IsIso (exchange Λ c v) := by
  refine ⟨directExchange_isIso Λ _, ?_⟩
  unfold exchange
  exact (square_isIso Λ (c := c) (c' := c.baseChange v)
    { middle := pullback.fst c.g v
      openSquare := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
      properSquare := (IsPullback.of_hasPullback c.g v).toCommSq }
    (IsPullback.of_hasPullback f v).toCommSq).2

/-- Projection transport uses the native tensorator on both inputs.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: for the proper factor use naturality of the counit-defined projection mate
under base change. For the open factor restrict to the open: the open mate and
projection map restrict to identity, and native monoidal square coherence identifies
the remaining tensorators. Open-adjunction injectivity gives equality before proper
pushforward. Compose these equations. Only the open projection is inverted. -/
theorem exchange_projection {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) [IsIso v]
    (K : D Λ X) (L : D Λ Y) :
    (P Λ v).map (pf Λ c K L) ≫
        (exchange Λ c v).app (K ⊗ (P Λ f).obj L) ≫
        (F Λ (c.baseChange v)).map (tensorInput Λ v K L) =
      ((leftDerivedUpperStarTensor Λ v).app ((F Λ c).obj K)).app L ≫
        ((exchange Λ c v).app K ⊗ₘ 𝟙 _) ≫
        pf Λ (c.baseChange v) ((P Λ (pullback.fst f v)).obj K) ((P Λ v).obj L) := by
  sorry

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

/-- Refinement projection compatibility on arbitrary unbounded inputs.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the clopen projector commutes with tensor: on the selected component it is
identity and on the complement it is zero. Arbitrary-open base change and native
monoidal coherence transport this equality to the displayed refinement adjunct.
Take its mate, apply the proper direct image, and use projection composition with
the inverse-conjugate direct compositor. This gives exactly the displayed equation. -/
theorem refinement_projection {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : D Λ X) (L : D Λ Y) :
    pf Λ c₂ K L ≫ (refinement Λ u).app (K ⊗ (P Λ f).obj L) =
      ((refinement Λ u).app K ⊗ₘ 𝟙 L) ≫ pf Λ c₁ K L := by
  sorry

set_option maxHeartbeats 1600000 in
-- Native derived endpoints require additional unification time.
/-- The clopen unit really is identity on the chosen component and zero off it.
Source: the source proof, paragraph 1, specified projector
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: in the clopen product decomposition, the fixed counit is identity and the
adjunction triangles force the first coordinate of its unit to be identity. The
other target coordinate is zero, hence the other coordinate map is zero. Exact
restriction and localization preserve both equations. -/
theorem clopenProjector_coordinates {A B C : Scheme.{u}}
    (s : A ⟶ B) [IsOpenImmersion s] (hs : IsClosed (Set.range s))
    (z : C ⟶ B) [IsOpenImmersion z] (hz : Set.range z = (Set.range s)ᶜ)
    (H : D Λ B) :
    (P Λ s).map ((clopenAdjunction Λ s hs).unit.app H) ≫
        (@asIso _ _ _ _ (oa Λ s).unit (openUnit_isIso Λ s)).inv.app ((P Λ s).obj H) = 𝟙 _ ∧
      (P Λ z).map ((clopenAdjunction Λ s hs).unit.app H) = 0 := by
  have he : (clopenAdjunction Λ s hs).counit =
      (@asIso _ _ _ _ (oa Λ s).unit (openUnit_isIso Λ s)).inv := by
    unfold clopenAdjunction
    exact (clopenAdjunction_existsUnique Λ s hs).exists.choose_spec
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact (clopenAdjunction Λ s hs).left_triangle_components H
  · have hd : Disjoint (Set.range s.base) (Set.range z.base) := by
      rw [hz]
      exact disjoint_compl_right
    exact (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ s z hd ((P Λ s).obj H)).eq_of_tgt _ _

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

/-- The same cube equation for inverse open mates; on Cartesian faces this is
precisely transport of beta after inversion of the open comparisons.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply the two open-adjunction mate bijections to the pullback cube identity.
Their injectivity and naturality give the displayed equation. Cartesian face mates
are invertible by arbitrary-open base change, so inversion gives transport of beta. -/
theorem open_cube {X Y X' Y' A B A' B' : Scheme.{u}}
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    {i : A ⟶ B} {i' : A' ⟶ B'} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion i] [IsOpenImmersion i']
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : CommSq w j' j v) (back : CommSq w₀ i' i v₀)
    (left : CommSq a i j b) (right : CommSq a' i' j' b')
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b) (K : D Λ X) :
    (J Λ i').map ((pullbackSquareComparison Λ top).hom.app K) ≫
        (openMate Λ right).app ((P Λ w).obj K) ≫
        (P Λ b').map ((openMate Λ front).app K) =
      (openMate Λ back).app ((P Λ a).obj K) ≫
        (P Λ v₀).map ((openMate Λ left).app K) ≫
        (pullbackSquareComparison Λ bottom).hom.app ((J Λ j).obj K) := by
  sorry

/-- Compact-support exchanges in an isomorphism cube, even for a non-isomorphic face base.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: expand each compact exchange into its direct and open factors. Apply the
direct cube identity to the proper factors and the inverse open cube identity to
the open factors. Naturality moves the intermediate comparisons through proper
pushforward. The middle comparisons cancel, leaving exactly the two displayed routes. -/
theorem compact_cube {X Y X' Y' A B A' B' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : A ⟶ B} {g' : A' ⟶ B'}
    {c : Compactification f} {c' : Compactification f'}
    {d : Compactification g} {d' : Compactification g'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : Square c c' w v) (back : Square d d' w₀ v₀)
    (left : Square c d a b) (right : Square c' d' a' b')
    [IsIso left.middle] [IsIso right.middle]
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b)
    (middle : CommSq right.middle back.middle front.middle left.middle)
    (K : D Λ X) :
    (P Λ b').map ((squareExchange Λ front).app K) ≫
        (squareExchange Λ right).app ((P Λ w).obj K) ≫
        (F Λ d').map ((pullbackSquareComparison Λ top).inv.app K) =
      (pullbackSquareComparison Λ bottom).inv.app ((F Λ c).obj K) ≫
        (P Λ v₀).map ((squareExchange Λ left).app K) ≫
        (squareExchange Λ back).app ((P Λ a).obj K) := by
  sorry

set_option maxHeartbeats 1600000 in
-- The endpoints of the native derived adjunctions require additional unification time.
/-- Direct exchange under vertical pasting, including identity and inverse squares.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the normalized comparison for the outer square is the paste of the two
pullback comparisons. The vertical mate-pasting law gives this equation, with the
native pullback compositors on the two boundaries. With identity edges these are
the native unit comparisons; pasting an isomorphism and its inverse therefore gives
mutually inverse exchanges. -/
theorem direct_paste {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : CommSq w f' f v) (t : CommSq w' f'' f' v')
    (outer : CommSq (w' ≫ w) f'' f (v' ≫ v)) (K : D Λ X) :
    (leftDerivedUpperStarComp Λ v' v).hom.app ((R Λ f).obj K) ≫
        (P Λ v').map ((baseChangeMap Λ s).app K) ≫
        (baseChangeMap Λ t).app ((P Λ w).obj K) =
      (baseChangeMap Λ outer).app K ≫
        (R Λ f'').map ((leftDerivedUpperStarComp Λ w' w).hom.app K) := by
  sorry

private theorem exchange_identity_aux {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (G : C ⥤ C) (H : D ⥤ D) (e : G ≅ 𝟭 C) (d : H ≅ 𝟭 D)
    (θ : G ⋙ L ≅ L ⋙ H)
    (h : ∀ N, θ.hom.app N ≫ d.hom.app (L.obj N) = L.map (e.hom.app N)) (K : D) :
    (a.exchangeRight a θ).app K ≫ R.map (d.hom.app K) = e.hom.app (R.obj K) := by
  rw [Adjunction.exchangeRight_app, Category.assoc, Category.assoc, ← R.map_comp]
  rw [show H.map (a.counit.app K) ≫ d.hom.app K =
      d.hom.app (L.obj (R.obj K)) ≫ a.counit.app K from d.hom.naturality _]
  rw [← R.map_comp, ← Category.assoc, h, R.map_comp, ← Category.assoc]
  have hu := a.unit.naturality (e.hom.app (R.obj K))
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← hu]
  simp only [Functor.id_obj, Category.assoc, a.right_triangle_components,
    Category.comp_id]

/-- Direct exchange on an identity square, with its actual identity comparisons.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply the mate identity law to the native square unit identity. The normalized
identity adjunction compares the remaining identity pullbacks with identity functors. -/
theorem direct_identity {X Y : Scheme.{u}} (f : X ⟶ Y) (K : D Λ X) :
    (baseChangeMap Λ (CommSq.mk
      ((Category.id_comp f).trans (Category.comp_id f).symm))).app K ≫
        (R Λ f).map ((leftDerivedUpperStarId Λ X).hom.app K) =
      (leftDerivedUpperStarId Λ Y).hom.app ((R Λ f).obj K) := by
  exact exchange_identity_aux (derivedUpperStarLowerStarAdjunction Λ f)
    (P Λ (𝟙 Y)) (P Λ (𝟙 X)) (leftDerivedUpperStarId Λ Y)
    (leftDerivedUpperStarId Λ X)
    (pullbackSquareComparison Λ (CommSq.mk
      ((Category.id_comp f).trans (Category.comp_id f).symm)))
    (pullbackSquareComparison_identity Λ f) K

/-- Pasting in the direct-image direction uses the canonical inverse-conjugate compositor.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: horizontal pullback pasting gives the common left-adjoint comparison. Its
mates under the composite adjunction are equal. The right-adjoint comparison in this
direction is the native `rightDerivedLowerStarComp`, the conjugate of the left
compositor, and not the conjugate of its inverse. -/
theorem direct_composition {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {d : Z' ⟶ Z}
    (s : CommSq a f' f b) (t : CommSq b g' g d)
    (outer : CommSq a (f' ≫ g') (f ≫ g) d) (K : D Λ X) :
    (P Λ d).map ((rightDerivedLowerStarComp Λ f g).inv.app K) ≫
        (baseChangeMap Λ t).app ((R Λ f).obj K) ≫
        (R Λ g').map ((baseChangeMap Λ s).app K) ≫
        (rightDerivedLowerStarComp Λ f' g').hom.app ((P Λ a).obj K) =
      (baseChangeMap Λ outer).app K := by
  sorry

/-- The literal pullback of the ambient map of a refinement.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def refinementBaseMap {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (v : Y' ⟶ Y) :
    (c₁.baseChange v).Z ⟶ (c₂.baseChange v).Z :=
  pullback.lift (pullback.fst c₁.g v ≫ u.hom) (pullback.snd c₁.g v)
    (by rw [Category.assoc, u.hom_g, pullback.condition])

/-- The pulled-back ambient map obeys both refinement triangles.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: compose each triangle with the two pullback projections. The first projection
uses the original refinement triangle and the second is the identity over the base.
The universal property of the pullback gives the required equality. -/
theorem refinementBaseMap_triangles {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (v : Y' ⟶ Y) :
    (c₁.baseChange v).i ≫ refinementBaseMap u v = (c₂.baseChange v).i ∧
      refinementBaseMap u v ≫ (c₂.baseChange v).g = (c₁.baseChange v).g := by
  constructor
  · apply pullback.hom_ext
    · simp [refinementBaseMap, Category.assoc, u.i_hom]
    · simp [refinementBaseMap, Category.assoc]
  · simp [refinementBaseMap]

/-- Base change of a proper refinement, without a boundary-preservation condition.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def refinementBaseChange {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (v : Y' ⟶ Y) :
    (c₁.baseChange v).Refinement (c₂.baseChange v) where
  hom := refinementBaseMap u v
  i_hom := (refinementBaseMap_triangles u v).1
  hom_g := (refinementBaseMap_triangles u v).2

/-- Identity and composition of refinements on the entire ambient category.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: under the open adjunction the defining map restricts to identity. For an
identity refinement its clopen projector is identity. For two successive refinements,
pasting and the adjunction triangles identify the composite transpose with the same
normalized map for their composite. Uniqueness under the open Hom bijection gives
both equations, and direct-image associativity gives the final support equations. -/
theorem refinement_id_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {c₀ c₁ c₂ : Compactification f}
    (z : c₀.Refinement c₁) (u : c₁.Refinement c₂) :
    refinement Λ (Compactification.Refinement.id c) = 𝟙 (F Λ c) ∧
      refinement Λ (z.comp u) = refinement Λ u ≫ refinement Λ z := by
  sorry

/-- A common-refinement comparison, using only inverses of refinement components.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def comparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (h₁ : d.Refinement c₁) (h₂ : d.Refinement c₂)
    (K : D Λ X) [h₁iso : IsIso ((refinement Λ h₁).app K)]
    [h₂iso : IsIso ((refinement Λ h₂).app K)] : (F Λ c₁).obj K ≅ (F Λ c₂).obj K :=
  @asIso _ _ _ _ ((refinement Λ h₁).app K) h₁iso ≪≫
    (@asIso _ _ _ _ ((refinement Λ h₂).app K) h₂iso).symm

/-- All rational bounded-constructible refinement components are invertible.
No positive-characteristic or absolute-separatedness hypothesis is present.
Source: the source proof, paragraph 1; the node's rational boundary argument
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: over the target open the adjoint refinement is identity by clopen counit
cancellation. On its closed complement both sides vanish: proper base change for
the rational coefficients identifies the target restriction with direct image of a
restriction disjoint from the source open. Open and closed restriction detect
isomorphisms. Proper direct image and its compositor preserve this isomorphism.
The finite-subextension-valued algebraic-closure case follows by finite coefficient
field descent; the finite-extension case is the rational proper base-change theorem. -/
theorem rational_refinement_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂)
    (K : D Λ X) (hK : boundedConstructible (condensedRingObj Λ X) K) :
    IsIso ((refinement Λ u).app K) := by
  sorry

set_option maxHeartbeats 1600000 in
-- Functor-category comparisons retain the native derived endpoints.
/-- Independence, identity and cocycle of common-refinement comparisons, including
naturality in the original bounded constructible full subcategory.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the category of compactifications has common refinements and equalizers of
parallel refinement maps. Apply the ambient composition law and cancel invertible
rational refinement components on bounded constructible inputs. This proves
independence of the common refinement. Identity, cocycle and naturality follow by
doing all comparisons over one further common refinement. This uses no density
condition on any supplied compactification or refinement. -/
theorem condensed_compactification_reindexing (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ τ : ∀ c₁ c₂ : Compactification f,
        (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₁ ≅
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₂,
      (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
          (h₂ : d.Refinement c₂) (K : BoundedConstructible (condensedRingObj Λ X)),
        (τ c₁ c₂).hom.app K ≫ (refinement Λ h₂).app K.obj =
          (refinement Λ h₁).app K.obj) ∧
      (∀ c : Compactification f, τ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, τ c₁ c₂ ≪≫ τ c₂ c₃ = τ c₁ c₃) ∧
      (∀ σ : ∀ c₁ c₂ : Compactification f,
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₁ ≅
            (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₂,
        (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
            (h₂ : d.Refinement c₂) (K : BoundedConstructible (condensedRingObj Λ X)),
          (σ c₁ c₂).hom.app K ≫ (refinement Λ h₂).app K.obj =
            (refinement Λ h₁).app K.obj) → σ = τ) := by
  sorry

/-- Pasting of compact-support exchanges uses the same boundary compositors.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: expand into the proper and open factors. Apply direct mate pasting and open
mate pasting to the two factors. Native associativity cancels their middle
comparisons. This yields the displayed equation for the outer square. -/
theorem compact_paste {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {c : Compactification f} {c' : Compactification f'} {c'' : Compactification f''}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : Square c c' w v) (t : Square c' c'' w' v')
    (outer : Square c c'' (w' ≫ w) (v' ≫ v))
    (h : outer.middle = t.middle ≫ s.middle) (K : D Λ X) :
    (leftDerivedUpperStarComp Λ v' v).hom.app ((F Λ c).obj K) ≫
        (P Λ v').map ((squareExchange Λ s).app K) ≫
        (squareExchange Λ t).app ((P Λ w).obj K) =
      (squareExchange Λ outer).app K ≫
        (F Λ c'').map ((leftDerivedUpperStarComp Λ w' w).hom.app K) := by
  sorry

/-- Identity compactification square, with the native unit comparisons.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: direct identity mates give identity, and open identity mates give identity
under the normalized open unit. Their product is identity under the same pullback
unit comparisons. -/
theorem compact_identity {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (s : Square c c (𝟙 X) (𝟙 Y))
    (h : s.middle = 𝟙 c.Z) (K : D Λ X) :
    (squareExchange Λ s).app K ≫
        (F Λ c).map ((leftDerivedUpperStarId Λ X).hom.app K) =
      (leftDerivedUpperStarId Λ Y).hom.app ((F Λ c).obj K) := by
  sorry


/-- Projection descends through the actual common-refinement comparison.
The four invertibilities here specify exactly the displayed comparison domain;
the rational bounded-constructible theorem supplies them on the node's domain.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply refinement projection compatibility for the two arrows to the common
refinement. Cancel the second refinement at the tensor input and the first at the
original input. The remaining inverses are exactly those in `comparison`. -/
theorem comparison_projection {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (h₁ : d.Refinement c₁) (h₂ : d.Refinement c₂)
    (K : D Λ X) (L : D Λ Y)
    [a₁ : IsIso ((refinement Λ h₁).app K)] [a₂ : IsIso ((refinement Λ h₂).app K)]
    [b₁ : IsIso ((refinement Λ h₁).app (K ⊗ (P Λ f).obj L))]
    [b₂ : IsIso ((refinement Λ h₂).app (K ⊗ (P Λ f).obj L))] :
    pf Λ c₁ K L ≫ (comparison Λ h₁ h₂ (K ⊗ (P Λ f).obj L) (h₁iso := b₁) (h₂iso := b₂)).hom =
      ((comparison Λ h₁ h₂ K (h₁iso := a₁) (h₂iso := a₂)).hom ⊗ₘ 𝟙 L) ≫ pf Λ c₂ K L := by
  apply (cancel_mono ((refinement Λ h₂).app (K ⊗ (P Λ f).obj L))).1
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [refinement_projection Λ h₂ K L, tensorHom_comp_tensorHom_assoc]
  simp only [IsIso.inv_hom_id, Category.assoc, Category.comp_id]
  exact refinement_projection Λ h₁ K L

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- Exchange descends through common refinements when the displayed refinement
components are invertible; neither face exchange is inverted.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the clopen projector is stable under pullback. Taking mates and pasting
therefore makes the two refinement/exchange squares commute, also for a
non-isomorphic base map. Apply them to the two common-refinement arrows and cancel
the invertible refinement components. All inverses in the result belong to
`comparison`; neither a base-change nor a projection map has been inverted. -/
theorem comparison_exchange {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (h₁ : d.Refinement c₁) (h₂ : d.Refinement c₂)
    (v : Y' ⟶ Y) (K : D Λ X)
    [a₁ : IsIso ((refinement Λ h₁).app K)] [a₂ : IsIso ((refinement Λ h₂).app K)]
    [b₁ : IsIso ((refinement Λ (refinementBaseChange h₁ v)).app
      ((P Λ (pullback.fst f v)).obj K))]
    [b₂ : IsIso ((refinement Λ (refinementBaseChange h₂ v)).app
      ((P Λ (pullback.fst f v)).obj K))] :
    (P Λ v).map (comparison Λ h₁ h₂ K (h₁iso := a₁) (h₂iso := a₂)).hom ≫ (exchange Λ c₂ v).app K =
      (exchange Λ c₁ v).app K ≫
        (comparison Λ (refinementBaseChange h₁ v) (refinementBaseChange h₂ v)
          ((P Λ (pullback.fst f v)).obj K) (h₁iso := b₁) (h₂iso := b₂)).hom := by
  sorry

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- The open inverse mate respects vertical pasting, with native boundary compositors.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply open-adjunction mate pasting to native pullback square pasting. The two
boundary comparisons are precisely the pullback compositors displayed here. This
also determines pasting for beta by inversion on Cartesian squares. -/
theorem open_paste {X Y X' Y' X'' Y'' : Scheme.{u}}
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {j'' : X'' ⟶ Y''}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : CommSq w j' j v) (t : CommSq w' j'' j' v')
    (outer : CommSq (w' ≫ w) j'' j (v' ≫ v)) (K : D Λ X) :
    (openMate Λ t).app ((P Λ w).obj K) ≫ (P Λ v').map ((openMate Λ s).app K) =
      (J Λ j'').map ((leftDerivedUpperStarComp Λ w' w).inv.app K) ≫
        (openMate Λ outer).app K ≫
        (leftDerivedUpperStarComp Λ v' v).hom.app ((J Λ j).obj K) := by
  sorry

private theorem open_identity_aux {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (G : C ⥤ C) (H : D ⥤ D) (e : G ≅ 𝟭 C) (d : H ≅ 𝟭 D)
    (θ : R ⋙ G ≅ H ⋙ R)
    (h : ∀ N, θ.hom.app N ≫ R.map (d.hom.app N) = e.hom.app (R.obj N)) (K : C) :
    (((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans).app K ≫ d.hom.app (L.obj K) =
      L.map (e.hom.app K) := by
  let α := ((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans
  have hu : G.map (a.unit.app K) ≫ θ.hom.app (L.obj K) =
      a.unit.app (G.obj K) ≫ R.map (α.app K) :=
    unit_mateEquiv_symm a a (TwoSquare.mk _ _ _ _ θ.hom) K
  change α.app K ≫ d.hom.app (L.obj K) = _
  apply (a.homEquiv (G.obj K) (L.obj K)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_comp,
    ← Category.assoc, ← hu, Category.assoc, h]
  have he := e.hom.naturality (a.unit.app K)
  have hn := a.unit.naturality (e.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj] at he hn
  exact he.trans hn


set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- The open identity mate, with its native unit normalization.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply the open-adjunction mate bijection to the normalized pullback square
identity. Its triangle identities contract the unit and counit to identity. -/
theorem open_identity {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : D Λ X) :
    (openMate Λ (CommSq.mk
      ((Category.id_comp j).trans (Category.comp_id j).symm))).app K ≫
        (leftDerivedUpperStarId Λ Y).hom.app ((J Λ j).obj K) =
      (J Λ j).map ((leftDerivedUpperStarId Λ X).hom.app K) := by
  unfold openMate
  refine open_identity_aux (oa Λ j) (P Λ (𝟙 X)) (P Λ (𝟙 Y))
    (leftDerivedUpperStarId Λ X) (leftDerivedUpperStarId Λ Y)
    (pullbackSquareComparison Λ (CommSq.mk
      ((Category.id_comp j).trans (Category.comp_id j).symm))).symm ?_ K
  intro N
  apply (cancel_epi ((pullbackSquareComparison Λ (CommSq.mk
    ((Category.id_comp j).trans (Category.comp_id j).symm))).hom.app N)).1
  rw [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact (pullbackSquareComparison_identity Λ j N).symm

set_option maxHeartbeats 1600000 in
-- Compute only the tensorator field of the native monoidal structure.
private theorem native_delta {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : D Λ Y) :
    Functor.OplaxMonoidal.δ (P Λ f) K L = ((leftDerivedUpperStarTensor Λ f).app K).app L := by
  rfl

set_option maxHeartbeats 1600000 in
-- Match the two adjoint transposes after identifying their tensorator fields.
private theorem proper_projection_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (K : D Λ X) (L : D Λ Y) :
    properProjectionMorphism Λ f K L = moduleObjectProjectionMap Λ f K L := by
  unfold properProjectionMorphism moduleObjectProjectionMap moduleObjectProjectionData
  rw [Adjunction.rightAdjointProjectionMap_app_app]
  unfold Adjunction.projectionMorphism
  rw [native_delta]
  rfl


set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- The native compact projection has exactly the specified proper/open factorization.
This records the connection to the dependency's explicit projection-mate interface.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the native monoidal pullback has tensorator the inverse K-flat comparison.
Consequently its adjunction projection morphism is the same counit transpose as
`moduleObjectProjectionMap`. The remaining two factors are, by definition, the
inverse open projection and the inverse compactification pullback compositor. -/
theorem pf_factorization {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : D Λ X) (L : D Λ Y) :
    pf Λ c K L = moduleObjectProjectionMap Λ c.g ((J Λ c.i).obj K) L ≫
      (R Λ c.g).map
        (inv (openImmersionProjectionComparison Λ c.i K ((P Λ c.g).obj L)) ≫
          (J Λ c.i).map (𝟙 K ⊗ₘ (leftDerivedUpperStarCompactificationIso Λ c).inv.app L)) := by
  have hpf : pf Λ c K L = properProjectionMorphism Λ c.g ((J Λ c.i).obj K) L ≫
      (R Λ c.g).map
        (inv (openImmersionProjectionComparison Λ c.i K ((P Λ c.g).obj L)) ≫
          (J Λ c.i).map (𝟙 K ⊗ₘ (leftDerivedUpperStarCompactificationIso Λ c).inv.app L)) := by
    unfold pf exceptionalProjectionMorphismOfCompactification
    simp only [CategoryTheory.MonoidalCategory.id_tensorHom]
  exact hpf.trans (congrArg (fun m ↦ m ≫ _) (proper_projection_eq Λ c.g _ L))

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- Transport of composition of open extensions uses the adjoint-normalized compositor.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: both routes are the open mates of the horizontal pullback-pasting equation.
The composite open adjunction fixes `jComp`, and mate pasting identifies its two
transposes. Injectivity of the mate bijection gives the equation. -/
theorem open_composition {X Y Z X' Y' Z' : Scheme.{u}}
    {j : X ⟶ Y} {i : Y ⟶ Z} {j' : X' ⟶ Y'} {i' : Y' ⟶ Z'}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    {a : X' ⟶ X} {b : Y' ⟶ Y} {d : Z' ⟶ Z}
    (s : CommSq a j' j b) (t : CommSq b i' i d)
    (outer : CommSq a (j' ≫ i') (j ≫ i) d) (K : D Λ X) :
    (J Λ i').map ((openMate Λ s).app K) ≫ (openMate Λ t).app ((J Λ j).obj K) =
      (jComp Λ j' i').hom.app ((P Λ a).obj K) ≫ (openMate Λ outer).app K ≫
        (P Λ d).map ((jComp Λ j i).inv.app K) := by
  sorry

/-- Native pullback comparison for an isomorphism followed by its inverse.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def pInverse {A B : Scheme.{u}} (a : A ⟶ B) [IsIso a] :
    P Λ a ⋙ P Λ (inv a) ≅ 𝟭 (D Λ B) :=
  (leftDerivedUpperStarComp Λ (inv a) a).symm ≪≫
    eqToIso (congrArg (P Λ) (IsIso.inv_hom_id a)) ≪≫ leftDerivedUpperStarId Λ B

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- The specified inverse-square direct exchange is the inverse, under native identifications.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: paste the square and its inverse. Pullback pasting contracts the two outside
compositors to `pInverse`. Direct identity exchange contracts the middle paste to
identity. Swapping the two squares gives the other inverse equation. -/
theorem direct_inverse {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    [IsIso w] [IsIso v] (s : CommSq w f' f v)
    (s' : CommSq (inv w) f f' (inv v)) (K : D Λ X) :
    (P Λ (inv v)).map ((baseChangeMap Λ s).app K) ≫
        (baseChangeMap Λ s').app ((P Λ w).obj K) ≫
        (R Λ f).map ((pInverse Λ w).hom.app K) =
      (pInverse Λ v).hom.app ((R Λ f).obj K) := by
  sorry

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
/-- A general isomorphism of refinement diagrams preserves the specified refinement map.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the vertex isomorphisms identify the two pulled-back target opens, the
clopen sections, and their complementary opens. Both coordinates of the projector
are preserved. Open mate coherence identifies the adjuncts, and proper mate pasting
with the native direct compositor identifies their compact-support transposes.
This is the displayed equality; no field-linearity hypothesis enters. -/
theorem refinement_cube {X Y A B : Scheme.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    {c₁ c₂ : Compactification f} {d₁ d₂ : Compactification g}
    (u : c₁.Refinement c₂) (z : d₁.Refinement d₂)
    {a : A ⟶ X} {b : B ⟶ Y} [IsIso a] [IsIso b]
    (s₁ : Square c₁ d₁ a b) (s₂ : Square c₂ d₂ a b)
    [IsIso s₁.middle] [IsIso s₂.middle]
    (h : z.hom ≫ s₂.middle = s₁.middle ≫ u.hom) (K : D Λ X) :
    (P Λ b).map ((refinement Λ u).app K) ≫ (squareExchange Λ s₁).app K =
      (squareExchange Λ s₂).app K ≫ (refinement Λ z).app ((P Λ a).obj K) := by
  sorry

/-- The specified open/proper diagram of the literal pullback model. -/
private def literalSquare {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) :
    Square c (c.baseChange v) (pullback.fst f v) v where
  middle := pullback.fst c.g v
  openSquare := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
  properSquare := (IsPullback.of_hasPullback c.g v).toCommSq

/-- The literal exchange uses precisely the named pullback diagram. -/
private theorem exchange_literalSquare {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) :
    exchange Λ c v = squareExchange Λ (literalSquare c v) := by
  delta exchange literalSquare
  rfl

/-- Isomorphism transport of the specified refinement, with its direction fixed.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: an isomorphism preserves the pulled-back open, its distinguished section and
the clopen projector on both coordinates. Thus it preserves the adjunct defining
refinement. Apply mate pasting to the proper adjunction and direct-image compositor;
this is exactly the displayed equation. No refinement map is inverted. -/
theorem refinement_exchange {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (v : Y' ⟶ Y) [IsIso v]
    (K : D Λ X) :
    (P Λ v).map ((refinement Λ u).app K) ≫ (exchange Λ c₁ v).app K =
      (exchange Λ c₂ v).app K ≫
        (refinement Λ (refinementBaseChange u v)).app ((P Λ (pullback.fst f v)).obj K) := by
  rw [exchange_literalSquare Λ c₁ v, exchange_literalSquare Λ c₂ v]
  have : IsIso (literalSquare c₁ v).middle := by
    dsimp only [literalSquare]
    infer_instance
  have : IsIso (literalSquare c₂ v).middle := by
    dsimp only [literalSquare]
    infer_instance
  exact refinement_cube Λ u (refinementBaseChange u v)
    (literalSquare c₁ v) (literalSquare c₂ v)
    (by simp only [literalSquare, refinementBaseChange, refinementBaseMap,
      pullback.lift_fst]) K

end AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
