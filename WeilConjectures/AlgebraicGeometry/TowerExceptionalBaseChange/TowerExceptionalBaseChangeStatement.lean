/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerMate.SmoothPurityTowerMateEvaluationReduction
public import WeilConjectures.AlgebraicGeometry.SpCondensedIntegralAdjunction.IntegralAdjunctionBijectionStatement
import WeilConjectures.AlgebraicGeometry.MixedBaseChangeOperations
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.MixedBaseChangeInput
public import WeilConjectures.AlgebraicGeometry.TowerExceptionalBaseChange.TowerExceptionalBaseChangeData
public import WeilConjectures.AlgebraicGeometry.TowerExceptionalBaseChange.TowerExceptionalBaseChangeIntegralCoordinates

/-! # Exceptional base change in current integral coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-tower.md
and its proof, clauses (1)--(3)
(blueprint: det-sp-tower-exceptional-bc).

The tower operations are the recorded ordinary derived varying-ring operations.
The integral category is the current bounded constructible full subcategory of
internal modules over the pulled-back condensed ring. No completeness condition
is imposed in its definition. A natural index n represents exponent n+1.
The auxiliary records only specify the canonical reduction, proper/open and
adjunction comparisons needed to state clause (3); all are outputs of the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.TowerExceptionalBaseChange
open IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (ex : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o ex)

/-- The existing current-coefficient presentation, shared by all four vertices.
Source: proof (3), common coefficient conventions (blueprint: det-sp-tower-exceptional-bc). -/
abbrev presentation : Presentation l E :=
  SpCondensedIntegralAdjunction.presentation l E b o q ex laws

/-- Reduction and total limit on one vertex, with the actual completion unit invertible
on Dbc. These are conclusions in the theorem, not additional hypotheses.
Source: proof (3), normalized equivalence (blueprint: det-sp-tower-exceptional-bc). -/
structure Vertex (T : Scheme.{u}) where
  limit : Limit l E (presentation l E b o q ex laws) T
  normalized : ∀ K : Constructible l E T,
    spNormalizedConstructibleTorTowers l E T (q.abelian T)
      ((red l E (presentation l E b o q ex laws) T).obj K.obj)
  fullyFaithful : (SpCondensedIntegralAdjunction.reduce l E
    (presentation l E b o q ex laws) T normalized).FullyFaithful
  completion : ∀ K : Constructible l E T,
    IsIso ((redLimitAdjunction l E (presentation l E b o q ex laws) T limit).unit.app K.obj)

/-- The already defined full restriction of reduction, in the specified tower coordinates.
Source: proof (3), red_T (blueprint: det-sp-tower-exceptional-bc). -/
abbrev reduction {T : Scheme.{u}} (r : Vertex l E b o q ex laws T) :=
  SpCondensedIntegralAdjunction.reduce l E (presentation l E b o q ex laws) T r.normalized

/-- The integral right adjoint is literally total inverse limit of G red, restricted
using its output constructibility certificate. Its comparison to G is the actual
reduction/limit counit. The left comparison is the proper/open coefficient mate.
Source: proof (3), integral adjunction (blueprint: det-sp-tower-exceptional-bc). -/
structure Support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (rX : Vertex l E b o q ex laws X) (rY : Vertex l E b o q ex laws Y)
    (geometry : ReductionGeometry l E (presentation l E b o q ex laws))
    (openIso : OpenReductionIsIso l E (presentation l E b o q ex laws) geometry)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G) where
  closed : ∀ K : Constructible l E Y,
    constantModelBoundedConstructible (spIntegralCondensed l E) X
      ((SpCondensedIntegralAdjunction.rightAmbient l E
        (presentation l E b o q ex laws) rX.limit rY.normalized G).obj K)
  supportClosed : ∀ M : Constructible l E X,
    constantModelBoundedConstructible (spIntegralCondensed l E) Y
      ((shriek l E c).obj M.obj)
  leftComparison : SpCondensedIntegralAdjunction.support l E c supportClosed ⋙
      reduction l E b o q ex laws rY ≅
    reduction l E b o q ex laws rX ⋙ SpTowerGluing.support l E b o q c hF
  left_normalized : ∀ M : Constructible l E X, (leftComparison.hom.app M).hom =
    towerBaseChange l E (presentation l E b o q ex laws) geometry openIso c M.obj
  rightComparison : SpCondensedIntegralAdjunction.right l E
      (presentation l E b o q ex laws) rX.limit rY.normalized G closed ⋙
        reduction l E b o q ex laws rX ≅ reduction l E b o q ex laws rY ⋙ G
  right_normalized : ∀ K : Constructible l E Y, (rightComparison.hom.app K).hom =
    (redLimitAdjunction l E (presentation l E b o q ex laws) X rX.limit).counit.app
      (G.obj ((reduction l E b o q ex laws rY).obj K)).obj
  adjunction : SpCondensedIntegralAdjunction.support l E c supportClosed ⊣
    SpCondensedIntegralAdjunction.right l E (presentation l E b o q ex laws)
      rX.limit rY.normalized G closed
  counit : ∀ K : Constructible l E Y,
    (reduction l E b o q ex laws rY).map (adjunction.counit.app K) =
      leftComparison.hom.app _ ≫
        (SpTowerGluing.support l E b o q c hF).map (rightComparison.hom.app K) ≫
          adj.counit.app ((reduction l E b o q ex laws rY).obj K)

/-- The same specified integral support and right adjoint, with no new construction.
Source: clause (3), integral f_! (blueprint: det-sp-tower-exceptional-bc). -/
abbrev support {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {rX : Vertex l E b o q ex laws X} {rY : Vertex l E b o q ex laws Y}
    {g : ReductionGeometry l E (presentation l E b o q ex laws)}
    {h : OpenReductionIsIso l E (presentation l E b o q ex laws) g}
    {hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj)}
    {G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X}
    {adj : SpTowerGluing.support l E b o q c hF ⊣ G}
    (s : Support l E b o q ex laws c rX rY g h hF G adj) :=
  SpCondensedIntegralAdjunction.support l E c s.supportClosed

/-- The right adjoint is the dependency's inverse limit, not an arbitrary functor.
Source: clause (3), integral f^! (blueprint: det-sp-tower-exceptional-bc). -/
abbrev right {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {rX : Vertex l E b o q ex laws X} {rY : Vertex l E b o q ex laws Y}
    {g : ReductionGeometry l E (presentation l E b o q ex laws)}
    {h : OpenReductionIsIso l E (presentation l E b o q ex laws) g}
    {hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj)}
    {G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X}
    {adj : SpTowerGluing.support l E b o q c hF ⊣ G}
    (s : Support l E b o q ex laws c rX rY g h hF G adj) :=
  SpCondensedIntegralAdjunction.right l E (presentation l E b o q ex laws)
    rX.limit rY.normalized G s.closed

/-- Full restriction of the actual total derived module inverse image.
Source: clause (3), integral inverse image (blueprint: det-sp-tower-exceptional-bc). -/
def pullback {U T : Scheme.{u}} (h : U ⟶ T)
    (closed : ∀ K : Constructible l E T,
      constantModelBoundedConstructible (spIntegralCondensed l E) U
        ((pull l E h).obj K.obj)) : Constructible l E T ⥤ Constructible l E U :=
  (constantModelBoundedConstructible (spIntegralCondensed l E) U).lift
    ((constantModelBoundedConstructible (spIntegralCondensed l E) T).ι ⋙ pull l E h) closed

/-- The reduction comparison for arbitrary inverse image. Its normalization is the
K-flat scalar/pullback comparison of ReductionGeometry, transported through the exact
section equivalence; a sign or a family of unrelated finite arrows cannot be substituted.
Source: proof (3), inverse-image reductions (blueprint: det-sp-tower-exceptional-bc). -/
structure Pull {U T : Scheme.{u}} (h : U ⟶ T)
    (rU : Vertex l E b o q ex laws U) (rT : Vertex l E b o q ex laws T)
    (g : ReductionGeometry l E (presentation l E b o q ex laws))
    (hT : ∀ K : SpTowerCalculus.C l E b q T,
      spConstructibleTorTowers l E U (q.abelian U)
        ((SpTowerCalculus.etalePullback l E b o q h).obj K.obj)) where
  closed : ∀ K : Constructible l E T,
    constantModelBoundedConstructible (spIntegralCondensed l E) U ((pull l E h).obj K.obj)
  comparison : pullback l E h closed ⋙ reduction l E b o q ex laws rU ≅
    reduction l E b o q ex laws rT ⋙ ObjectProperty.lift _
      (SpTowerCalculus.inclusion l E b q T ⋙ SpTowerCalculus.etalePullback l E b o q h) hT
  normalized : ∀ K : Constructible l E T, (comparison.hom.app K).hom =
    (SpTowerCalculus.realization l E b U (q.abelian U)).unitIso.hom.app
        ((red l E (presentation l E b o q ex laws) U).obj ((pull l E h).obj K.obj)) ≫
      (SpTowerCalculus.realization l E b U (q.abelian U)).inverse.map
        ((g.pullback h).derived.hom.app K.obj)

variable {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y} {sq : IsPullback u' f' f v} {c : Compactification f}
  (a : SpTowerMate.Data l E b o q sq c)

/-- Clause (3), with whole-tower reduction and literal total-limit realization.
The integral exchange is fixed by reduction, and its exceptional mate by the counit.
Every vertex, membership certificate, and comparison here is an output. In particular
normalization or completeness is not assumed of the input constructible complex.
Source: proof (3), final paragraph (blueprint: det-sp-tower-exceptional-bc). -/
def IntegralConclusion (hb : IsIso (SpTowerMate.beta l E b o q a ex)) : Prop :=
  ∃ (rX : Vertex l E b o q ex laws X) (rY : Vertex l E b o q ex laws Y)
    (rX' : Vertex l E b o q ex laws X') (rY' : Vertex l E b o q ex laws Y'),
  ∃ g : ReductionGeometry l E (presentation l E b o q ex laws),
  ∃ h : OpenReductionIsIso l E (presentation l E b o q ex laws) g,
  ∃ s : Support l E b o q ex laws c rX rY g h a.support_closed a.right a.adjunction,
  ∃ s' : Support l E b o q ex laws (c.ofIsPullback sq) rX' rY' g h
    a.support_closed' a.right' a.adjunction',
  ∃ pu : Pull l E b o q ex laws u' rX' rX g a.pull_closed,
  ∃ pv : Pull l E b o q ex laws v rY' rY g a.pull_closed',
  ∃ beta : support l E b o q ex laws s ⋙ pullback l E v pv.closed ≅
    pullback l E u' pu.closed ⋙ support l E b o q ex laws s',
    (∀ M : Constructible l E X,
      (reduction l E b o q ex laws rY').map (beta.hom.app M) =
        pv.comparison.hom.app _ ≫
          (SpTowerMate.V l E b o q a).map (s.leftComparison.hom.app M) ≫
          (SpTowerMate.beta l E b o q a ex).app
            ((reduction l E b o q ex laws rX).obj M) ≫
          (SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed').map
            (pu.comparison.inv.app M) ≫ s'.leftComparison.inv.app _) ∧
    ∀ K : Constructible l E Y,
    ∃ e : (pullback l E u' pu.closed).obj ((right l E b o q ex laws s).obj K) ⟶
      (right l E b o q ex laws s').obj ((pullback l E v pv.closed).obj K),
      IsIso e ∧
      e = s'.adjunction.homEquiv _ _
        (beta.inv.app ((right l E b o q ex laws s).obj K) ≫
          (pullback l E v pv.closed).map (s.adjunction.counit.app K)) ∧
      (reduction l E b o q ex laws rX').map e =
        pu.comparison.hom.app _ ≫
          (SpTowerMate.U l E b o q a).map (s.rightComparison.hom.app K) ≫
          (SpTowerMate.mate l E b o q a ex hb).app
            ((reduction l E b o q ex laws rY).obj K) ≫
          a.right'.map (pv.comparison.inv.app K) ≫ s'.rightComparison.inv.app _ ∧
      e.hom ≫ (redLimitAdjunction l E (presentation l E b o q ex laws) X' rX'.limit).unit.app
          ((right l E b o q ex laws s').obj ((pullback l E v pv.closed).obj K)).obj =
        (redLimitAdjunction l E (presentation l E b o q ex laws) X' rX'.limit).unit.app
            ((pullback l E u' pu.closed).obj ((right l E b o q ex laws s).obj K)).obj ≫
          (lim l E (presentation l E b o q ex laws) X' rX'.limit).map
            ((pu.comparison.hom.app _ ≫
              (SpTowerMate.U l E b o q a).map (s.rightComparison.hom.app K) ≫
              (SpTowerMate.mate l E b o q a ex hb).app
                ((reduction l E b o q ex laws rY).obj K) ≫
              a.right'.map (pv.comparison.inv.app K) ≫ s'.rightComparison.inv.app _).hom)

private theorem counit_transport
    {C D C' D' A B A' B' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Category A] [Category B] [Category A'] [Category B']
    (rC : C ⥤ A) (rD : D ⥤ B) (rC' : C' ⥤ A') (rD' : D' ⥤ B')
    [rD'.Faithful]
    (F : C ⥤ D) (G : D ⥤ C) (F' : C' ⥤ D') (G' : D' ⥤ C')
    (U : C ⥤ C') (V : D ⥤ D')
    (Ft : A ⥤ B) (Gt : B ⥤ A) (Ft' : A' ⥤ B') (Gt' : B' ⥤ A')
    (Ut : A ⥤ A') (Vt : B ⥤ B')
    (ad : F ⊣ G) (ad' : F' ⊣ G') (adt : Ft ⊣ Gt) (adt' : Ft' ⊣ Gt')
    (sf : F ⋙ rD ≅ rC ⋙ Ft) (sf' : F' ⋙ rD' ≅ rC' ⋙ Ft')
    (sg : G ⋙ rC ≅ rD ⋙ Gt) (sg' : G' ⋙ rC' ≅ rD' ⋙ Gt')
    (su : U ⋙ rC' ≅ rC ⋙ Ut) (sv : V ⋙ rD' ≅ rD ⋙ Vt)
    (bt : Ft ⋙ Vt ⟶ Ut ⋙ Ft') (mt : Gt ⋙ Ut ⟶ Vt ⋙ Gt')
    (beta : F ⋙ V ≅ U ⋙ F') (K : D)
    (e : U.obj (G.obj K) ⟶ G'.obj (V.obj K))
    (hb : rD'.map (beta.hom.app (G.obj K)) =
      sv.hom.app (F.obj (G.obj K)) ≫ Vt.map (sf.hom.app (G.obj K)) ≫
        bt.app (rC.obj (G.obj K)) ≫ Ft'.map (su.inv.app (G.obj K)) ≫
          sf'.inv.app (U.obj (G.obj K)))
    (he : rC'.map e = su.hom.app (G.obj K) ≫ Ut.map (sg.hom.app K) ≫
      mt.app (rD.obj K) ≫ Gt'.map (sv.inv.app K) ≫ sg'.inv.app (V.obj K))
    (hc : rD.map (ad.counit.app K) = sf.hom.app (G.obj K) ≫
      Ft.map (sg.hom.app K) ≫ adt.counit.app (rD.obj K))
    (hc' : rD'.map (ad'.counit.app (V.obj K)) = sf'.hom.app (G'.obj (V.obj K)) ≫
      Ft'.map (sg'.hom.app (V.obj K)) ≫ adt'.counit.app (rD'.obj (V.obj K)))
    (ht : bt.app (Gt.obj (rD.obj K)) ≫ Ft'.map (mt.app (rD.obj K)) ≫
      adt'.counit.app (Vt.obj (rD.obj K)) = Vt.map (adt.counit.app (rD.obj K))) :
    beta.hom.app (G.obj K) ≫ F'.map e ≫ ad'.counit.app (V.obj K) =
      V.map (ad.counit.app K) := by
  apply rD'.map_injective
  simp only [Functor.map_comp]
  rw [hc']
  have hn : rD'.map (F'.map e) ≫ sf'.hom.app (G'.obj (V.obj K)) =
      sf'.hom.app (U.obj (G.obj K)) ≫ Ft'.map (rC'.map e) :=
    sf'.hom.naturality e
  rw [reassoc_of% hn]
  simp only [Functor.comp_obj]
  rw [he]
  apply (cancel_mono (sv.hom.app K)).1
  rw [hb]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hu : Ft'.map (su.inv.app (G.obj K)) ≫ Ft'.map (su.hom.app (G.obj K)) =
      𝟙 _ := by rw [← Ft'.map_comp, su.inv_hom_id_app, Ft'.map_id]
  have hg : Ft'.map (sg'.inv.app (V.obj K)) ≫
      Ft'.map (sg'.hom.app (V.obj K)) = 𝟙 _ := by
    rw [← Ft'.map_comp, sg'.inv_hom_id_app, Ft'.map_id]
  rw [reassoc_of% hu, reassoc_of% hg]
  have hcounit : Ft'.map (Gt'.map (sv.inv.app K)) ≫
      adt'.counit.app (rD'.obj (V.obj K)) =
      adt'.counit.app (Vt.obj (rD.obj K)) ≫ sv.inv.app K :=
    adt'.counit.naturality (sv.inv.app K)
  rw [reassoc_of% hcounit]
  simp only [Iso.inv_hom_id_app]
  slice_lhs 3 4 => exact (bt.naturality (sg.hom.app K)).symm
  simp only [Functor.comp_map, Functor.comp_obj, Category.assoc, Category.comp_id]
  rw [ht]
  rw [← Vt.map_comp, ← Vt.map_comp, ← hc]
  exact (sv.hom.naturality (ad.counit.app K)).symm

private def integralExchange (hb : IsIso (SpTowerMate.beta l E b o q a ex)) :
    support l E b o q ex laws s.support ⋙ pullback l E v s.pull'.closed ≅
      pullback l E u' s.pull.closed ⋙ support l E b o q ex laws s.support' := by
  letI := hb
  let F := support l E b o q ex laws s.support
  let F' := support l E b o q ex laws s.support'
  let U := pullback l E u' s.pull.closed
  let V := pullback l E v s.pull'.closed
  let Ft := SpTowerGluing.support l E b o q c a.support_closed
  let Ft' := SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed'
  let Ut := SpTowerMate.U l E b o q a
  let Vt := SpTowerMate.V l E b o q a
  let rX := reduction l E b o q ex laws s.rX
  let rY' := reduction l E b o q ex laws s.rY'
  let e : (F ⋙ V) ⋙ rY' ≅ (U ⋙ F') ⋙ rY' :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F s.pull'.comparison ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight s.support.leftComparison Vt ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft rX (asIso (SpTowerMate.beta l E b o q a ex)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight s.pull.comparison.symm Ft' ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft U s.support'.leftComparison.symm ≪≫
      (Functor.associator _ _ _).symm
  exact (s.rY'.fullyFaithful.whiskeringRight _).preimageIso e

private theorem integralExchange_reduction
    (hb : IsIso (SpTowerMate.beta l E b o q a ex)) (M : Constructible l E X) :
    (reduction l E b o q ex laws s.rY').map
        ((integralExchange l E b o q ex laws a s hb).hom.app M) =
      s.pull'.comparison.hom.app _ ≫
        (SpTowerMate.V l E b o q a).map (s.support.leftComparison.hom.app M) ≫
        (SpTowerMate.beta l E b o q a ex).app
          ((reduction l E b o q ex laws s.rX).obj M) ≫
        (SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed').map
          (s.pull.comparison.inv.app M) ≫ s.support'.leftComparison.inv.app _ := by
  unfold integralExchange
  simp only [Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    asIso_hom, Category.id_comp, Category.comp_id]
  exact Category.id_comp _

private def reconstructed (hb : IsIso (SpTowerMate.beta l E b o q a ex))
    (K : Constructible l E Y) :
    (pullback l E u' s.pull.closed).obj ((right l E b o q ex laws s.support).obj K) ⟶
      (right l E b o q ex laws s.support').obj
        ((pullback l E v s.pull'.closed).obj K) :=
  s.rX'.fullyFaithful.preimage
    (s.pull.comparison.hom.app _ ≫
      (SpTowerMate.U l E b o q a).map (s.support.rightComparison.hom.app K) ≫
      (SpTowerMate.mate l E b o q a ex hb).app
        ((reduction l E b o q ex laws s.rY).obj K) ≫
      a.right'.map (s.pull'.comparison.inv.app K) ≫ s.support'.rightComparison.inv.app _)

private theorem reconstructed_isIso (hb : IsIso (SpTowerMate.beta l E b o q a ex))
    (hm : IsIso (SpTowerMate.mate l E b o q a ex hb)) (K : Constructible l E Y) :
    IsIso (reconstructed l E b o q ex laws a s hb K) := by
  have := hm
  let e := s.pull.comparison.app _ ≪≫
    (SpTowerMate.U l E b o q a).mapIso (s.support.rightComparison.app K) ≪≫
    asIso ((SpTowerMate.mate l E b o q a ex hb).app
      ((reduction l E b o q ex laws s.rY).obj K)) ≪≫
    a.right'.mapIso (s.pull'.comparison.app K).symm ≪≫
    (s.support'.rightComparison.app _).symm
  unfold reconstructed
  simpa only [Functor.FullyFaithful.preimageIso_hom, e, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, asIso_hom,
    Category.assoc] using (s.rX'.fullyFaithful.preimageIso e).isIso_hom

private theorem reconstructed_counit (hb : IsIso (SpTowerMate.beta l E b o q a ex))
    (K : Constructible l E Y) :
    (integralExchange l E b o q ex laws a s hb).hom.app
        ((right l E b o q ex laws s.support).obj K) ≫
      (support l E b o q ex laws s.support').map
        (reconstructed l E b o q ex laws a s hb K) ≫
      s.support'.adjunction.counit.app ((pullback l E v s.pull'.closed).obj K) =
    (pullback l E v s.pull'.closed).map (s.support.adjunction.counit.app K) := by
  have := hb
  let F' := SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed'
  let U := SpTowerMate.U l E b o q a
  let V := SpTowerMate.V l E b o q a
  let Kt := (reduction l E b o q ex laws s.rY).obj K
  have ht : (SpTowerMate.beta l E b o q a ex).app (a.right.obj Kt) ≫
      F'.map ((SpTowerMate.mate l E b o q a ex hb).app Kt) ≫
        a.adjunction'.counit.app (V.obj Kt) = V.map (a.adjunction.counit.app Kt) := by
    have h := mateEquiv_counit a.adjunction a.adjunction'
      (TwoSquare.mk _ _ _ _ (@inv _ _ _ _ (SpTowerMate.beta l E b o q a ex) hb)) Kt
    change F'.map ((SpTowerMate.mate l E b o q a ex hb).app Kt) ≫
      a.adjunction'.counit.app (V.obj Kt) = _ at h
    rw [h]
    simp [V]
  have := s.rY'.fullyFaithful.faithful
  apply counit_transport (reduction l E b o q ex laws s.rX)
    (reduction l E b o q ex laws s.rY) (reduction l E b o q ex laws s.rX')
    (reduction l E b o q ex laws s.rY') _ _ _ _ _ _ _ _ _ _ _ _
    s.support.adjunction s.support'.adjunction a.adjunction a.adjunction'
    s.support.leftComparison s.support'.leftComparison
    s.support.rightComparison s.support'.rightComparison
    s.pull.comparison s.pull'.comparison
    (SpTowerMate.beta l E b o q a ex) (SpTowerMate.mate l E b o q a ex hb)
    (integralExchange l E b o q ex laws a s hb) K
    (reconstructed l E b o q ex laws a s hb K)
  · exact integralExchange_reduction l E b o q ex laws a s hb _
  · unfold reconstructed
    exact s.rX'.fullyFaithful.map_preimage _
  · exact s.support.counit K
  · exact s.support'.counit _
  · exact ht

private theorem integralConclusion_of_data
    (hb : IsIso (SpTowerMate.beta l E b o q a ex))
    (hm : IsIso (SpTowerMate.mate l E b o q a ex hb)) :
    IntegralConclusion l E b o q ex laws a hb := by
  let beta := integralExchange l E b o q ex laws a s hb
  refine ⟨s.rX, s.rY, s.rX', s.rY', s.geometry, s.openIso, s.support, s.support',
    s.pull, s.pull', beta, integralExchange_reduction l E b o q ex laws a s hb, ?_⟩
  intro K
  let e := reconstructed l E b o q ex laws a s hb K
  refine ⟨e, reconstructed_isIso l E b o q ex laws a s hb hm K, ?_, ?_, ?_⟩
  · apply (s.support'.adjunction.homEquiv _ _).symm_apply_eq.mp
    change (support l E b o q ex laws s.support').map e ≫
      s.support'.adjunction.counit.app _ = _
    apply (Iso.cancel_iso_hom_left
      (beta.app ((right l E b o q ex laws s.support).obj K)) _ _).mp
    simpa only [Iso.app_hom, Category.assoc, Iso.hom_inv_id_app_assoc] using
      reconstructed_counit l E b o q ex laws a s hb K
  · exact s.rX'.fullyFaithful.map_preimage _
  · have he := congrArg (fun t ↦ t.hom) (s.rX'.fullyFaithful.map_preimage
      (s.pull.comparison.hom.app _ ≫
        (SpTowerMate.U l E b o q a).map (s.support.rightComparison.hom.app K) ≫
        (SpTowerMate.mate l E b o q a ex hb).app
          ((reduction l E b o q ex laws s.rY).obj K) ≫
        a.right'.map (s.pull'.comparison.inv.app K) ≫ s.support'.rightComparison.inv.app _))
    change (red l E (presentation l E b o q ex laws) X').map e.hom = _ at he
    rw [← he]
    exact ((redLimitAdjunction l E (presentation l E b o q ex laws) X'
      s.rX'.limit).unit.naturality e.hom)

/-- Tower exchange data, finite mates, and normalized source and target towers.
Proof: pull back the chosen compactification. Finite constant-ring inverse image
preserves constructibility and common cohomological and Tor intervals. The finite
or algebraically closed base-field argument gives bounded etale-origin witnesses.
The compact-support amplitude bound and tower shriek-level theorem restrict the
actual compactification operations to the uniformly bounded ctf categories.
Apply tower gluing to f and f' to obtain their right adjoints and the finite
unit/counit-normalized comparison data. Open exchange and proper base change define
beta, whose evaluations are the invertible finite compact-support exchange maps;
conservativity of evaluation makes beta invertible. Transpose its inverse followed
by the pulled-back counit. Evaluation of gluing units and counits identifies the
result with the finite exceptional counit mate at every level. Finite smooth
exceptional base change makes these maps invertible; evaluation conservativity
and the full inclusion reflect this to the tower mate. The gluing coefficient
counit formula gives the source and target reduction equations. The second mixed
base-change identity intertwines the finite mates with coefficient reduction;
finite mate naturality gives the full three-step reduction chain. Tower purity
normalizes the exceptional source on normalized inputs; scalar/pullback compatibility
preserves its normalization under u*. Naturality of the actual reductions transfers
normalization across the tower mate isomorphism to the target. These constructions
supply Data, Laws, both isomorphism assertions and both normalization conclusions.
Source: proof clauses (1)--(2)
(blueprint: stage3-sp-tower-exceptional-data-current).
-/
theorem tower_exceptional_base_change_data
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (pchar : ℕ) (_hp : 0 < pchar) [CharP k pchar] (_hne : l ≠ pchar)
    (X Y X' Y' : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left) :
    ∃ a : SpTowerMate.Data l E b o q sq c,
    ∃ hb : IsIso (SpTowerMate.beta l E b o q a ex),
    ∃ hfinite : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n)),
      IsIso ((SpTowerMate.finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj),
      SpTowerMate.Laws l E b o q a ex hb hfinite ∧
      IsIso (SpTowerMate.mate l E b o q a ex hb) ∧
      (∀ K : SpTowerCalculus.C l E b q Y.left,
        IsSpNormalizedTower l E Y.left (q.abelian Y.left) K.obj →
          IsSpNormalizedTower l E X'.left (q.abelian X'.left)
              (((SpTowerMate.U l E b o q a).obj (a.right.obj K)).obj) ∧
            IsSpNormalizedTower l E X'.left (q.abelian X'.left)
              ((a.right'.obj ((SpTowerMate.V l E b o q a).obj K)).obj)) := by
  sorry

/-- The integral counit transpose is the inverse limit of the specified tower mate.
Source: blueprint sk-prop-sp-purity-bc-tower.proof.md, clause (3)
(blueprint: det-sp-tower-exceptional-bc).

Proof: obtain the common geometric reduction coordinates. Lift the conjugated
whole-tower exchange and mate through fully faithful reduction. The preimage
isomorphism proves invertibility. The two reduced counit formulas and the tower
mate-counit identity identify the lift with the integral adjunction transpose.
Naturality of the actual reduction/limit unit proves the displayed limit equation.
-/
theorem tower_exceptional_base_change_integral
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (pchar : ℕ) (_hp : 0 < pchar) [CharP k pchar] (_hne : l ≠ pchar)
    (X Y X' Y' : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left)
    (a : SpTowerMate.Data l E b o q sq c)
    (hb : IsIso (SpTowerMate.beta l E b o q a ex))
    (hfinite : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n)),
      IsIso ((SpTowerMate.finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj))
    (hlaws : SpTowerMate.Laws l E b o q a ex hb hfinite)
    (hm : IsIso (SpTowerMate.mate l E b o q a ex hb))
    (hn : ∀ K : SpTowerCalculus.C l E b q Y.left,
      IsSpNormalizedTower l E Y.left (q.abelian Y.left) K.obj →
        IsSpNormalizedTower l E X'.left (q.abelian X'.left)
            (((SpTowerMate.U l E b o q a).obj (a.right.obj K)).obj) ∧
          IsSpNormalizedTower l E X'.left (q.abelian X'.left)
            ((a.right'.obj ((SpTowerMate.V l E b o q a).obj K)).obj)) :
    Module.finrank (Padic l) E = 1 → IntegralConclusion l E b o q ex laws a hb  := by
  intro hdim
  obtain ⟨s⟩ := tower_exceptional_base_change_integral_coordinates l E b o q ex laws
    k _hk pchar _hp _hne X Y X' Y' f v u' f' sq d c a hb hfinite hlaws hm hn hdim
  exact integralConclusion_of_data l E b o q ex laws a s hb hm

/-- Compact-support base change, its exceptional counit transpose, all finite evaluations
and reductions, preservation of normalized towers, and integral inverse-limit descent.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-tower.md,
clauses (1)--(3) (blueprint: det-sp-tower-exceptional-bc).

Proof:
1. Finite type over the field gives Noetherianity. Exact finite-ring inverse image
preserves constructibility and the common cohomological and Tor intervals; finite
constructible objects admit etale-origin witnesses.
2. Pull back the compactification. Extension by zero and proper base change give the
specified tower exchange. Boundedness and finite evaluation restrict it to Dctf.
Base-change stability makes f' smooth of the same dimension.
3. Transpose inverse exchange followed by v* of the counit. The gluing adjunction
unit and counit formulas identify its evaluations with the finite exceptional mates.
Finite smooth cohomological smoothness over the finite or algebraically closed field
makes them invertible. Conservativity of derived evaluation gives a tower isomorphism.
4. The mixed coefficient/base-change identity and the gluing transition formula
identify the two reductions. The finite exceptional coefficient comparisons are
invertible, so normalized inputs give normalized sources and targets.
5. At E = Q_l use the reduction/total-limit adjunction and normalized equivalence.
The direct-image tower comparison and canonical tensor/pullback comparisons identify
integral support and inverse image with their whole reduction towers. Restrict the
tower adjunction along fully faithful reduction, with its actual units and counits.
Mate pasting carries the integral proper/open exchange to tower beta. Full
faithfulness identifies the integral counit transpose with the limit of the tower
mate. The completion units give exactly the displayed limit equation and transfer
invertibility. The coefficient construction is common to all four vertices. -/
theorem tower_exceptional_base_change_statement
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (pchar : ℕ) (_hp : 0 < pchar) [CharP k pchar] (_hne : l ≠ pchar)
    (X Y X' Y' : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left) :
    ∃ a : SpTowerMate.Data l E b o q sq c,
    ∃ hb : IsIso (SpTowerMate.beta l E b o q a ex),
    ∃ hfinite : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n)),
      IsIso ((SpTowerMate.finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj),
      SpTowerMate.Laws l E b o q a ex hb hfinite ∧
      IsIso (SpTowerMate.mate l E b o q a ex hb) ∧
      (∀ K : SpTowerCalculus.C l E b q Y.left,
        IsSpNormalizedTower l E Y.left (q.abelian Y.left) K.obj →
          IsSpNormalizedTower l E X'.left (q.abelian X'.left)
              (((SpTowerMate.U l E b o q a).obj (a.right.obj K)).obj) ∧
            IsSpNormalizedTower l E X'.left (q.abelian X'.left)
              ((a.right'.obj ((SpTowerMate.V l E b o q a).obj K)).obj)) ∧
      (Module.finrank (Padic l) E = 1 → IntegralConclusion l E b o q ex laws a hb) := by
  obtain ⟨a, hb, hfinite, hlaws, hm, hn⟩ :=
    tower_exceptional_base_change_data l E b o q ex k _hk pchar _hp _hne
      X Y X' Y' f v u' f' sq d c
  refine ⟨a, hb, hfinite, hlaws, hm, hn, ?_⟩
  intro hdim
  exact tower_exceptional_base_change_integral l E b o q ex laws k _hk pchar _hp _hne
    X Y X' Y' f v u' f' sq d c a hb hfinite hlaws hm hn hdim

end AlgebraicGeometry.ProEtale.TowerExceptionalBaseChange
