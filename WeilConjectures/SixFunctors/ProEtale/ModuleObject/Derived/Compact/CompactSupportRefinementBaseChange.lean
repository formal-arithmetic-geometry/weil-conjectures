/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportOpenRefinementPasting
import WeilConjectures.AlgebraicGeometry.Compactification.DenseRefinementMorphisms

/-!
# Pasting compact-support exchange with dense refinements

Source: blueprint det-sf-comp-composition-base-change, proof steps 4--7.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.rightDerivedFunctor Functor.mapDerivedCategory Functor.leftDerivedFunctor
  derivedUpperStarLowerStarAdjunction derivedOpenImmersionLowerShriekUpperStarAdjunction
  refinementDerivedLowerStarComp
  leftDerivedUpperStarIsoMapDerivedCategory upperStarLowerStarAdjunction
  condensedAmbientPullbackComparison AlgebraicGeometry.ProEtale.upperStarFromPoint
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Sheaf.monoidalCategory DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] compactificationRefinementComponent
  detSfCompactSupportBaseChangeComposite detSfCompactSupportExchangeData
  condensedAmbientExchange detSfOpenBaseChangeMap localizingRefinementMap refinementTheta
  compactSupportPushforwardTriangle compactSupportTrianglePullbackSquare
  compactSupportTrianglePullback detSfProperBaseChangeSquare
  instCategoryDerivedCategory MorphismProperty.instCategoryLocalization

-- Keep the mate abstract so component conversions do not unfold its adjunction data.
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem refinement_component_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c : Compactification f} {d : Compactification.BoundaryCompactification f}
    (h : d ⟶ detSfBoundaryCompactification c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    compactificationRefinementComponent Λ h K =
      R((c.g)_*⟦Λ⟧).map (localizingRefinementMap Λ h K) ≫
        (compactSupportPushforwardTriangle Λ h.hom.hom.hom c.g d.obj.obj.g
          h.hom.hom.hom_g).hom.app (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) := by
  rfl

private theorem refinement_baseChange_component_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (v : Y' ⟶ Y) {c : Compactification f}
    {d : Compactification.BoundaryCompactification (pullback.snd f v)}
    (h : d ⟶ detSfBoundaryCompactification (c.baseChange v))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (pullback f v)) Ab.{u + 1})
        (condensedRingObj Λ (pullback f v)))) :
    compactificationRefinementComponent Λ h K =
      R((pullback.snd c.g v)_*⟦Λ⟧).map (localizingRefinementMap Λ h K) ≫
        (compactSupportPushforwardTriangle Λ h.hom.hom.hom (pullback.snd c.g v)
          d.obj.obj.g h.hom.hom.hom_g).hom.app (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) := by
  rfl

private theorem exchange_component_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y)
    (c : Compactification f) (o :
      D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
        detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (detSfCompactSupportBaseChangeComposite Λ f v c o).app K =
      (detSfProperBaseChangeMap Λ c.g v).app (D((c.i)_!open⟦Λ⟧).obj K) ≫
        R((pullback.snd c.g v)_*⟦Λ⟧).map (o.hom.app K) :=
  (detSfCompactSupportExchangeData Λ f v c o).component K

private theorem proper_chase
    {F C D E : Type*} [Category F] [Category C] [Category D] [Category E]
    (V : F ⥤ D) (P : C ⥤ D) (Q : E ⥤ D)
    {A₀ B₀ C₀ : F} {Z : D} {S T U : C} {M N L : E}
    {x : A₀ ⟶ B₀} {b : B₀ ⟶ C₀} {rho : A₀ ⟶ C₀}
    {d : V.obj C₀ ⟶ Q.obj M} {ks : Q.obj L ⟶ Z}
    {ca : V.obj A₀ ⟶ P.obj S} {cb : V.obj B₀ ⟶ P.obj T} {kr : P.obj U ⟶ Z}
    {u : S ⟶ T} {l : T ⟶ U} {od : M ⟶ N} {ed : N ⟶ L}
    {bd : V.obj C₀ ⟶ Q.obj N} {rd : Q.obj N ⟶ Z}
    (hρ : rho = x ≫ b) (hbd : bd = d ≫ Q.map od) (hrd : rd = Q.map ed ≫ ks)
    (hp : V.map b ≫ d ≫ Q.map (od ≫ ed) ≫ ks = cb ≫ P.map l ≫ kr)
    (hn : V.map x ≫ cb = ca ≫ P.map u) :
    V.map rho ≫ bd ≫ rd = ca ≫ P.map (u ≫ l) ≫ kr := by
  rw [hρ, hbd, hrd, V.map_comp]
  simp only [Category.assoc]
  rw [← Q.map_comp_assoc, hp, reassoc_of% hn, ← P.map_comp_assoc]

private theorem open_chase
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {A Z : D} {S T U W : C} {ca : A ⟶ P.obj S} {kr : P.obj U ⟶ Z}
    {u : S ⟶ T} {l : T ⟶ U} {o : S ⟶ W} {e : W ⟶ U}
    {bc : A ⟶ P.obj W} {rc : P.obj W ⟶ Z}
    (hbc : bc = ca ≫ P.map o) (hrc : rc = P.map e ≫ kr)
    (hl : u ≫ l = o ≫ e) :
    ca ≫ P.map (u ≫ l) ≫ kr = bc ≫ rc := by
  rw [hl, P.map_comp, hbc, hrc]
  simp only [Category.assoc]

private theorem proper_stage_of_pasting
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c : Compactification f) (d : Compactification.BoundaryCompactification f)
    (h : d ⟶ detSfBoundaryCompactification c)
    (w : Compactification.BoundaryCompactification (pullback.snd f v))
    (hd : w ⟶ detSfBoundaryCompactification (d.obj.obj.baseChange v))
    (hc : w ⟶ detSfBoundaryCompactification (c.baseChange v))
    (esr : hd.hom.hom.hom ≫ compactSupportTrianglePullback h.hom.hom.hom c.g
      d.obj.obj.g h.hom.hom.hom_g v = hc.hom.hom.hom)
    (od : D((d.obj.obj.i)_!open⟦Λ⟧) ⋙
      detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙
        D(((d.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (β : R((c.g)_*⟦Λ⟧) ⋙ detSfDerivedPullback Λ v ⟶
      detSfDerivedPullback Λ (pullback.fst c.g v) ⋙ R((pullback.snd c.g v)_*⟦Λ⟧))
    (hp : (detSfDerivedPullback Λ v).map
          ((compactSupportPushforwardTriangle Λ h.hom.hom.hom c.g d.obj.obj.g
            h.hom.hom.hom_g).hom.app (D((d.obj.obj.i)_!open⟦Λ⟧).obj K)) ≫
        (detSfProperBaseChangeMap Λ d.obj.obj.g v).app (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) ≫
        R((pullback.snd d.obj.obj.g v)_*⟦Λ⟧).map
          (od.hom.app K ≫ localizingRefinementMap Λ hd
            ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) ≫
        (compactSupportPushforwardTriangle Λ hd.hom.hom.hom
          (pullback.snd d.obj.obj.g v) w.obj.obj.g hd.hom.hom.hom_g).hom.app
            (D((w.obj.obj.i)_!open⟦Λ⟧).obj
              ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) =
      β.app (R((h.hom.hom.hom)_*⟦Λ⟧).obj (D((d.obj.obj.i)_!open⟦Λ⟧).obj K)) ≫
        R((pullback.snd c.g v)_*⟦Λ⟧).map
          ((condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare
            h.hom.hom.hom c.g d.obj.obj.g h.hom.hom.hom_g v)).app
              (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) ≫
            R((compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g
              h.hom.hom.hom_g v)_*⟦Λ⟧).map
                (od.hom.app K ≫ localizingRefinementMap Λ hd
                  ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) ≫
            (compactSupportPushforwardTriangle Λ hd.hom.hom.hom
              (compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g
                h.hom.hom.hom_g v) hc.hom.hom.hom esr).hom.app
                  (D((w.obj.obj.i)_!open⟦Λ⟧).obj
                    ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))) ≫
        (compactSupportPushforwardTriangle Λ hc.hom.hom.hom (pullback.snd c.g v)
          w.obj.obj.g hc.hom.hom.hom_g).hom.app
            (D((w.obj.obj.i)_!open⟦Λ⟧).obj
              ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))) :
    (detSfDerivedPullback Λ v).map (compactificationRefinementComponent Λ h K) ≫
      (detSfCompactSupportBaseChangeComposite Λ f v d.obj.obj od).app K ≫
      compactificationRefinementComponent Λ hd
        ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) =
    β.app (D((c.i)_!open⟦Λ⟧).obj K) ≫
        R((pullback.snd c.g v)_*⟦Λ⟧).map
          ((detSfDerivedPullback Λ (pullback.fst c.g v)).map (localizingRefinementMap Λ h K) ≫
            (condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare
              h.hom.hom.hom c.g d.obj.obj.g h.hom.hom.hom_g v)).app
                (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) ≫
            R((compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g
              h.hom.hom.hom_g v)_*⟦Λ⟧).map
                (od.hom.app K ≫ localizingRefinementMap Λ hd
                  ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) ≫
            (compactSupportPushforwardTriangle Λ hd.hom.hom.hom
              (compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g
                h.hom.hom.hom_g v) hc.hom.hom.hom esr).hom.app
                  (D((w.obj.obj.i)_!open⟦Λ⟧).obj
                    ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))) ≫
        (compactSupportPushforwardTriangle Λ hc.hom.hom.hom (pullback.snd c.g v)
          w.obj.obj.g hc.hom.hom.hom_g).hom.app
            (D((w.obj.obj.i)_!open⟦Λ⟧).obj
              ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) := by
  have hn := β.naturality (localizingRefinementMap Λ h K)
  exact proper_chase (detSfDerivedPullback Λ v)
    R((pullback.snd c.g v)_*⟦Λ⟧) R((pullback.snd d.obj.obj.g v)_*⟦Λ⟧)
    (refinement_component_eq Λ h K)
    (exchange_component_eq Λ f v d.obj.obj od K)
    (refinement_baseChange_component_eq Λ v hd
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) hp hn

private theorem proper_stage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c : Compactification f) (d : Compactification.BoundaryCompactification f)
    (h : d ⟶ detSfBoundaryCompactification c)
    (w : Compactification.BoundaryCompactification (pullback.snd f v))
    (hd : w ⟶ detSfBoundaryCompactification (d.obj.obj.baseChange v))
    (hc : w ⟶ detSfBoundaryCompactification (c.baseChange v))
    (esr : hd.hom.hom.hom ≫ compactSupportTrianglePullback h.hom.hom.hom c.g
      d.obj.obj.g h.hom.hom.hom_g v = hc.hom.hom.hom)
    (od : D((d.obj.obj.i)_!open⟦Λ⟧) ⋙
      detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙
        D(((d.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (detSfDerivedPullback Λ v).map (compactificationRefinementComponent Λ h K) ≫
      (detSfCompactSupportBaseChangeComposite Λ f v d.obj.obj od).app K ≫
      compactificationRefinementComponent Λ hd
        ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) =
    (detSfProperBaseChangeMap Λ c.g v).app (D((c.i)_!open⟦Λ⟧).obj K) ≫
        R((pullback.snd c.g v)_*⟦Λ⟧).map
          ((detSfDerivedPullback Λ (pullback.fst c.g v)).map (localizingRefinementMap Λ h K) ≫
            (condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare
              h.hom.hom.hom c.g d.obj.obj.g h.hom.hom.hom_g v)).app
                (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) ≫
            R((compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g
              h.hom.hom.hom_g v)_*⟦Λ⟧).map
                (od.hom.app K ≫ localizingRefinementMap Λ hd
                  ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) ≫
            (compactSupportPushforwardTriangle Λ hd.hom.hom.hom
              (compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g
                h.hom.hom.hom_g v) hc.hom.hom.hom esr).hom.app
                  (D((w.obj.obj.i)_!open⟦Λ⟧).obj
                    ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))) ≫
        (compactSupportPushforwardTriangle Λ hc.hom.hom.hom (pullback.snd c.g v)
          w.obj.obj.g hc.hom.hom.hom_g).hom.app
            (D((w.obj.obj.i)_!open⟦Λ⟧).obj
              ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) := by
  have hp := compactSupportProperTriangle_pasting Λ h.hom.hom.hom c.g d.obj.obj.g
    h.hom.hom.hom_g v hd.hom.hom.hom hc.hom.hom.hom w.obj.obj.g hd.hom.hom.hom_g
    hc.hom.hom.hom_g esr (D((d.obj.obj.i)_!open⟦Λ⟧).obj K)
    (D((w.obj.obj.i)_!open⟦Λ⟧).obj
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))
    (od.hom.app K ≫ localizingRefinementMap Λ hd
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))
    (detSfProperBaseChangeMap Λ c.g v) rfl
  exact proper_stage_of_pasting Λ f v c d h w hd hc esr od K
    (detSfProperBaseChangeMap Λ c.g v) hp

private theorem open_stage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c : Compactification f) (d : Compactification.BoundaryCompactification f)
    (h : d ⟶ detSfBoundaryCompactification c)
    (w : Compactification.BoundaryCompactification (pullback.snd f v))
    (hd : w ⟶ detSfBoundaryCompactification (d.obj.obj.baseChange v))
    (hc : w ⟶ detSfBoundaryCompactification (c.baseChange v))
    (esr : hd.hom.hom.hom ≫ compactSupportTrianglePullback h.hom.hom.hom c.g
      d.obj.obj.g h.hom.hom.hom_g v = hc.hom.hom.hom)
    (od : D((d.obj.obj.i)_!open⟦Λ⟧) ⋙
      detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙
        D(((d.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (oc : D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧))
    (hoc : oc.inv = detSfOpenBaseChangeMap Λ f v c)
    (hod : od.inv = detSfOpenBaseChangeMap Λ f v d.obj.obj) :
    (detSfProperBaseChangeMap Λ c.g v).app (D((c.i)_!open⟦Λ⟧).obj K) ≫
        R((pullback.snd c.g v)_*⟦Λ⟧).map
          ((detSfDerivedPullback Λ (pullback.fst c.g v)).map (localizingRefinementMap Λ h K) ≫
            (condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare
              h.hom.hom.hom c.g d.obj.obj.g h.hom.hom.hom_g v)).app
                (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) ≫
            R((compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g
              h.hom.hom.hom_g v)_*⟦Λ⟧).map
                (od.hom.app K ≫ localizingRefinementMap Λ hd
                  ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) ≫
            (compactSupportPushforwardTriangle Λ hd.hom.hom.hom
              (compactSupportTrianglePullback h.hom.hom.hom c.g d.obj.obj.g
                h.hom.hom.hom_g v) hc.hom.hom.hom esr).hom.app
                  (D((w.obj.obj.i)_!open⟦Λ⟧).obj
                    ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))) ≫
        (compactSupportPushforwardTriangle Λ hc.hom.hom.hom (pullback.snd c.g v)
          w.obj.obj.g hc.hom.hom.hom_g).hom.app
            (D((w.obj.obj.i)_!open⟦Λ⟧).obj
              ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) =
      (detSfCompactSupportBaseChangeComposite Λ f v c oc).app K ≫
        compactificationRefinementComponent Λ hc
          ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) := by
  exact open_chase R((pullback.snd c.g v)_*⟦Λ⟧)
    (exchange_component_eq Λ f v c oc K)
    (refinement_baseChange_component_eq Λ v hc
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))
    (compactSupportOpenRefinement_pasting Λ f v c d oc od hoc hod h w hd hc esr K)

private theorem refinement_pullback_eq
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c : Compactification f) (d : Compactification.DenseBoundaryCompactification f)
    (h : d.obj ⟶ detSfBoundaryCompactification c)
    (w : Compactification.DenseBoundaryCompactification (pullback.snd f v))
    (hd : w.obj ⟶ detSfBoundaryCompactification (d.obj.obj.obj.baseChange v))
    (hc : w.obj ⟶ detSfBoundaryCompactification (c.baseChange v)) :
    hd.hom.hom.hom ≫ compactSupportTrianglePullback h.hom.hom.hom c.g
      d.obj.obj.obj.g h.hom.hom.hom_g v = hc.hom.hom.hom := by
  apply (denseCompactification_refinement_morphisms w.obj.obj
    (detSfBoundaryCompactification (c.baseChange v)).obj w.property hc.hom.hom.hom
    hc.hom.hom.hom_g hc.hom.hom.i_hom).2.2
  · change (hd.hom.hom.hom ≫ _) ≫ pullback.snd c.g v = w.obj.obj.obj.g
    simpa [Category.assoc, compactSupportTrianglePullback,
      detSfBoundaryCompactification] using hd.hom.hom.hom_g
  · rw [← Category.assoc, hd.hom.hom.i_hom]
    change (d.obj.obj.obj.baseChange v).i ≫ _ = (c.baseChange v).i
    apply pullback.hom_ext
    · simp [compactSupportTrianglePullback, Category.assoc,
        h.hom.hom.i_hom, detSfBoundaryCompactification]
    · simp [compactSupportTrianglePullback, Category.assoc]

/-- The local refinement-pasting equation for the specified exchange composite.
This statement involves one refinement and one dense refinement after pullback; it
neither chooses compactification comparisons nor asserts that exchange is invertible.

Source: blueprint det-sf-comp-composition-base-change, proof (3), the equation obtained
by applying proper pushforward to the identity-on-open comparison.
(blueprint: lem-sfb-compact-support-refinement-base-change).

Proof: the two composite refinements from the dense source `w` to `c.baseChange v`
agree, since they agree on the distinguished open and the target is separated over
Y'. Transport the proper compositors to the canonical derived adjunction compositors
using the K-injective normalization. On the open square, the unit, square comparison
and counit defining `detSfOpenBaseChangeMap` restrict to identity. The same holds for
the normalized localizing refinement maps. The precise proper base-change mate for
`h` restricts to identity on the open, by baseChangeIdentityOpenRestriction. Transpose
the two maps from the base-changed open extension to the proper image from `w`
under its open adjunction. Their adjuncts are equal by these identity restrictions,
so injectivity of the adjunction Hom equivalence equates the original maps. Apply
the proper pushforward for c and precompose with its proper base-change mate.
Naturality moves the refinement arrow across that mate. Horizontal mate pasting
replaces the two proper mates by the mate for d. The normalized compositor cancels
with the inverse compositor in compactificationRefinementComponent. The resulting
component equation is precisely the displayed formula. No base-changed open is
assumed dense: density is required only for the chosen further source w. The proof
uses no invertibility of a proper mate or of a refinement map and applies to every
unbounded K, including zero objects and empty distinguished opens. -/
theorem compactSupportRefinement_baseChange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (o : ∀ c : Compactification f,
      D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
        detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧))
    (ho : ∀ c, (o c).inv = detSfOpenBaseChangeMap Λ f v c)
    (c : Compactification f) (d : Compactification.DenseBoundaryCompactification f)
    (h : d.obj ⟶ detSfBoundaryCompactification c)
    (w : Compactification.DenseBoundaryCompactification (pullback.snd f v))
    (hd : w.obj ⟶ detSfBoundaryCompactification (d.obj.obj.obj.baseChange v))
    (hc : w.obj ⟶ detSfBoundaryCompactification (c.baseChange v))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (detSfDerivedPullback Λ v).map (compactificationRefinementComponent Λ h K) ≫
        (detSfCompactSupportBaseChangeComposite Λ f v d.obj.obj.obj
          (o d.obj.obj.obj)).app K ≫
        compactificationRefinementComponent Λ hd
          ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) =
      (detSfCompactSupportBaseChangeComposite Λ f v c (o c)).app K ≫
        compactificationRefinementComponent Λ hc
          ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) := by
  have esr := refinement_pullback_eq f v c d h w hd hc
  exact (proper_stage Λ f v c d.obj h w.obj hd hc esr (o d.obj.obj.obj) K).trans
    (open_stage Λ f v c d.obj h w.obj hd hc esr (o d.obj.obj.obj) K (o c)
      (ho c) (ho d.obj.obj.obj))

end AlgebraicGeometry.ProEtale.CondensedRing
