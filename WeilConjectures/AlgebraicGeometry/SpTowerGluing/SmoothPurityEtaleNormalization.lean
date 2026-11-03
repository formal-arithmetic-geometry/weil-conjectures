/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Normalization of the etale tower comparisons

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
Local pairs and Levels (blueprint: def-sp-tower-gluing-interfaces).

The graph coordinates and graph-normalization predicate are shared by the local
coordinate construction and global gluing. Refinement compatibility is a separate
tower equation for the supplied calculus, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

attribute [instance] GraphCoordinates.additive GraphCoordinates.inverseAdditive

end AlgebraicGeometry.ProEtale.SpTowerGluing

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

/-- The actual lifted quotient rings for the graph construction, with index n meaning n+1.
Source: Local pairs, coefficient convention (blueprint: det-sp-tower-gluing). -/
def graphRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))

/-- The adjacent quotient maps, lifted without changing coefficients.
Source: Local pairs, coefficient convention (blueprint: det-sp-tower-gluing). -/
def graphTransitions (n : ℕ) : graphRings l E (n + 1) ⟶ graphRings l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
      ULift.ringEquiv.toRingHom))

/-- Section-preserving ordinary presentations and direct-image comparisons for the
existing graph model. Units and counits are pinned as functions on sections.
The push square agrees levelwise with the given ordinaryPushEvaluation isomorphism,
allowing arbitrary carrier presentations without an independent scalar twist.
Source: Local pairs, section-model and graph construction (blueprint: det-sp-tower-gluing). -/
structure GraphCoordinates where
  presentation : ∀ T : Scheme.{u}, SpTowerShriek.S l E T ≌
    SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) T
  [additive : ∀ T : Scheme.{u}, (presentation T).functor.Additive]
  [inverseAdditive : ∀ T : Scheme.{u}, (presentation T).inverse.Additive]
  sections : ∀ (T : Scheme.{u}) (M : SpTowerShriek.S l E T) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (((presentation T).functor.obj M).val.obj V) (M.val.obj V)
  restrictions : ∀ (T : Scheme.{u}) (M : SpTowerShriek.S l E T)
    {V W : (ℕ × T.ProEt)ᵒᵖ} (a : V ⟶ W),
    HEq (((presentation T).functor.obj M).val.map a) (M.val.map a)
  morphisms : ∀ (T : Scheme.{u}) {M N : SpTowerShriek.S l E T} (a : M ⟶ N)
    (V : (ℕ × T.ProEt)ᵒᵖ), HEq (((presentation T).functor.map a).val.app V) (a.val.app V)
  unit_sections : ∀ (T : Scheme.{u}) (M : SpTowerShriek.S l E T)
    (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((presentation T).unitIso.hom.app M).val.app V x)
      (fun x : M.val.obj V ↦ x)
  counit_sections : ∀ (T : Scheme.{u})
    (M : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) T)
    (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((presentation T).counitIso.hom.app M).val.app V x)
      (fun x : M.val.obj V ↦ x)
  push : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (presentation X).inverse ⋙ (o.geometry f).push ⋙ (presentation Y).functor ≅
      SemilinearProperOpen.push (graphRings l E) (graphTransitions l E) f
  /-- Compatibility with the supplied ordinary evaluation iso, on all component sections.
  Both sides are functions; no equality with the input section's carrier is required. -/
  push_evaluation : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) X)
    (n : ℕ) (V : Y.ProEtᵒᵖ),
    HEq (fun x ↦ ((push f).hom.app M).val.app (op (n, V.unop)) x)
      (fun x ↦ (((o.geometry f).ordinaryPushEvaluation n).hom.app
        ((presentation X).inverse.obj M)).val.app V x)

/-- Remove an ordinary conjugation using only the presentation's fixed unit.
Source: Local pairs, canonical coordinate transport (blueprint: det-sp-tower-gluing). -/
def graphForward (g : GraphCoordinates l E b o) {X Y : Scheme.{u}}
    (F : SpTowerShriek.S l E X ⥤ SpTowerShriek.S l E Y)
    (G : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) X ⥤
      SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) Y)
    (a : (g.presentation X).inverse ⋙ F ⋙ (g.presentation Y).functor ≅ G) :
    F ⋙ (g.presentation Y).functor ≅ (g.presentation X).functor ⋙ G :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (g.presentation X).unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ a

/-- Pullback comparison uniquely preserving the section-normalized geometric adjunction.
Source: Local pairs, canonical coordinate transport (blueprint: det-sp-tower-gluing). -/
def graphPullCoordinates (g : GraphCoordinates l E b o) {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (g.presentation Y).inverse ⋙ (o.geometry f).pull ⋙ (g.presentation X).functor ≅
      SemilinearProperOpen.pull (graphRings l E) (graphTransitions l E) f :=
  ((((g.presentation Y).symm.toAdjunction.comp (o.geometry f).ordinaryAdjunction).comp
    (g.presentation X).toAdjunction).ofNatIsoRight (g.push f)).leftAdjointUniq
      (SemilinearProperOpen.ordinaryAdj (graphRings l E) (graphTransitions l E) f)

/-- Open extension comparison obtained from the specified ordinary adjunctions.
Source: Local pairs, canonical coordinate transport (blueprint: det-sp-tower-gluing). -/
def graphOpenCoordinates (g : GraphCoordinates l E b o) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    (g.presentation U).inverse ⋙ (o.openOp j).extension ⋙ (g.presentation T).functor ≅
      SemilinearProperOpen.extension (graphRings l E) (graphTransitions l E) j :=
  ((((g.presentation U).symm.toAdjunction.comp (o.openOp j).ordinaryAdjunction).comp
    (g.presentation T).toAdjunction).ofNatIsoRight
      (graphPullCoordinates l E b o g j)).leftAdjointUniq
        (SemilinearProperOpen.ordinaryOpenAdj (graphRings l E) (graphTransitions l E) j)

/-- Etale sum comparison preserving the actual summand adjunction and its counit.
Source: Local pairs, canonical coordinate transport (blueprint: det-sp-tower-gluing). -/
def graphSumCoordinates (g : GraphCoordinates l E b o)
    (z : SpTowerCalculus.FiniteCoordinates l E) {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] (a : SpTowerCalculus.EtaleOperation l E b o z e) :
    (g.presentation U).inverse ⋙ a.extension ⋙ (g.presentation T).functor ≅
      VaryingRingGraph.sum (graphRings l E) (graphTransitions l E) e :=
  ((((g.presentation U).symm.toAdjunction.comp a.ordinaryAdjunction).comp
    (g.presentation T).toAdjunction).ofNatIsoRight
      (graphPullCoordinates l E b o g e)).leftAdjointUniq
        (VaryingRingGraph.geometricSumAdjunction (graphRings l E) (graphTransitions l E) e)

/-- The exact ordinary sum square descended termwise to all unbounded complexes.
Source: Local pairs, canonical coordinate transport (blueprint: det-sp-tower-gluing). -/
def graphDerivedSum (g : GraphCoordinates l E b o)
    (z : SpTowerCalculus.FiniteCoordinates l E) {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] (a : SpTowerCalculus.EtaleOperation l E b o z e) :
    a.extension.mapDerivedCategory ⋙ (g.presentation T).functor.mapDerivedCategory ≅
      (g.presentation U).functor.mapDerivedCategory ⋙
        (VaryingRingGraph.sum (graphRings l E) (graphTransitions l E) e).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (graphForward l E b o g _ _ (graphSumCoordinates l E b o g z e a)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Derived proper/open transport uses the ordinary section square and the canonical
right-derived composition maps. No arbitrary derived comparison is selected.
Source: Local pairs, graph comparison (blueprint: det-sp-tower-gluing). -/
def graphSupportCoordinates (g : GraphCoordinates l E b o)
    {U T : Scheme.{u}} {e : U ⟶ T} (c : Compactification e) :
    SpTowerShriek.F l E b o c ⋙ (g.presentation T).functor.mapDerivedCategory ≅
      (g.presentation U).functor.mapDerivedCategory ⋙
        SemilinearProperOpen.J (graphRings l E) (graphTransitions l E) c.i ⋙
        SemilinearProperOpen.R (graphRings l E) (graphTransitions l E) c.g :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
      Functor.rightDerivedFunctorNatIso (graphForward l E b o g _ _ (g.push c.g)) ≪≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (graphForward l E b o g _ _ (graphOpenCoordinates l E b o g c.i)) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _

/-- Graph normalization of the GIVEN etale calculus for every etale chart.
The inverse compact-support comparison is the existing graph transformation, uniquely
specified on all homotopy representatives by degreewise graph extension followed by the
total-derived unit. Coordinate transport uses only section-normalized ordinary maps and
adjunction-unique comparisons. It excludes an independent non-open sign change.
Source: Local pairs, etale fibre summation (blueprint: det-sp-tower-gluing). -/
def EtaleNormalized (k : Type u) [Field k]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (et : SpTowerCalculus.EtaleCalculus l E k b o q z) : Prop :=
  ∃ g : GraphCoordinates l E b o,
  ∀ {U T : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (e : U ⟶ T) [e.IsOver (Spec (.of k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (c : Compactification e) (K : SpTowerCalculus.C l E b q U),
    (g.presentation T).functor.mapDerivedCategory.map
        ((SpTowerCalculus.realization l E b T (q.abelian T)).functor.map
          ((et.etale_shriek e c).inv.app K) ≫
        (SpTowerCalculus.realization l E b T (q.abelian T)).counitIso.hom.app
          ((SpTowerShriek.F l E b o c).obj
            ((SpTowerCalculus.realization l E b U (q.abelian U)).functor.obj K.obj))) ≫
      (graphSupportCoordinates l E b o g c).hom.app
        ((SpTowerCalculus.realization l E b U (q.abelian U)).functor.obj K.obj) =
    (g.presentation T).functor.mapDerivedCategory.map
        ((SpTowerCalculus.realization l E b T (q.abelian T)).counitIso.hom.app
          ((et.etale e).extension.mapDerivedCategory.obj
            ((SpTowerCalculus.realization l E b U (q.abelian U)).functor.obj K.obj))) ≫
      (graphDerivedSum l E b o g z e (et.etale e)).hom.app
        ((SpTowerCalculus.realization l E b U (q.abelian U)).functor.obj K.obj) ≫
      (VaryingRingGraph.theta (graphRings l E) (graphTransitions l E) e c).app
        ((g.presentation U).functor.mapDerivedCategory.obj
          ((SpTowerCalculus.realization l E b U (q.abelian U)).functor.obj K.obj))

/-- Compatibility of the supplied etale comparison with the supplied tower
refinement. Graph normalization of each comparison alone does not imply this law
for independently supplied refinement maps. The canonical producer must establish
it from the same graph and proper/open mate construction.
Source: Local pairs, independence of intermediate compactifications
(blueprint: def-sp-tower-gluing-interfaces). -/
def EtaleRefinementCompatible (k : Type u) [Field k]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) : Prop :=
  ∀ {U T : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (e : U ⟶ T) [e.IsOver (Spec (.of k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (c d : Compactification e) (K : SpTowerCalculus.C l E b q U),
    (cal.composition.refinement e c d).hom.app K ≫
        (cal.etale.etale_shriek e d).hom.app K =
      (cal.etale.etale_shriek e c).hom.app K

end AlgebraicGeometry.ProEtale.SpTowerGluing
