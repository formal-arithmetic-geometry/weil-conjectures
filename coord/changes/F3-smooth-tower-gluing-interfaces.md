# AlgebraicGeometry.ProEtale.SpTowerGluing shared interfaces

## Reason

The geometric chart-adjunction assembly and its finite evaluation/reduction assembly
must mention the existing Charts, Levels and their shared definitions. Keeping these
definitions in the module which imports the new lemmas would create an import cycle.
Move the existing interface block, byte-identical, to
Sheaf.Paper.SmoothPurityTowerGluingData and publicly import it at the original module.
This is an interface extraction for two mathematical proof steps, not a split to
avoid the compiler limit. No target statement, universe, field, attribute, definition
body, or normalization changes. No definition chooses data from a new theorem.
The theorem tower_gluing keeps its exact source signature and is reduced to two
strict parts of its argument, with preservation and categorical uniqueness proved.

All original public imports are retained in the data module and re-exported at the
original module. The original private imports for coordinate-cover and binary-fibre
proofs are not needed by the interface; these remain mathematical dependencies of
the global-chart assembly and are not pruned from its DAG.

## Old

In Sheaf.Paper.SmoothPurityTowerGluing, the shared block was:

```lean
/-- Exact evaluation restricted to the recorded full finite-level category.
Source: clause (3), finite levels (blueprint: det-sp-tower-gluing). -/
def level (T : Scheme.{u}) (n : ℕ) :
    SpTowerCalculus.C l E b q T ⥤ spFiniteConstructibleTorCategory T (SpTowerShriek.R l E n) :=
  ObjectProperty.lift _
    (SpTowerCalculus.inclusion l E b q T ⋙
      spDerivedCoefficientEvaluation l E T (q.abelian T) n)
    (fun K ↦ K.property.1 n)

/-- The genuine full-subcategory restriction of the specified compactification functor.
Source: the representing functor (blueprint: det-sp-tower-gluing). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj)) :
    SpTowerCalculus.C l E b q X ⥤ SpTowerCalculus.C l E b q Y :=
  ObjectProperty.lift _
    (SpTowerCalculus.inclusion l E b q X ⋙ SpTowerCalculus.F l E b o q c) hF

/-- The finite coefficient comparison is its specified counit transpose, not an arbitrary
map between exceptional inverse images. This is c_(n,m) of det-sp-reduction-exceptional.
Source: clause (3), reduction comparison (blueprint: det-sp-tower-gluing). -/
def coefficientMate {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (m n : ℕ) (h : m ≤ n)
    (hFn : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n),
      spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
        ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj M.obj))
    (hFm : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E m),
      spFiniteConstructibleTor Y (SpTowerShriek.R l E m)
        ((reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n),
      spFiniteConstructibleTor X (SpTowerShriek.R l E m)
        ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n),
      spFiniteConstructibleTor Y (SpTowerShriek.R l E m)
        ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).obj K.obj))
    (Gn : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n) ⥤
      spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n))
    (Gm : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E m) ⥤
      spFiniteConstructibleTorCategory X (SpTowerShriek.R l E m))
    (an : reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g hFn ⊣ Gn)
    (am : reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g hFm ⊣ Gm)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n))
    (hb : IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
      (Gn.obj K).obj)) :
    (reductionCtfScalar (SpTowerCalculus.quotient l E h) X hSX).obj (Gn.obj K) ⟶
      Gm.obj ((reductionCtfScalar (SpTowerCalculus.quotient l E h) Y hSY).obj K) :=
  am.homEquiv _ _ (ObjectProperty.homMk
    (@inv _ _ _ _
      ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
        (Gn.obj K).obj) hb ≫
      (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).map
        (an.counit.app K).hom))

set_option maxHeartbeats 800000 in
-- Elaborating the dependent counit-mate reduction equation unfolds several derived functors.
/-- Finite adjunctions and their natural comparison to the tower right adjoint, with both
adjunction normalizations and the actual coefficient-mate reduction equation.
Source: clause (3), all finite levels and reductions (blueprint: det-sp-tower-gluing). -/
structure Levels {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : support l E b o q c hF ⊣ G) where
  finite_closed : ∀ (n : ℕ) (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
      ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj M.obj)
  right : ∀ n : ℕ, spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n) ⥤
    spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)
  adjunction : ∀ n : ℕ,
    reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (finite_closed n) ⊣ right n
  realization : ∀ n : ℕ,
    ReductionExceptionalRealization (SpTowerShriek.R l E n) c.i c.g
      (finite_closed n) (right n) (adjunction n)
  support_evaluation : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q c n
  comparison : ∀ n : ℕ, G ⋙ level l E b q X n ≅ level l E b q Y n ⋙ right n
  counit : ∀ (n : ℕ) (K : SpTowerCalculus.C l E b q Y),
    (support_evaluation n).comparison.inv.app (G.obj K).obj ≫
        (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map (adj.counit.app K).hom =
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map
        ((comparison n).hom.app K).hom ≫
      ((adjunction n).counit.app ((level l E b q Y n).obj K)).hom
  unit : ∀ (n : ℕ) (M : SpTowerCalculus.C l E b q X),
    (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map (adj.unit.app M).hom ≫
        ((comparison n).hom.app ((support l E b o q c hF).obj M)).hom ≫
        ((right n).map (ObjectProperty.homMk
          ((support_evaluation n).comparison.hom.app M.obj))).hom =
      ((adjunction n).unit.app ((level l E b q X n).obj M)).hom
  scalarX : ∀ (m n : ℕ) (h : m ≤ n)
    (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor X (SpTowerShriek.R l E m)
      ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).obj M.obj)
  scalarY : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor Y (SpTowerShriek.R l E m)
      ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).obj K.obj)
  direct_image_iso : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
      ((right n).obj K).obj)
  coefficient_iso : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    IsIso (coefficientMate l E b c m n h (finite_closed n) (finite_closed m)
      (scalarX m n h) (scalarY m n h) (right n) (right m) (adjunction n) (adjunction m)
      K (direct_image_iso m n h K))
  reduction : ∀ (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
        ((comparison n).hom.app K).hom ≫
      (coefficientMate l E b c m n h (finite_closed n) (finite_closed m)
        (scalarX m n h) (scalarY m n h) (right n) (right m) (adjunction n) (adjunction m)
        ((level l E b q Y n).obj K)
        (direct_image_iso m n h ((level l E b q Y n).obj K))).hom ≫
      ((right m).map (ObjectProperty.homMk
        (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj))).hom =
    SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj ≫
      ((comparison m).hom.app K).hom

/-- The canonical open restriction counit in the strict tower coordinates.
Source: clause (1), restriction of representing pairs (blueprint: det-sp-tower-gluing). -/
def openAdjunction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    SpTowerCalculus.openExtension l E b o q j ⊣ SpTowerCalculus.etalePullback l E b o q j :=
  ((SpTowerCalculus.realization l E b U (q.abelian U)).toAdjunction.comp
    (o.openOp j).derivedAdjunction).comp
    (SpTowerCalculus.realization l E b T (q.abelian T)).symm.toAdjunction

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

attribute [instance] GraphCoordinates.additive GraphCoordinates.inverseAdditive

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

open SpCoordinateAdjunction in
/-- The full normalized coordinate specification at a GIVEN chart family.
This is the predicate Construction with its chart existential made an explicit
parameter. All prefix witnesses, their normalization equations, and every suffix
compatibility equation are retained literally. In particular its last equation
mentions this parameter's counit, and can be recovered by ordinary Exists elimination.
No relation is indexed by a proposition, so propext cannot replace the chart family.
Source: Local pairs and Levels, normalized coordinate construction
(blueprint: det-sp-tower-gluing). -/
def ConstructionAt (k : Type u) [Field k]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E)
    (chart : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
      (_over : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
      [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification (e ≫ proj Y.val.left d)),
      ChartPair l E b o q e (proj Y.val.left d) c (w U.val.left) d) : Prop :=
  /- All finite-type bases admit the dependency's normalized P1 presentation. -/
  ∃ (projective : ∀ Y : Bases k, ProjectivePresentation l E b o Y.val.left),
  /- The finite line is the root-projection normalized Kummer line. -/
  ∃ (roots : ∀ Y : Bases k, RootLines l E Y.val.left),
  /- Shift comparisons use the signed total-complex convention. -/
  ∃ (shifts : ∀ Y : Bases k, TensorShifts l E b Y.val.left),
  /- Multiplication is specified on local tensors and K-flat representatives. -/
  ∃ (products : ∀ Y : Bases k, Products l E b (w Y.val.left)),
  /- The Tate factors are pulled back before being multiplied. -/
  ∃ (pulled : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d) (r : ℕ),
    PullTwist l E b o e (proj Y.val.left d) (w (space Y.val.left d)) (w U.val.left) r),
  /- The degree-zero line comparison sends each coefficient section to its pullback. -/
  ∃ (_pulled_zero : ∀ (Y U : Bases k) (d n : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E (space Y.val.left d) n).obj.obj V),
    pullSection l E (pulled Y U d e 0) n V a =
      (Scheme.proEtaleConstantDirectImageMap.{u, u + 2} e CommRingCat.{u + 1}
        (CommRingCat.of (SpTowerClasses.FiniteRing l E n))).hom.app V a),
  /- The positive generator is pulled back by restriction of the actual finite root. -/
  ∃ (_pulled_one : ∀ (Y U : Bases k) (d n : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E (space Y.val.left d) n).obj.obj V)
    (z : (Scheme.proEtaleRootsOfUnitySheaf (space Y.val.left d) (l ^ (n + 1))).obj.obj V),
    ((roots U).iso n).hom.val.app (SpTowerClasses.chart e V)
      (pullSection l E (pulled Y U d e 1) n V
        (((roots (coordinateBase Y d)).iso n).inv.val.app V
          (Scheme.tateFiniteTensor (space Y.val.left d) l (SpTowerClasses.FiniteRing l E n) n
            (SpTowerClasses.finiteScalar l E n) V.unop a z))) =
      Scheme.tateFiniteTensor U.val.left l (SpTowerClasses.FiniteRing l E n) n
        (SpTowerClasses.finiteScalar l E n) (SpTowerClasses.chart e V).unop
        ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} e CommRingCat.{u + 1}
          (CommRingCat.of (SpTowerClasses.FiniteRing l E n))).hom.app V a)
        (SpTowerClasses.restrictRoot l e n V z)),
  /- Higher positive powers are the same ordinary tensor pullback on local tensors. -/
  ∃ (_pulled_product : ∀ (Y U : Bases k) (d n r : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (x : (spEllTwistLine l E (space Y.val.left d) n (r + 1 : ℕ)).val.obj V)
    (y : (spEllTwistOne l E (space Y.val.left d) n).val.obj V),
    pullSection l E (pulled Y U d e (r + 2)) n V
      (SheafOfModules.siteSheafTensorTmul
        (spEllTwistLine l E (space Y.val.left d) n (r + 1 : ℕ))
        (spEllTwistOne l E (space Y.val.left d) n) V x y) =
      SheafOfModules.siteSheafTensorTmul
        (spEllTwistLine l E U.val.left n (r + 1 : ℕ)) (spEllTwistOne l E U.val.left n)
        (SpTowerClasses.chart e V)
        (pullSection l E (pulled Y U d e (r + 1)) n V x)
        (pullSection l E (pulled Y U d e 1) n V y)),
  /- Root-normalized restriction of the projective right factor. -/
  ∃ (affine : ∀ Y : Bases k, AffineRestriction l E (projective Y)
    (w (space Y.val.left 1)) (roots (coordinateBase Y 1)) (shifts (coordinateBase Y 1))),
  /- Extension by zero has the etale-origin bounded-below domain needed by P1. -/
  ∃ (affine_source : ∀ (Y : Bases k) (M : (P l E b q (space Y.val.left 1)).FullSubcategory),
    SpTowerP1.domain l E (projective Y).presentation.classes.base (ProjectiveLine Y.val.left)
      ((SpTowerShriek.openD l E b (o.openOp (ProjectiveLine.affineChart Y.val.left))).obj
        ((SpTowerCalculus.realization l E b (space Y.val.left 1)
          (q.abelian (space Y.val.left 1))).functor.obj M.obj))),
  /- The input on the base has the same domain. -/
  ∃ (affine_target : ∀ (Y : Bases k) (K : (P l E b q Y.val.left).FullSubcategory),
    SpTowerP1.domain l E (projective Y).presentation.classes.base Y.val.left
      ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)),
  /- Separate level origins and bounded-below domains, without normalization. -/
  ∃ (_domains : ∀ (Y : Bases k) (K : (P l E b q Y.val.left).FullSubcategory),
    SpChartAdmissibility.domain l E b Y.val.left
      ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)),
  /- Projection adjunction for every coefficient-independent compactification. -/
  ∃ (projection : ∀ (Y : Bases k) (d : ℕ) (c : Compactification (proj Y.val.left d)),
    ProjectionPair l E b o q (proj Y.val.left d) c (w (space Y.val.left d)) d),
  /- Ordered tensor/shift identification, constructed on actual strict towers. -/
  ∃ (iteration : ∀ (Y : Bases k) (d : ℕ),
    orderedRight l E b o w Y.val.left d ≅
      projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d),
  /- The successor comparison is the explicit pull/tensor/shift component. -/
  ∃ (step : ∀ (Y : Bases k) (d : ℕ),
    projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d ⋙
      projectionRight l E b o
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1 ≅
      projectionRight l E b o (proj Y.val.left (d + 1))
        (w (space Y.val.left (d + 1))) (d + 1)),
  ∃ (_step_normalized : ∀ (Y : Bases k) (d : ℕ) (K : SpTowerShriek.D l E Y.val.left),
    (step Y d).app K = stepComponent l E b o w Y.val.left d
      (pulled Y (coordinateBase Y (d + 1)) d
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d) d)
      (products (coordinateBase Y (d + 1))) (shifts (coordinateBase Y (d + 1))) K),
  ∃ (_iteration_successor : ∀ (Y : Bases k) (d : ℕ),
    iteration Y (d + 1) =
      Functor.isoWhiskerRight (iteration Y d)
        (projectionRight l E b o
          (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
          (w (space Y.val.left (d + 1))) 1) ≪≫ step Y d),
  /- The affine Hom map is the P1 Hom map followed by the actual open adjunction. -/
  ∃ (_affine_hom : ∀ (Y : Bases k)
    (M : (P l E b q (space Y.val.left 1)).FullSubcategory)
    (K : (P l E b q Y.val.left).FullSubcategory)
    (f : (SpTowerCalculus.F l E b o q (affineTraceLineCompactification Y.val.left)).obj
      M.obj ⟶ K.obj),
    realizedTranspose l E b q
      (projectionRight l E b o (proj Y.val.left 1) (w (space Y.val.left 1)) 1)
      M.obj K.obj ((projection Y 1 (affineTraceLineCompactification Y.val.left)).homEquiv
        M K f) =
      openHom l E b o Y.val.left
        ((SpTowerCalculus.realization l E b (space Y.val.left 1)
          (q.abelian (space Y.val.left 1))).functor.obj M.obj)
        (((projective Y).presentation.G l E).obj
          ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
            K.obj))
        (projectiveHom l E (projective Y)
          ⟨_, affine_source Y M⟩ ⟨_, affine_target Y K⟩
          ((projectivePush l E (projective Y)).hom.app _ ≫
            (supportRealization l E b o q (affineTraceLineCompactification Y.val.left)).inv.app
              M.obj ≫
            (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.map f)) ≫
      (affine Y).comparison.hom.app
        ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)),
  /- Every ordered projection is the composite of the preceding projection and line. -/
  ∃ (_projection_successor : ∀ (Y : Bases k) (d : ℕ)
    (cl : Compactification
      (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d))
    (cp : Compactification (proj Y.val.left d))
    (cc : Compactification (proj Y.val.left (d + 1))),
    CompositeEquation (P l E b q (space Y.val.left (d + 1)))
      (P l E b q (space Y.val.left d)) (P l E b q Y.val.left)
      _ _ _ _ _ _
      (projection (coordinateBase Y d) 1 cl) (projection Y d cp)
      (projection Y (d + 1) cc)
      (cal.composition.composition
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (proj Y.val.left d) (proj Y.val.left (d + 1)) rfl cl cp cc)
      (composeRight l E b q _ _ _ (step Y d))),
  /- The identity factor is fixed before deriving, including the coefficient unit. -/
  ∃ (zeroComparison : ∀ Y : Bases k, ZeroComparison l E b o Y.val.left (w Y.val.left)),
  ∃ (_iteration_zero : ∀ (Y : Bases k) (K : SpTowerShriek.D l E Y.val.left),
    (iteration Y 0).app K = ((zeroComparison Y).component l E K).symm),
  /- The zero-coordinate identification transports the identity adjunction. -/
  ∃ (_zero : ∀ (Y : Bases k) (c : Compactification (𝟙 Y.val.left))
    (M : (P l E b q Y.val.left).FullSubcategory)
    (K : (P l E b q Y.val.left).FullSubcategory)
    (f : (SpTowerCalculus.F l E b o q c).obj M.obj ⟶ K.obj),
    (projection Y 0 c).homEquiv M K f ≫
      (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).inverse.map
        ((iteration Y 0).inv.app
          ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
            K.obj)) ≫
      (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).unitIso.inv.app
        K.obj = (cal.composition.identity c).inv.app M ≫ f),
  /- Finite projection adjunction and evaluation of all units, counits and Hom maps. -/
  ∃ (projection_levels : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ),
    LevelCompatibility l E b q (projection Y d c) n (SpTowerShriek.finiteF l E b c n)
      (finiteProjectionRight l E b (proj Y.val.left d) (w (space Y.val.left d)) d n)),
  /- The finite chart adjunction is asserted for every finite object. -/
  ∃ (chart_levels : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ),
    LevelCompatibility l E b q (chart Y U d e hOver c) n
      (SpTowerShriek.finiteF l E b c n)
      (finiteChartRight l E b e (proj Y.val.left d) (w U.val.left) d n)),
  /- The finite left coordinate change is the specified compactification evaluation. -/
  ∃ (_projection_left_normalization : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ),
    (projection_levels Y d c n).left = supportEvaluation l E b o q c n),
  /- The same fixed evaluation for the chart's compact support. -/
  ∃ (_chart_left_normalization : ∀ (Y U : Bases k) (d : ℕ)
    (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ),
    (chart_levels Y U d e hOver c n).left = supportEvaluation l E b o q c n),
  /- Right evaluation has the canonical section/shift/tensor normalization. -/
  ∃ (_projection_right_normalization : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ)
    (K : spDerivedCoefficientTowers l E Y.val.left (q.abelian Y.val.left)),
    (projection_levels Y d c n).right.hom.app K =
      projectionEvaluation l E b o q (proj Y.val.left d) (w (space Y.val.left d)) d n K),
  /- The chart uses the same fixed evaluation for both pullbacks. -/
  ∃ (_chart_right_normalization : ∀ (Y U : Bases k) (d : ℕ)
    (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ)
    (K : spDerivedCoefficientTowers l E Y.val.left (q.abelian Y.val.left)),
    (chart_levels Y U d e hOver c n).right.hom.app K =
      rightEvaluation l E b o q e (proj Y.val.left d) (w U.val.left) d n K),
  /- The chart counit is the counit of the etale pair followed by integration,
  transported by the calculus composition and the preceding right comparison. -/
  ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    [e.IsOver (Spec (.of k))] [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    (ce : Compactification e) (cp : Compactification (proj Y.val.left d))
    (ch : Compactification (e ≫ proj Y.val.left d))
    (K : (P l E b q Y.val.left).FullSubcategory),
    (chart Y U d e hOver ch).counit K =
      (SpTowerCalculus.F l E b o q ch).map
        ((composeRight l E b q _ _ _ (pulled Y U d e d).comparison).inv.app K.obj) ≫
      (cal.composition.composition e (proj Y.val.left d)
        (e ≫ proj Y.val.left d) rfl ce cp ch).inv.app
          ⟨(SpTowerCalculus.etalePullback l E b o q e).obj
              ((originalProjectionRight l E b o q (proj Y.val.left d)
                (w (space Y.val.left d)) d).obj K.obj),
            (etalePair l E k b o q z h cal U (coordinateBase Y d) e).right_closed
              ⟨_, (projection Y d cp).right_closed K⟩⟩ ≫
      (SpTowerCalculus.F l E b o q cp).map
        ((cal.etale.etale_shriek e ce).hom.app
          ⟨(SpTowerCalculus.etalePullback l E b o q e).obj
              ((originalProjectionRight l E b o q (proj Y.val.left d)
                (w (space Y.val.left d)) d).obj K.obj),
            (etalePair l E k b o q z h cal U (coordinateBase Y d) e).right_closed
              ⟨_, (projection Y d cp).right_closed K⟩⟩ ≫
          (etalePair l E k b o q z h cal U (coordinateBase Y d) e).counit
            ⟨_, (projection Y d cp).right_closed K⟩) ≫
      (projection Y d cp).counit K

/-- Bundle a source open with its inherited ground-field structure. The properties are
supplied as conclusions of the chart statement, not as additional hypotheses.
Source: standing finite-type setting (blueprint: det-sp-tower-gluing). -/
def openBase {k : Type u} [Field k] (X : Over (Spec (.of k))) (U : X.left.Opens)
    (h : IsSeparated (U.ι ≫ X.hom) ∧ LocallyOfFiniteType (U.ι ≫ X.hom) ∧
      QuasiCompact (U.ι ≫ X.hom)) : SpCoordinateAdjunction.Bases k :=
  ⟨Over.mk (U.ι ≫ X.hom), h⟩

/-- Counit-normalized charts from the existing explicit coordinate construction.
`normalized` is a predicate at the actual chart family, including its P1/open Hom
formula, zero identity, successor composites, and final etale-sum counit formula.
Only the canonical compactification copy changes the index of the local pair.
Source: clause (1), all coordinate charts (blueprint: det-sp-tower-gluing). -/
structure Charts (k : Type u) [Field k]
    (X Y : Over (Spec (.of k)))
    (hY : IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom)
    (f : X ⟶ Y) (d : ℕ) (c : Compactification f.left)
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
    (adj : support l E b o q c hF ⊣ G) where
  finiteCoordinates : SpTowerCalculus.FiniteCoordinates l E
  preservation : SpTowerCalculus.Preservation l E k b o q
  calculus : SpTowerCalculus.Calculus l E k b o q finiteCoordinates preservation
  etale_normalized : EtaleNormalized l E b o q k finiteCoordinates calculus.etale
  twists : SpCoordinateAdjunction.TwistFamily l E
  chart : ∀ (B U : SpCoordinateAdjunction.Bases k) (r : ℕ)
    (e : U.val.left ⟶ affineTraceTower B.val.left r)
    (_over : e ≫ affineTraceProjection B.val.left r ≫ B.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (cc : Compactification (e ≫ affineTraceProjection B.val.left r)),
    SpCoordinateAdjunction.ChartPair l E b o q e (affineTraceProjection B.val.left r)
      cc (twists U.val.left) r
  normalized : ConstructionAt l E b o q k finiteCoordinates preservation calculus twists chart
  open_properties : ∀ U : X.left.Opens,
    IsSeparated (U.ι ≫ X.hom) ∧ LocallyOfFiniteType (U.ι ≫ X.hom) ∧
      QuasiCompact (U.ι ≫ X.hom)
  comparison : ∀ (K : SpTowerCalculus.C l E b q Y.left) (U : X.left.Opens)
    (e : U.toScheme ⟶ affineTraceTower Y.left d) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (_he : U.ι ≫ f.left = e ≫ affineTraceProjection Y.left d),
    (SpTowerCalculus.etalePullback l E b o q U.ι).obj (G.obj K).obj ≅
      (SpCoordinateAdjunction.originalChartRight l E b o q e
        (affineTraceProjection Y.left d) (twists U.toScheme) d).obj K.obj
  counit : ∀ (K : SpTowerCalculus.C l E b q Y.left) (U : X.left.Opens)
    (e : U.toScheme ⟶ affineTraceTower Y.left d) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : U.ι ≫ f.left = e ≫ affineTraceProjection Y.left d)
    (hOver : e ≫ affineTraceProjection Y.left d ≫ Y.hom = U.ι ≫ X.hom),
    (SpTowerCalculus.F l E b o q (c.precomp U.ι)).map (comparison K U e he).inv ≫
      (SpTowerCalculus.openComposition l E b o q U.ι c).inv.app
        ((SpTowerCalculus.etalePullback l E b o q U.ι).obj (G.obj K).obj) ≫
      (SpTowerCalculus.F l E b o q c).map
        ((openAdjunction l E b o q U.ι).counit.app (G.obj K).obj) ≫
      (adj.counit.app K).hom =
      (chart ⟨Y, hY⟩ (openBase X U (open_properties U)) d e hOver
        ((c.precomp U.ι).copy he.symm)).counit K
```

## New

The entire block above occurs verbatim in
lean/Sheaf/Paper/SmoothPurityTowerGluingData.lean, in the same namespace and with the
same universe, variables, options and instance attributes. The original module now
begins with:

```lean
module

public import Sheaf.Paper.SmoothPurityTowerGluingData
import Sheaf.Paper.SmoothPurityTowerBound
import Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction
import Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels
```

The shared interface has zero sorry. Its declaration ownership is recorded by
new definition node def-sp-tower-gluing-interfaces. The parent node now owns only
tower_gluing. The two new lemma statements are in their own modules and their
nodes contain their complete signatures and proof plans. The parent assembly
uses the existing sp_tower_bound and a proved private categorical uniqueness lemma.

## Users

The table contains every module returned by tools/downstream.py on the original
module, plus all delivered modules. None of the existing consumers requires an edit:
the definitions are textually identical and remain visible through a public import.
Among existing consumers only IntegralReconstructionComparisons names Charts;
several name Levels. No source-library file is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SmoothPurityTowerGluing | F3 | Re-exports the identical shared interface; proves the assembly. |
| Sheaf.Paper.SmoothPurityTowerGluingData | F3, new | Owns exactly the moved shared declarations. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | F3, new | States the global geometric adjunction step, without finite compatibility. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | F3, new | States finite compatibility conditional on the given adjunction and Charts. |
| Sheaf.Paper.CompactSupportTowerReduction | J9 | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | M6 | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | D8 | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | F6 | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | N2 | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | Q4 | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.TowerAdjointCompositorRealization | M4 | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | H9 | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Identical declarations re-exported; no source adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | F8 | Identical declarations re-exported; no source adaptation. |

The change is definitionally identical, including every operation used by targets.
Independent review should confirm the unchanged meanings and public re-export; no
target binder, statement text, hypothesis or conclusion is changed. There are no
forced adaptations of files held by other groups.

## Status

landed 20261025T162329-L-425972 2026-10-25 (merge of deliver/F3/Sheaf.Paper.SmoothPurityTowerGluing)
