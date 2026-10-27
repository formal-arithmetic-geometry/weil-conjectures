# AlgebraicGeometry.Etale.etaleGraphDiagramInterchange

## Reason

Separate the existing diagram data from the theorem that proves its coherence, so the
strict intermediate pasting statements can import the data without an import cycle.
Every existing declaration keeps its name, signature, visibility, and definition body.
The original module publicly imports the new data module and re-exports the same API.

## Old

The following declarations were in
`Sheaf.AlgebraicGeometry.EtaleGraphComparisonInterchange`:

```lean
def etaleGraphNormalizedProperOpenExchange (A : Type (u + 1)) [CommRing A] [Finite A] :
    ProperOpenDerivedComparisonFamily A :=
  Classical.choose (α := ProperOpenDerivedComparisonFamily A)
    (Classical.choose_spec (etaleProperOpenExchangeCube A))

/-- Shrink the middle neighborhood through a supplied proper lift.
Source: Stacks Tag 0F7J, elementary presentation move in the product-graph extension
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def EtaleGraphPresentation.shrink {X Z W : Scheme.{u}} {h : X ⟶ Z}
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    EtaleGraphPresentation h where
  U := W
  P := H.P
  a := a'
  e := v ≫ H.e
  p := H.p
  fac := by simpa only [← Category.assoc, fac] using H.fac

/-- The explicit inverse triangle interchange, followed by the open compositor.
The identity-top proper/open square is Cartesian; its normalized exchange, after
removing extension by the identity, is exactly the upstream triangle isomorphism.
Source: Stacks Tag 0F7J, elementary presentation move
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def etaleGraphShrinkInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (H : EtaleGraphPresentation h)
    (a' : X ⟶ W) (v : W ⟶ H.U) [IsProper a'] [IsOpenImmersion v]
    (fac : a' ≫ v = H.a) : H.functor A ≅ (H.shrink a' v fac).functor A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A a' v H.a fac).symm
      (D((H.e)_!open[ModuleCat.{u + 1} A]) ⋙ R((H.p)_*[ModuleCat.{u + 1} A])) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R((a')_*[ModuleCat.{u + 1} A])
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) v H.e).symm R((H.p)_*[ModuleCat.{u + 1} A]))

/-- One of the two supplied proper/open diagrams; its square need only commute.
Source: Stacks Tag 0F7J, two-diagram comparison, with the proper initial factor
of the product-graph extension
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
structure EtaleGraphInterchangeDiagram {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) where
  W : Scheme.{u}
  V : Scheme.{u}
  P : Scheme.{u}
  T : Scheme.{u}
  a : X ⟶ W
  e : W ⟶ V
  r : V ⟶ Y
  k : V ⟶ P
  p : P ⟶ T
  i : Y ⟶ T
  q : T ⟶ Z
  [properA : IsProper a]
  [properR : IsProper r]
  [properP : IsProper p]
  [properQ : IsProper q]
  [openE : IsOpenImmersion e]
  [openK : IsOpenImmersion k]
  [openI : IsOpenImmersion i]
  facF : a ≫ e ≫ r = f
  facG : i ≫ q = g
  square : CommSq k r p i

attribute [instance] EtaleGraphInterchangeDiagram.properA EtaleGraphInterchangeDiagram.properR
  EtaleGraphInterchangeDiagram.properP EtaleGraphInterchangeDiagram.properQ
  EtaleGraphInterchangeDiagram.openE EtaleGraphInterchangeDiagram.openK
  EtaleGraphInterchangeDiagram.openI

/-- The supplied presentation `t = (a,e,r)` of `f`.
Source: Stacks Tag 0F7J, two-diagram comparison
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def EtaleGraphInterchangeDiagram.sourcePresentation {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    EtaleGraphPresentation f where
  U := d.W
  P := d.V
  a := d.a
  e := d.e
  p := d.r
  fac := d.facF

/-- The supplied open-then-proper factorization `(i,q)` of `g`.
Source: Stacks Tag 0F7J, two-diagram comparison
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def EtaleGraphInterchangeDiagram.compactification {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    Compactification g where
  Z := d.T
  i := d.i
  g := d.q
  comm := d.facG.symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The supplied presentation `s = (a,ke,qp)` of the composite.
Source: Stacks Tag 0F7J, two-diagram comparison
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def EtaleGraphInterchangeDiagram.compositePresentation {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    EtaleGraphPresentation (f ≫ g) where
  U := d.W
  P := d.P
  a := d.a
  e := d.e ≫ d.k
  p := d.p ≫ d.q
  fac := by
    calc
      _ = d.a ≫ d.e ≫ (d.k ≫ d.p) ≫ d.q := by simp only [Category.assoc]
      _ = d.a ≫ d.e ≫ (d.r ≫ d.i) ≫ d.q := by rw [d.square.w]
      _ = (d.a ≫ d.e ≫ d.r) ≫ (d.i ≫ d.q) := by simp only [Category.assoc]
      _ = f ≫ g := congrArg₂ (fun l m ↦ l ≫ m) d.facF d.facG

/-- The specified word `Rq Γ_Q Je Ra`, including the identity-direct-image normalization,
open compositor and proper compositor. No isomorphism with bare endpoints is chosen.
Source: Stacks Tag 0F7J, first paragraph and A--F comparison
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def etaleGraphDiagramInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g) :
    d.sourcePresentation.functor A ⋙
        (EtaleGraphPresentation.ofCompactification d.compactification).functor A ≅
      d.compositePresentation.functor A :=
  Functor.isoWhiskerLeft (d.sourcePresentation.functor A)
      (etaleGraphOpenNormalization A d.compactification) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R((d.a)_*[ModuleCat.{u + 1} A])
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D((d.e)_!open[ModuleCat.{u + 1} A])
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              (etaleGraphNormalizedProperOpenExchange A d.k d.r d.p d.i d.square)
              R((d.q)_*[ModuleCat.{u + 1} A]) ≪≫
            Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) d.e d.k).symm
          (R((d.p)_*[ModuleCat.{u + 1} A]) ⋙ R((d.q)_*[ModuleCat.{u + 1} A])) ≪≫
        Functor.isoWhiskerLeft D((d.e ≫ d.k)_!open[ModuleCat.{u + 1} A])
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q))
```

## New

The same declarations and bodies are in
`Sheaf.AlgebraicGeometry.EtaleGraphInterchangeData`, publicly imported by the original
module. No existing mathematical statement or definition changes. 
The new public re-export is:

```lean
public import Sheaf.AlgebraicGeometry.EtaleGraphInterchangeData
```

The definitions in the data module are, verbatim:

```lean
def etaleGraphNormalizedProperOpenExchange (A : Type (u + 1)) [CommRing A] [Finite A] :
    ProperOpenDerivedComparisonFamily A :=
  Classical.choose (α := ProperOpenDerivedComparisonFamily A)
    (Classical.choose_spec (etaleProperOpenExchangeCube A))

/-- Shrink the middle neighborhood through a supplied proper lift.
Source: Stacks Tag 0F7J, elementary presentation move in the product-graph extension
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def EtaleGraphPresentation.shrink {X Z W : Scheme.{u}} {h : X ⟶ Z}
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    EtaleGraphPresentation h where
  U := W
  P := H.P
  a := a'
  e := v ≫ H.e
  p := H.p
  fac := by simpa only [← Category.assoc, fac] using H.fac

/-- The explicit inverse triangle interchange, followed by the open compositor.
The identity-top proper/open square is Cartesian; its normalized exchange, after
removing extension by the identity, is exactly the upstream triangle isomorphism.
Source: Stacks Tag 0F7J, elementary presentation move
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def etaleGraphShrinkInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (H : EtaleGraphPresentation h)
    (a' : X ⟶ W) (v : W ⟶ H.U) [IsProper a'] [IsOpenImmersion v]
    (fac : a' ≫ v = H.a) : H.functor A ≅ (H.shrink a' v fac).functor A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A a' v H.a fac).symm
      (D((H.e)_!open[ModuleCat.{u + 1} A]) ⋙ R((H.p)_*[ModuleCat.{u + 1} A])) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R((a')_*[ModuleCat.{u + 1} A])
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) v H.e).symm R((H.p)_*[ModuleCat.{u + 1} A]))

/-- One of the two supplied proper/open diagrams; its square need only commute.
Source: Stacks Tag 0F7J, two-diagram comparison, with the proper initial factor
of the product-graph extension
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
structure EtaleGraphInterchangeDiagram {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) where
  W : Scheme.{u}
  V : Scheme.{u}
  P : Scheme.{u}
  T : Scheme.{u}
  a : X ⟶ W
  e : W ⟶ V
  r : V ⟶ Y
  k : V ⟶ P
  p : P ⟶ T
  i : Y ⟶ T
  q : T ⟶ Z
  [properA : IsProper a]
  [properR : IsProper r]
  [properP : IsProper p]
  [properQ : IsProper q]
  [openE : IsOpenImmersion e]
  [openK : IsOpenImmersion k]
  [openI : IsOpenImmersion i]
  facF : a ≫ e ≫ r = f
  facG : i ≫ q = g
  square : CommSq k r p i

attribute [instance] EtaleGraphInterchangeDiagram.properA EtaleGraphInterchangeDiagram.properR
  EtaleGraphInterchangeDiagram.properP EtaleGraphInterchangeDiagram.properQ
  EtaleGraphInterchangeDiagram.openE EtaleGraphInterchangeDiagram.openK
  EtaleGraphInterchangeDiagram.openI

/-- The supplied presentation `t = (a,e,r)` of `f`.
Source: Stacks Tag 0F7J, two-diagram comparison
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def EtaleGraphInterchangeDiagram.sourcePresentation {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    EtaleGraphPresentation f where
  U := d.W
  P := d.V
  a := d.a
  e := d.e
  p := d.r
  fac := d.facF

/-- The supplied open-then-proper factorization `(i,q)` of `g`.
Source: Stacks Tag 0F7J, two-diagram comparison
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def EtaleGraphInterchangeDiagram.compactification {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    Compactification g where
  Z := d.T
  i := d.i
  g := d.q
  comm := d.facG.symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The supplied presentation `s = (a,ke,qp)` of the composite.
Source: Stacks Tag 0F7J, two-diagram comparison
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def EtaleGraphInterchangeDiagram.compositePresentation {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    EtaleGraphPresentation (f ≫ g) where
  U := d.W
  P := d.P
  a := d.a
  e := d.e ≫ d.k
  p := d.p ≫ d.q
  fac := by
    calc
      _ = d.a ≫ d.e ≫ (d.k ≫ d.p) ≫ d.q := by simp only [Category.assoc]
      _ = d.a ≫ d.e ≫ (d.r ≫ d.i) ≫ d.q := by rw [d.square.w]
      _ = (d.a ≫ d.e ≫ d.r) ≫ (d.i ≫ d.q) := by simp only [Category.assoc]
      _ = f ≫ g := congrArg₂ (fun l m ↦ l ≫ m) d.facF d.facG

/-- The specified word `Rq Γ_Q Je Ra`, including the identity-direct-image normalization,
open compositor and proper compositor. No isomorphism with bare endpoints is chosen.
Source: Stacks Tag 0F7J, first paragraph and A--F comparison
(blueprint: lem-pur-etale-graph-comparison-interchange). -/
def etaleGraphDiagramInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g) :
    d.sourcePresentation.functor A ⋙
        (EtaleGraphPresentation.ofCompactification d.compactification).functor A ≅
      d.compositePresentation.functor A :=
  Functor.isoWhiskerLeft (d.sourcePresentation.functor A)
      (etaleGraphOpenNormalization A d.compactification) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R((d.a)_*[ModuleCat.{u + 1} A])
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D((d.e)_!open[ModuleCat.{u + 1} A])
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              (etaleGraphNormalizedProperOpenExchange A d.k d.r d.p d.i d.square)
              R((d.q)_*[ModuleCat.{u + 1} A]) ≪≫
            Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) d.e d.k).symm
          (R((d.p)_*[ModuleCat.{u + 1} A]) ⋙ R((d.q)_*[ModuleCat.{u + 1} A])) ≪≫
        Functor.isoWhiskerLeft D((d.e ≫ d.k)_!open[ModuleCat.{u + 1} A])
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q))
```
## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleGraphComparisonInterchange | V1 | Publicly re-exports the moved definitions; proves its unchanged theorem from intermediate pasting statements. |

| Sheaf.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry | new, V1 | Constructs the neighborhood map from the unchanged presentation and shrink definitions. |
| Sheaf.AlgebraicGeometry.EtaleGraphNeighborhoodWords | new, V1 | Defines the graph words and inverse neighborhood triangle. |
| Sheaf.AlgebraicGeometry.EtaleGraphShrinkSidePasting | new, V1 | States the side-square substep for the unchanged shrinking map. |
| Sheaf.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting | new, V1 | States the intersection substep for the graph words. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductGeometry | new, V1 | Constructs products of the supplied diagrams. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductInterchange | new, V1 | Uses the unchanged normalized exchange family in the common boundary. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductRowPasting | new, V1 | States one selected row to that explicit boundary. |

`tools/downstream.py` reports no other current Lean consumer. DAG parents still need
the unchanged theorem, so it is retained. All new intermediate consumers are included
in this packet. The target statements retain the same definitions and meanings.

## Status

landed 20261024T020820-L-2671853 2026-10-24 (merge of deliver/V1/Sheaf.AlgebraicGeometry.EtaleGraphComparisonInterchange)
