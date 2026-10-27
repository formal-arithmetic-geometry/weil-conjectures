# EtaleGraphPresentation and the graph-comparison public interface

## Reason

The assigned module bundled the presentation definitions and the seven-clause coherence
theorem. The existing pairwise-product normalization uses only those definitions, yet
its public import of the coherence module prevented using its theorem to prove the
coherence module. Separate the identical definitions, publicly re-export them from the
item, and import the shared definition module in the pairwise normalization. No target,
existing Lean signature, visibility, or mathematical map changes. The assembly proof
locally marks the sheaf and derived-functor constructors irreducible, so categorical
cancellation does not unfold their large implementations. This proof-elaboration
attribute is local and changes no exported declaration or definition.

The pairwise, open-shrink and proper-ambient modules are unclaimed in current claim
records. Their current-main bodies are preserved verbatim, including W3's now complete
pairwise normalization proof. The only Lean change in each is the public import line.
The returned cycle at ae4dc602260 arose through the two elementary-move imports; both
must import the shared definitions rather than the full theorem. The same reference
correction is made in their DAG nodes; the theorem statements do not change.

## Old

The following declarations occurred in EtaleGraphComparisonBaseChange:

```lean
/-- A supplied presentation `f = p e a`, with proper outer factors and open middle factor.
Source: the presentations in the product-graph argument, Stacks Tags 0F7C--0F7F
(blueprint: lem-pur-etale-graph-comparison-base-change). -/
structure EtaleGraphPresentation {X Y : Scheme.{u}} (f : X ⟶ Y) where
  U : Scheme.{u}
  P : Scheme.{u}
  a : X ⟶ U
  e : U ⟶ P
  p : P ⟶ Y
  [properA : IsProper a]
  [openE : IsOpenImmersion e]
  [properP : IsProper p]
  fac : a ≫ e ≫ p = f

attribute [instance] EtaleGraphPresentation.properA EtaleGraphPresentation.openE
  EtaleGraphPresentation.properP

/-- An open-then-proper factorization is the presentation with identity first factor.
Source: `LowerShriekComposition.lean`, graph-model source
(blueprint: lem-pur-etale-graph-comparison-base-change). -/
def EtaleGraphPresentation.ofCompactification {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : EtaleGraphPresentation f where
  U := X
  P := c.Z
  a := 𝟙 X
  e := c.i
  p := c.g
  fac := by simpa using c.comm.symm

/-- The actual ordinary unbounded functor `Rp_* De_! Ra_*` attached to a presentation.
Source: `LowerShriekComposition.lean`, target of the graph comparison
(blueprint: lem-pur-etale-graph-comparison-base-change). -/
def EtaleGraphPresentation.functor (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A Y :=
  R((t.a)_*[ModuleCat.{u + 1} A]) ⋙ D((t.e)_!open[ModuleCat.{u + 1} A]) ⋙
    R((t.p)_*[ModuleCat.{u + 1} A])

/-- Remove the identity proper direct image in an open-then-proper presentation.
Source: `LowerShriekComposition.lean`, `rightDerivedLowerStarIdIso`
(blueprint: lem-pur-etale-graph-comparison-base-change). -/
def etaleGraphOpenNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (EtaleGraphPresentation.ofCompactification c).functor A ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.isoWhiskerRight (rightDerivedLowerStarIdIso A X) _ ≪≫ Functor.leftUnitor _

/-- The specified `B_{t,c}`: use the graph theorem only for its properness proofs and
then evaluate its explicit `B₁`, intersection `B₁₂`, and inverse `B₂` composite. No
endpoint isomorphism is chosen. Source: `EtaleLocallyClosedGraphModel.lean`, graph formula
(blueprint: lem-pur-etale-graph-comparison-base-change). -/
def etaleGraphComparisonFromOpen (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅ t.functor A :=
  let model := Classical.choice
    (etaleLocallyClosedGraphModel A t.a t.e t.p c.i c.g c.comm.symm t.fac)
  letI := model.properS₁
  letI := model.properS₂
  locallyClosedGraphIso t.a t.e t.p c.i c.g
    ((Category.assoc t.a t.e t.p).trans (t.fac.trans c.comm)) A

/-- `C_{t,s} = B_{t,c} B_{s,c}^{-1}`, retaining the auxiliary compactification explicitly
until the independence theorem. Source: Stacks Tags 0F7C--0F7D, product/intersection argument
(blueprint: lem-pur-etale-graph-comparison-base-change). -/
def etaleGraphComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) : s.functor A ≅ t.functor A :=
  (etaleGraphComparisonFromOpen A c s).symm ≪≫ etaleGraphComparisonFromOpen A c t

/-- Cartesian representatives of the three pulled-back factors of a presentation.
The maps `v` and `b` are the source and base projections. Source: Stacks Tag 0F7F
(blueprint: lem-pur-etale-graph-comparison-base-change). -/
structure EtaleGraphPresentation.BaseChange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (t : EtaleGraphPresentation f) (t' : EtaleGraphPresentation f')
    (v : X' ⟶ X) (b : Y' ⟶ Y) where
  u : t'.U ⟶ t.U
  w : t'.P ⟶ t.P
  aSquare : IsPullback v t'.a t.a u
  eSquare : IsPullback u t'.e t.e w
  pSquare : IsPullback w t'.p t.p b

/-- The actual successive canonical exchanges `chi_t`: proper exchange for `p`, inverse
of the unit-normalized open mate for `e`, then proper exchange for `a`, with associators.
Source: Stacks Tag 0F7F; `exactDerivedBaseChangeMap` and the termwise open-unit mate
(blueprint: lem-pur-etale-graph-comparison-base-change). -/
def etaleGraphPresentationExchange (A : Type (u + 1)) [CommRing A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {t : EtaleGraphPresentation f} {t' : EtaleGraphPresentation f'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} (d : t.BaseChange t' v b) :
    t.functor A ⋙ D((b)^*[ModuleCat.{u + 1} A]) ⟶
      D((v)^*[ModuleCat.{u + 1} A]) ⋙ t'.functor A :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) d.pSquare.toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) d.eSquare).inv _ ≫
      (Functor.associator _ _ _).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) d.aSquare.toCommSq) _ ≫
    (Functor.associator _ _ _).hom
```

The old item public imports were:

```lean
public import Sheaf.SixFunctors.EtaleLocallyClosedGraphModel
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
```

The pairwise, open-shrink and proper-ambient modules each publicly imported:

```lean
public import Sheaf.AlgebraicGeometry.EtaleGraphComparisonBaseChange
```

## New

The existing declarations above are verbatim in EtaleGraphPresentation. The item now
publicly imports that module, so its consumers see exactly the same existing names,
instances, functors and maps. The one additional record constructor is explicit:

```lean
/-- The Cartesian representatives for the base change of an open-then-proper presentation.
Source: `Compactification.BaseChange`, the two constituent pullback squares
(blueprint: def-pur-etale-graph-presentation-maps). -/
def EtaleGraphPresentation.ofCompactificationBaseChange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} (c : Compactification f) (sq : IsPullback v f' f b) :
    (EtaleGraphPresentation.ofCompactification c).BaseChange
      (EtaleGraphPresentation.ofCompactification (c.ofIsPullback sq)) v b where
  u := v
  w := pullback.fst c.g b
  aSquare := IsPullback.id_vert v
  eSquare := c.isPullback_i_ofIsPullback sq
  pSquare := (c.isPullback_g_ofIsPullback sq).flip
```

The pairwise, open-shrink and proper-ambient modules each now publicly import:

```lean
public import Sheaf.AlgebraicGeometry.EtaleGraphPresentation
```

Its existing statement, constructors and signatures are unchanged; the dependency in its
node statement is redirected from the old bundled node to the new definition node.
Each node's statement_change records this reference correction and audits its current citers.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleGraphComparisonBaseChange | F8 | Same public definitions re-exported; theorem signature unchanged; complete assembly proof. |
| Sheaf.AlgebraicGeometry.EtalePairwiseProductGraphNormalization | unclaimed | Only public import redirected; all current-main signatures and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGraphComparisonOpenShrink | unclaimed | Only public import redirected; all current-main signatures and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGraphComparisonProperAmbient | unclaimed | Only public import redirected; all current-main signatures and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGraphComparisonInterchange | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphInterchangeData | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphNeighborhoodWords | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductGeometry | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductInterchange | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductRowPasting | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphShrinkSidePasting | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |

The downstream and uses checks were rerun against current main. All twelve downstream
modules retain identical definitions and signatures. Current DAG citers of the three
import-adapted nodes are listed in their statement_change records; every use still holds.
The current W3 proofs in the pairwise module are preserved, not replaced with holes.
No module held by another group is adapted. Challenge.lean and the source library are
unchanged. The item import closure is acyclic after the three import corrections.
AlgebraicGeometry.EtaleGraphNeighborhoodGeometry | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphNeighborhoodWords | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductGeometry | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductInterchange | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductRowPasting | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
| Sheaf.AlgebraicGeometry.EtaleGraphShrinkSidePasting | unclaimed | No adaptation; unchanged definitions remain re-exported; every use retains its meaning. |
