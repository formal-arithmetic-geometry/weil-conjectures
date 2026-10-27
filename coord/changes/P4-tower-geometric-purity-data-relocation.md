# AlgebraicGeometry.ProEtale.SpGeometricPurity (data relocation)

## Reason

The strictly lower root, presentation-comparison and two-factor lemmas must refer to the
existing interfaces without importing their own consumer. Move only the existing data
portion into `Sheaf.Paper.TowerGeometricPurityData`, and publicly import that module from
the original module. Every name, universe, binder, attribute and definition body is
preserved. The original conclusion definition and theorem statement are unchanged.
No target meaning changes. No adopted-source file is changed.

## Old

Location: `lean/Sheaf/Paper/TowerGeometricPurityMate.lean`.
The signatures below are verbatim as read by the declaration parser; their complete
bodies are unchanged in the new file.

```lean
structure Roots {X : Scheme.{u}} (g : X ⟶ X) (w : SpChartAdmissibility.Twists l E X) (r : SpCoordinateAdjunction.RootLines l E X)

def orderedRoots {X : Scheme.{u}} {g : X ⟶ X} {w : SpChartAdmissibility.Twists l E X} {r : SpCoordinateAdjunction.RootLines l E X} (t : Roots l E b o g w r) : ∀ d : ℕ, (SpTowerShriek.pull l E b (o.geometry g)).obj (SpTowerGamma.orderedLine l E b X w d) ≅ SpTowerGamma.orderedLine l E b X w d

def pullRealization {X Y : Scheme.{u}} (g : X ⟶ Y) (h : ∀ K : SpTowerCalculus.C l E b q Y, spConstructibleTorTowers l E X (q.abelian X) ((SpTowerCalculus.etalePullback l E b o q g).obj K.obj)) (K : SpTowerCalculus.C l E b q Y) : (SpTowerGamma.realization l E b q X).obj ((ObjectProperty.lift _ (SpTowerCalculus.inclusion l E b q Y ⋙ SpTowerCalculus.etalePullback l E b o q g) h).obj K) ≅ (SpTowerShriek.pull l E b (o.geometry g)).obj ((SpTowerGamma.realization l E b q Y).obj K)

def Q : SpTowerCalculus.C l E b q X ⥤ SpTowerCalculus.C l E b q X

def P : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q Y

def sourceComparison (w : SpChartAdmissibility.Twists l E X) (r : SpCoordinateAdjunction.RootLines l E X) (t : Roots l E b o gX w r) (d : ℕ) (K : SpTowerCalculus.C l E b q Y) : (SpTowerShriek.pull l E b (o.geometry gX)).obj ((SpTowerGamma.source l E b o q f w d).obj K) ≅ (SpTowerGamma.source l E b o q f w d).obj ((P l E b o q gY hy).obj K)

def exchange : SpTowerGluing.support l E b o q c hF ⋙ P l E b o q gY hy ⟶ Q l E b o q gX hx ⋙ SpTowerGluing.support l E b o q c hF

def mate (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X) (adj : SpTowerGluing.support l E b o q c hF ⊣ G) (hb : IsIso (exchange l E b o q k f gX gY sq c z h cal x hx hy hF)) : G ⋙ Q l E b o q gX hx ⟶ P l E b o q gY hy ⋙ G

def purityIso (K : SpTowerCalculus.C l E b q Y) : (SpTowerGamma.source l E b o q (j ≫ p) w d).obj K ≅ (SpTowerGamma.exceptional l E b q G).obj K

def Retagging : Prop

structure Result
```

## New

Location: `lean/Sheaf/Paper/TowerGeometricPurityData.lean`, publicly re-exported by
`Sheaf.Paper.TowerGeometricPurityMate`. Identical signatures and bodies:

```lean
structure Roots {X : Scheme.{u}} (g : X ⟶ X) (w : SpChartAdmissibility.Twists l E X) (r : SpCoordinateAdjunction.RootLines l E X)

def orderedRoots {X : Scheme.{u}} {g : X ⟶ X} {w : SpChartAdmissibility.Twists l E X} {r : SpCoordinateAdjunction.RootLines l E X} (t : Roots l E b o g w r) : ∀ d : ℕ, (SpTowerShriek.pull l E b (o.geometry g)).obj (SpTowerGamma.orderedLine l E b X w d) ≅ SpTowerGamma.orderedLine l E b X w d

def pullRealization {X Y : Scheme.{u}} (g : X ⟶ Y) (h : ∀ K : SpTowerCalculus.C l E b q Y, spConstructibleTorTowers l E X (q.abelian X) ((SpTowerCalculus.etalePullback l E b o q g).obj K.obj)) (K : SpTowerCalculus.C l E b q Y) : (SpTowerGamma.realization l E b q X).obj ((ObjectProperty.lift _ (SpTowerCalculus.inclusion l E b q Y ⋙ SpTowerCalculus.etalePullback l E b o q g) h).obj K) ≅ (SpTowerShriek.pull l E b (o.geometry g)).obj ((SpTowerGamma.realization l E b q Y).obj K)

def Q : SpTowerCalculus.C l E b q X ⥤ SpTowerCalculus.C l E b q X

def P : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q Y

def sourceComparison (w : SpChartAdmissibility.Twists l E X) (r : SpCoordinateAdjunction.RootLines l E X) (t : Roots l E b o gX w r) (d : ℕ) (K : SpTowerCalculus.C l E b q Y) : (SpTowerShriek.pull l E b (o.geometry gX)).obj ((SpTowerGamma.source l E b o q f w d).obj K) ≅ (SpTowerGamma.source l E b o q f w d).obj ((P l E b o q gY hy).obj K)

def exchange : SpTowerGluing.support l E b o q c hF ⋙ P l E b o q gY hy ⟶ Q l E b o q gX hx ⋙ SpTowerGluing.support l E b o q c hF

def mate (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X) (adj : SpTowerGluing.support l E b o q c hF ⊣ G) (hb : IsIso (exchange l E b o q k f gX gY sq c z h cal x hx hy hF)) : G ⋙ Q l E b o q gX hx ⟶ P l E b o q gY hy ⋙ G

def purityIso (K : SpTowerCalculus.C l E b q Y) : (SpTowerGamma.source l E b o q (j ≫ p) w d).obj K ≅ (SpTowerGamma.exceptional l E b q G).obj K

def Retagging : Prop

structure Result
```

## Users

`tools/downstream.py Sheaf.Paper.TowerGeometricPurityMate --uses` and the direct-import
search report no existing downstream modules. The original node still has unfinished
DAG parents: none is withdrawn, and the re-export preserves the interface for them.
No other existing module needs adaptation. The new consumers are listed for clarity.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TowerGeometricPurityMate | P4 | unchanged public interface; imports data and proved assembly |
| Sheaf.Paper.TowerIsomorphismPullback | P4 (new) | uses strict Roots and tower domain interfaces |
| Sheaf.Paper.TowerPurityPresentationRetagging | P4 (new) | uses Retagging |
| Sheaf.Paper.TowerTensorPresentationRetagging | P4 (new) | uses actual projection-counit and tensor-transpose interfaces |
| Sheaf.Paper.TowerSemilinearPurityFactors | P4 (new) | uses specified exchange, mate and factor interfaces |
| Sheaf.Paper.TowerGeometricPurityAssembly | P4 (new) | constructs the unchanged Result |

## Status

landed 20261027T012915-L-2345962 2026-10-27 (merge of deliver/P4/Sheaf.Paper.TowerGeometricPurityMate)
