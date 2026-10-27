# CenteredToricTowerLift

## Reason

Extract the existing lift data from the item module so separate construction and uniqueness
lemmas can refer to it without creating an import cycle. All three declaration names,
binders, universes, fields, bodies and visibility are preserved. Only the declaration
locations and their blueprint ownership tags change. The item publicly imports the new
data module, so it continues to export the same original interface. Its theorem signature
and its four original public imports are unchanged. No target definition changes meaning.

## Old

The following declarations were in
`Sheaf.AlgebraicGeometry.MonoschemeToricTowerDescent`:

```lean
/-- The original component tori preserve every center of the given normalized tower.
The lifted action is over the original monomial action, and preservation is equality
of ideal sheaves, not of their radicals. Products are restricted to the component.
Source: ILO VIII 3.2.15 and 3.2.19
(blueprint: lem-trf-monoscheme-toric-tower-descent). -/
def NormalizedTower.HasEquivariantToricCenters {n : ℕ} (M : Fine.{u})
    (T : NormalizedTower.{u} n) (e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M) : Prop :=
  ∀ (C : ToricComponent M) (i : Fin n),
    ∃ μ : toricActionDomain (ULift.{u} ℚ) C
        (T.toFirst i.castSucc ≫ e₀.hom) ⟶ T.level i.castSucc,
      μ ≫ T.toFirst i.castSucc ≫ e₀.hom =
        toricActionBase (ULift.{u} ℚ) C (T.toFirst i.castSucc ≫ e₀.hom) ∧
      (T.center i).comap μ = (T.center i).comap
        (pullback.snd _ _ ≫ pullback.fst _ _)

/-- A centered lift retains every stage and uses the canonical monomial realization
of every arrow. `Tower.blowup` supplies the exact saturated affine blowup charts and
nonempty coherent monoid centers. Finiteness of affine covers is part of `Fine`.
The comparison is over the original base with its unchanged dense component tori.
Source: ILO VIII 3.2.18--3.2.20
(blueprint: lem-trf-monoscheme-toric-tower-descent). -/
structure CenteredToricTowerLift {n : ℕ} (M : Fine.{u})
    (T : NormalizedTower.{u} n) (e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M) where
  tower : Tower.{u} n
  base : tower.level 0 = M
  torsionFree : ∀ i, (tower.level i).IsTorsionFree
  iso : ∀ i, realization (ULift.{u} ℚ) (tower.level i) ≅ T.level i
  initial : (iso 0).hom ≫ e₀.hom =
    eqToHom (congrArg (realization (ULift.{u} ℚ)) base)
  centers : ∀ i : Fin n, ringIdeal (ULift.{u} ℚ) (tower.center i) =
    (T.center i).comap (iso i.castSucc).hom
  arrows : ∀ i : Fin n,
    realizationMap (ULift.{u} ℚ) (tower.arrow i) ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ T.arrow i
  equivariant : ∀ i : Fin (n + 1),
    IsToricComparison (ULift.{u} ℚ)
      ((iso i).hom ≫ T.toFirst i ≫ e₀.hom) (T.toFirst i ≫ e₀.hom) (iso i)

/-- The canonical centered identification between two lifts fixes the specified base,
commutes with arrows, preserves the actual ideals, and induces the specified scheme
identifications by the monomial realization. It compares monoscheme maps, not arbitrary
scheme isomorphisms; uniqueness of this family is the intended uniqueness of descent.
Source: ILO VIII 3.2.14--3.2.20
(blueprint: lem-trf-monoscheme-toric-tower-descent). -/
def CenteredToricTowerLift.IsCenteredIdentification {n : ℕ} {M : Fine.{u}}
    {T : NormalizedTower.{u} n} {e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M}
    (L L' : CenteredToricTowerLift M T e₀)
    (e : ∀ i : Fin (n + 1), (L.tower.level i).space ≅ (L'.tower.level i).space) : Prop :=
  (e 0).hom = eqToHom (congrArg Fine.space (L.base.trans L'.base.symm)) ∧
  (∀ i : Fin n,
    (L.tower.arrow i).map ≫ (e i.castSucc).hom =
      (e i.succ).hom ≫ (L'.tower.arrow i).map) ∧
  (∀ i : Fin n,
    L.tower.center i = pullbackAlong (e i.castSucc).hom (L'.tower.center i)) ∧
  ∀ i : Fin (n + 1), ∃ f : Hom (L.tower.level i) (L'.tower.level i),
    f.map = (e i).hom ∧
      realizationMap (ULift.{u} ℚ) f ≫ (L'.iso i).hom = (L.iso i).hom
```

## New

The same declarations are now in `Sheaf.AlgebraicGeometry.CenteredToricTowerLiftData`,
publicly imported by the original module. The docstring tags now name the extracted
definition node. There is exactly one implementation of each declaration.

```lean
/-- The original component tori preserve every center of the given normalized tower.
The lifted action is over the original monomial action, and preservation is equality
of ideal sheaves, not of their radicals. Products are restricted to the component.
Source: ILO VIII 3.2.15 and 3.2.19
(blueprint: def-trf-centered-toric-tower-lift-data). -/
def NormalizedTower.HasEquivariantToricCenters {n : ℕ} (M : Fine.{u})
    (T : NormalizedTower.{u} n) (e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M) : Prop :=
  ∀ (C : ToricComponent M) (i : Fin n),
    ∃ μ : toricActionDomain (ULift.{u} ℚ) C
        (T.toFirst i.castSucc ≫ e₀.hom) ⟶ T.level i.castSucc,
      μ ≫ T.toFirst i.castSucc ≫ e₀.hom =
        toricActionBase (ULift.{u} ℚ) C (T.toFirst i.castSucc ≫ e₀.hom) ∧
      (T.center i).comap μ = (T.center i).comap
        (pullback.snd _ _ ≫ pullback.fst _ _)

/-- A centered lift retains every stage and uses the canonical monomial realization
of every arrow. `Tower.blowup` supplies the exact saturated affine blowup charts and
nonempty coherent monoid centers. Finiteness of affine covers is part of `Fine`.
The comparison is over the original base with its unchanged dense component tori.
Source: ILO VIII 3.2.18--3.2.20
(blueprint: def-trf-centered-toric-tower-lift-data). -/
structure CenteredToricTowerLift {n : ℕ} (M : Fine.{u})
    (T : NormalizedTower.{u} n) (e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M) where
  tower : Tower.{u} n
  base : tower.level 0 = M
  torsionFree : ∀ i, (tower.level i).IsTorsionFree
  iso : ∀ i, realization (ULift.{u} ℚ) (tower.level i) ≅ T.level i
  initial : (iso 0).hom ≫ e₀.hom =
    eqToHom (congrArg (realization (ULift.{u} ℚ)) base)
  centers : ∀ i : Fin n, ringIdeal (ULift.{u} ℚ) (tower.center i) =
    (T.center i).comap (iso i.castSucc).hom
  arrows : ∀ i : Fin n,
    realizationMap (ULift.{u} ℚ) (tower.arrow i) ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ T.arrow i
  equivariant : ∀ i : Fin (n + 1),
    IsToricComparison (ULift.{u} ℚ)
      ((iso i).hom ≫ T.toFirst i ≫ e₀.hom) (T.toFirst i ≫ e₀.hom) (iso i)

/-- The canonical centered identification between two lifts fixes the specified base,
commutes with arrows, preserves the actual ideals, and induces the specified scheme
identifications by the monomial realization. It compares monoscheme maps, not arbitrary
scheme isomorphisms; uniqueness of this family is the intended uniqueness of descent.
Source: ILO VIII 3.2.14--3.2.20
(blueprint: def-trf-centered-toric-tower-lift-data). -/
def CenteredToricTowerLift.IsCenteredIdentification {n : ℕ} {M : Fine.{u}}
    {T : NormalizedTower.{u} n} {e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M}
    (L L' : CenteredToricTowerLift M T e₀)
    (e : ∀ i : Fin (n + 1), (L.tower.level i).space ≅ (L'.tower.level i).space) : Prop :=
  (e 0).hom = eqToHom (congrArg Fine.space (L.base.trans L'.base.symm)) ∧
  (∀ i : Fin n,
    (L.tower.arrow i).map ≫ (e i.castSucc).hom =
      (e i.succ).hom ≫ (L'.tower.arrow i).map) ∧
  (∀ i : Fin n,
    L.tower.center i = pullbackAlong (e i.castSucc).hom (L'.tower.center i)) ∧
  ∀ i : Fin (n + 1), ∃ f : Hom (L.tower.level i) (L'.tower.level i),
    f.map = (e i).hom ∧
      realizationMap (ULift.{u} ℚ) f ≫ (L'.iso i).hom = (L.iso i).hom
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.MonoschemeToricTowerDescent --uses
CenteredToricTowerLift HasEquivariantToricCenters IsCenteredIdentification` found zero
existing downstream modules. A direct import search also found none. Therefore no
existing consumer copies or forced adaptations require compilation. The item and all
three new modules compile individually through the sandbox compilation set.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MonoschemeToricTowerDescent | R5 | Imports the extracted data publicly; its theorem signature stays identical. |
| Sheaf.AlgebraicGeometry.CenteredToricTowerLiftData | R5, new | Receives the existing three definitions verbatim. |
| Sheaf.AlgebraicGeometry.CenteredToricTowerLiftExistence | R5, new | Uses the extracted data in the construction-only conclusion. |
| Sheaf.AlgebraicGeometry.CenteredToricTowerLiftUniqueness | R5, new | Uses the extracted data for two supplied lifts and their identifications. |

## Status

landed 20261026T092450-L-3434782 2026-10-26 (merge of deliver/R5/Sheaf.AlgebraicGeometry.MonoschemeToricTowerDescent)
