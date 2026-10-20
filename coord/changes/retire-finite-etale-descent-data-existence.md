# AlgebraicGeometry.finiteEtaleDescentCompatible

## Reason

Retire item `Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence`, listed
in `coord/retire-items.tsv` as DIFFERENT with zero holes. Its upstream twin
already proves the construction. The recorded difference is only the lowercase
name of the compatibility predicate. The two predicates have verbatim bodies.
The two direct consumers also duplicate proved upstream theorems; re-exporting
their twins removes the duplicate declarations and the old import together.
Both consumers are unclaimed (no claim files at preparation).

## Old

The retired predicate was:

```lean
def finiteEtaleDescentCompatible {Y Y' : Scheme.{v}} {g : Y' ⟶ Y}
    (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
    (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left) : Prop :=
  (∀ P : Y.FiniteEtale,
    ∃ _hq : q P ≫ P.obj.hom = (F.obj P).obj.V.hom ≫ g,
      IsPullback (q P) (F.obj P).obj.V.hom P.obj.hom g ∧
      ∀ {T : Scheme.{v}} (f₁ f₂ : T ⟶ Y')
        (h : f₁ ≫ g = f₂ ≫ g) (z : Over.mk f₁ ⟶ (F.obj P).obj.V),
        ((F.obj P).obj.datum.transport f₁ f₂ h z).left ≫ q P = z.left ≫ q P) ∧
  ∀ P Q : Y.FiniteEtale, ∀ f : P ⟶ Q,
    (F.map f).hom.hom.left ≫ q Q = q P ≫ f.hom.left
```

The local theorem signatures were:

```lean
theorem finiteEtaleDescent_data {Y Y' : Scheme.{v}} (g : Y' ⟶ Y) :
    ∃ (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
      (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left),
      finiteEtaleDescentCompatible F q

theorem finiteEtaleDescent_essSurj {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    [Surjective g] [Etale g]
    (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
    (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left)
    (h : finiteEtaleDescentCompatible F q) : F.EssSurj

theorem finiteEtaleDescent_fullyFaithful {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    [Surjective g] [Etale g]
    (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
    (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left)
    (h : finiteEtaleDescentCompatible F q) : Nonempty F.FullyFaithful
```

## New

Delete `lean/Sheaf/AlgebraicGeometry/FiniteEtaleDescentDataExistence.lean`.
Use `AlgebraicGeometry.FiniteEtaleDescentCompatible` from
`WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentDataExistence`; its body
is exactly the old predicate body with the new name. The consumer modules
become public re-exports of their respective upstream twins:

```lean
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful
```

The corresponding upstream theorem signatures are:

```lean
theorem finiteEtaleDescent_data {Y Y' : Scheme.{v}} (g : Y' ⟶ Y) :
    ∃ (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
      (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left),
      FiniteEtaleDescentCompatible F q

theorem finiteEtaleDescent_essSurj {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    [Surjective g] [Etale g]
    (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
    (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left)
    (h : FiniteEtaleDescentCompatible F q) : F.EssSurj

theorem finiteEtaleDescent_fullyFaithful {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    [Surjective g] [Etale g]
    (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
    (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left)
    (h : FiniteEtaleDescentCompatible F q) : Nonempty F.FullyFaithful
```

The three DAG Lean attachments now point to these upstream declarations;
the compatibility declaration attachment uses the capitalized name. Node
statements and proof steps do not change. No upstream file changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence | D7 | duplicate deleted |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective | unclaimed | re-exports upstream theorem with definitionally identical hypothesis |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful | unclaimed | re-exports upstream theorem with definitionally identical hypothesis |

`tools/downstream.py` lists exactly these two direct consumers, and neither
consumer has any downstream importer. Searching all Lean sources finds no
other use of the lowercase predicate. No target mentions it. Therefore target
meaning is unchanged; no target statement or used definition is repaired here.

The server compiled a scratch theorem comparing the verbatim old predicate
with the upstream predicate by `Iff.rfl`. The server also printed axioms for
all three upstream theorems: only `propext`, `Classical.choice`, `Quot.sound`.
Both re-export modules compile separately without warnings.

## Status

landed 20261020T135359-L-1817002 2026-10-20 (merge of deliver/D7/Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence)
