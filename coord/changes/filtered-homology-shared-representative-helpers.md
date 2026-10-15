# Shared filtered-homology representative helpers

## Reason

The landing of the previous delivery was refused because the new forward-representative
module copied five private theorems from the existing tower-quotients module. The latter
imports the differential item, so importing it from the forward-representative module
would close an import cycle. Relocate the existing proofs once into the lower-level
forward-representative module and import them from the quotient module.

`Sheaf.CategoryTheory.FilteredHomologyTowerQuotients` was unclaimed when this repair
was made. This is an allowed change to an unclaimed module, not an adaptation of a
module another group holds. No definition or public statement changes.

## Old

The following private signatures and their proofs occur in
`Sheaf.CategoryTheory.FilteredHomologyTowerQuotients`:

```lean
private theorem inclusion_homology_heq
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (a b a' b' n n' : ℤ) (h : b ≤ a) (h' : b' ≤ a')
    (ha : a = a') (hb : b = b') (hn : n = n') :
    HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step a) (F.step b) (F.antitone_step h)) n ≍
      HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step a') (F.step b') (F.antitone_step h')) n'

private theorem filtered_alphaIter
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (s : ℕ) (P Q : ℤ) :
    (filteredHomologyExactCouple K F).alphaIter s P Q ≍
      HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step (-Q)) (F.step (-(Q + (s : ℤ))))
          (F.antitone_step (by omega))) (P + Q)

private theorem connecting_heq
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n p' n' : ℤ) (hp : p = p') (hn : n = n') :
    (filteredStep_shortExact K F p).δ n (n + 1) rfl ≍
      (filteredStep_shortExact K F p').δ n' (n' + 1) rfl

private theorem filtered_initial_f
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ) :
    (filteredHomologyEIso K F p q).inv ≫
        (filteredHomologyExactCouple K F).f (2 * p + q) (-p) ≍
      (filteredStep_shortExact K F p).δ (p + q) (p + q + 1) rfl

private theorem connecting_representative
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n r : ℤ) (hr : 1 ≤ r) {A : C}
    (a : A ⟶ (F.step p : CochainComplex C ℤ).X n)
    (a' : A ⟶ (F.step (p + r) : CochainComplex C ℤ).X (n + 1))
    (g : A ⟶ (F.gradedPiece p).cycles n)
    (ha : a ≫ (F.step p).arrow.f n ≫ K.d n (n + 1) =
      a' ≫ (F.step (p + r)).arrow.f (n + 1))
    (hg : g ≫ (F.gradedPiece p).iCycles n =
      a ≫ (F.complexQuotientπ p (p + 1) (by omega)).f n) :
    ∃ z : A ⟶ (F.step (p + r) : CochainComplex C ℤ).cycles (n + 1),
      z ≫ (F.step (p + r) : CochainComplex C ℤ).iCycles (n + 1) = a' ∧
      g ≫ (F.gradedPiece p).homologyπ n ≫
          (filteredStep_shortExact K F p).δ n (n + 1) rfl =
        z ≫ (F.step (p + r) : CochainComplex C ℤ).homologyπ (n + 1) ≫
          HomologicalComplex.homologyMap
            (Subobject.ofLE (F.step (p + r)) (F.step (p + 1))
              (F.antitone_step (by omega))) (n + 1)
```

## New

The exact same five private signatures and complete proof bodies occur once in
`Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives`. They are removed
from `Sheaf.CategoryTheory.FilteredHomologyTowerQuotients`, whose only other change is
this proof-only import:

```lean
import all Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives
```

Private visibility is retained. The quotient module's public imports, declarations,
definitions and remaining proofs are unchanged. The new module does not import the
quotient module; the resulting dependency graph has no cycle. No target statement or
definition changes, and no target statement review is reopened.

## Users

`tools/downstream.py` was run with `--uses` for all five helper names. The only user
of these private helpers in the existing module's downstream closure is the module
itself. None of its public consumers use these private names.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredHomologyTowerQuotients | unclaimed | Remove five private proof copies; import their single implementation. |
| Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives | new in T2 delivery | Home of the five unchanged private proofs; forward theorem uses them. |
| Sheaf.CategoryTheory.FilteredHomologyTowerDifferential | T2 | Proves the existing theorem from the forward identity and the derived-g comparison. |

## Status

landed 20261015T235420-L-3518739 2026-10-15 (merge of deliver/T2/Sheaf.CategoryTheory.FilteredHomologyTowerDifferential)
