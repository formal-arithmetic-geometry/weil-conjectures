# CategoryTheory.exists_natural_boundedBelow_truncation_couples

## Reason

Complete retirement row `retire:Sheaf.CategoryTheory.NaturalTruncationCouple`
in `coord/retire-items.tsv`, following the human hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. This is a zero-hole retirement,
not a new proof or a decomposition. The adopted source already proves the same
public theorem. Its full signature and four public imports are byte-identical
to the duplicate. Both modules construct the raw objects and maps explicitly;
only the proof fields use raw exactness. There is no arbitrary data chosen from
an unproved existence statement.

All six listed prerequisites are retired: DerivedCoupleFunctoriality,
ExactCouple, ExactCoupleConvergence, Filtration, TruncationAbutmentCocone and
TruncationCoupleNaturality. The adopted module's project import closure contains
no Sheaf module and hence no pair of live Sheaf/adopted twins.

## Old

Module `Sheaf.CategoryTheory.NaturalTruncationCouple` supplies this signature:

```lean
theorem exists_natural_boundedBelow_truncation_couples
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (a : ℤ) :
    let L := {M : DerivedCategory A // ∀ r : ℤ, r < a →
      IsZero ((DerivedCategory.homologyFunctor A r).obj M)}
    ∃ (Z : L → BigradedExactCouple B 0)
      (eD : ∀ (M : L) (n : ℤ), (Z M).D 0 n ≅
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj M.val)
      (eE : ∀ (M : L) (p : ℕ) (r : ℤ), (Z M).E p r ≅
        (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B (p : ℤ)).obj
            ((DerivedCategory.homologyFunctor A r).obj M.val)),
      (∀ (M : L) (p r : ℤ), r < a → IsZero ((Z M).D p r)) ∧
      (∀ (M : L) (p r : ℤ), p < 0 → IsZero ((Z M).E p r)) ∧
      ∀ (M N : L) (c : M.val ⟶ N.val),
        ∃ T : BigradedExactCouple.CoupleMorphism (Z M) (Z N),
          (∀ n : ℤ, T.tD 0 n ≫ (eD N n).hom = (eD M n).hom ≫
            (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map c) ∧
          (∀ (p : ℕ) (r : ℤ), T.tE p r ≫ (eE N p r).hom = (eE M p r).hom ≫
            (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
              DerivedCategory.homologyFunctor B (p : ℤ)).map
                ((DerivedCategory.homologyFunctor A r).map c))
```

Its other declarations are private proof helpers: `zero_projection_square`,
`rawCouple` and `abutmentMap_isIso`. They have no external users.

## New

Withdraw `lean/Sheaf/CategoryTheory/NaturalTruncationCouple.lean` using
`deleted.txt`. The identical public signature is supplied by
`WeilConjectures.CategoryTheory.NaturalTruncationCouple`, whose existing proof
and private helpers remain untouched. Reattach the node
`lem-pc-natural-bounded-below-truncation-couples` to that module, retaining
its declaration name and verbatim statement. Only the node's `lean` record
changes; its mathematical statement, proof, dependencies and unit route remain.

No source-library file, public import, target statement, or definition is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.NaturalTruncationCouple | U3 | Withdraw the duplicate. |
| WeilConjectures.CategoryTheory.CoproductTruncationCouple | unmodified | Already imports the adopted theorem; no adaptation. |

`tools/downstream.py Sheaf.CategoryTheory.NaturalTruncationCouple` reports zero
module users. Searches of both library roots and `quarantine/` find no import
of the duplicate. The retirement table's former consumer
`Sheaf.CategoryTheory.CoproductTruncationCouple` has already been retired;
the current sole DAG parent, `lem-pc-coproduct-truncation-couple`, points to
`WeilConjectures.CategoryTheory.CoproductTruncationCouple`. Its proof imports
and applies the adopted individual-couple theorem, so the dependency is retained
and does not require a parent edit. The unit's realized lists are empty.
There is no rework/quarantine row for the item.

Server verification through `lcompile.py` compiles the adopted module verbatim
and the adopted coproduct consumer verbatim. An independent scratch theorem
with the old public signature applies the adopted theorem directly, checking
the elaborated interface. Axiom probes of the individual and coproduct theorems
report only `propext`, `Classical.choice`, and `Quot.sound`. Both source modules
contain zero holes. All scratch checks are outside the delivery's `lean/` tree.

## Status

landed 20261020T233225-L-908495 2026-10-20 (merge of deliver/U3/Sheaf.CategoryTheory.NaturalTruncationCouple)
