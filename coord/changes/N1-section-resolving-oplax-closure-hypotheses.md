# section_resolving_oplax_closure

## Reason

The previous split omitted its parent's three resolving hypotheses. It asserted
flat-term K-flat pullback for arbitrary input complexes. For identity pullback,
Λ the discrete condensed integers, and a nonempty geometric point, take the
constant Z/2 module in degree zero. Multiplication by 2 is injective on the
constant Z module but becomes zero after tensoring with Z/2, so that term is not
flat. Stacks Tag 0G7E explicitly assumes both K-flatness and flat terms; the proof
of Tag 07A4 resolves its inputs before invoking closure. The parent already
quantifies objects of the resolving full subcategory.

## Old

```lean
theorem section_resolving_oplax_closure {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q H : CochainComplex (modules Λ Y) ℤ) :
    ResolvingClosure Λ f P Q H
```

## New

```lean
theorem section_resolving_oplax_closure {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q H : CochainComplex (modules Λ Y) ℤ)
    (hP : KFlatSectionComparison.sectionResolving Λ Y P)
    (hQ : KFlatSectionComparison.sectionResolving Λ Y Q)
    (hH : KFlatSectionComparison.sectionResolving Λ Y H) :
    ResolvingClosure Λ f P Q H
```

The corrected theorem is proved from existing total-tensor closure, the algebraic
presentation of pro-etale section pullback, and K-flat and flat inverse-image
preservation. No definitions, target statements, public imports or attributes
change. The item node records the correction and the actual proof dependencies.
No unit statement or unit proof route changes.

## Users

`tools/downstream.py Sheaf.Paper.SectionResolvingOplaxClosure --uses
section_resolving_oplax_closure` reports exactly the following two users. A source
search finds the same two occurrences. There is one direct importer.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SectionResolvingOplaxClosure | N1 | Restore the missing input hypotheses and prove the corrected closure assertion. |
| Sheaf.Paper.SectionResolvingOplaxModelEdges | unclaimed | Pass the existing P.property, Q.property and H.property at the sole call; all public signatures stay identical. |

The sole DAG citer is lem-pd-section-resolving-oplax-model-edges. It already
assumes resolving inputs and remains true verbatim. Every further downstream
module sees the same model-edges statement. No target uses the corrected lemma
in a definition, so no target meaning changes.

Compatibility check of the original direct importer failed at line 63:
Application type mismatch, since the unapplied closure theorem has type
sectionResolving P → sectionResolving Q → sectionResolving H → ResolvingClosure,
but And.intro expects ResolvingClosure. The adaptation supplies exactly those
three proofs, with no other edits to that module. The final two-file compile
passed: closure in 16.8 s, adapted model-edges in 7.4 s.

## Status

landed 20261027T034714-L-3677009 2026-10-27 (merge of deliver/N1/Sheaf.Paper.SectionResolvingOplaxClosure)
