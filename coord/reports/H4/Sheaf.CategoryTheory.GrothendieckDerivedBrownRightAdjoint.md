## What changed

Replaced the sole sorry in `Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint`
with a complete Lean proof of the Tag 0F5Y argument from its cohomological
representability input, Tag 0F5X. The original signature and docstring are unchanged.
The proof installs the standard opposite triangulated structures and opposite
exactness of F locally, forms `H = F.op ⋙ preadditiveYoneda.obj Y`, infers its homologicality,
proves preservation of every discrete product from `hF`, and invokes Mathlib's
partial-adjoint criterion after establishing objectwise representability.

Added one proof-only import of
`Sheaf.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability` and
three proof-only Mathlib imports: `Adjunction.PartialAdjoint`,
`Limits.Preserves.Opposites`, and `Triangulated.Opposite.Functor`.
The new module states the general cohomological representability input with its
own complete source proof in words. Both modules compile locally with no warnings.

The remaining lemma is a strict part of the source argument: it has no target
category D, functor F, or adjunction conclusion. The Hom-functor construction,
verification of its hypotheses, and assembly into a right adjoint are all proved
in the item's module. The original unit's route is preserved.

## Proved and sorry left

Closed: `CategoryTheory.grothendieckDerived_hasRightAdjoint`
(node `lem-grothendieck-derived-brown-right-adjoint`), 1 of 1 original holes.
The item's module has no sorry left.

Added: `CategoryTheory.grothendieckDerived_cohomological_isRepresentable`
(node `lem-grothendieck-derived-brown-cohomological-representability`), exactly
`:= by sorry` in its separate new module. This delivery is a decomposition:
one upper hole closed and one lower hole added; net holes zero. The resulting
adjoint theorem still depends on that lower hole and is not claimed axiom-free.

## No longer needed

None. The original module had only its required statement import and its node
had no proof dependencies. Every added proof import is used. No existing node or
module is pruned. The compactly generated Brown theorems cannot replace this
argument without the absent compact-generation hypothesis on D(A); they were
searched and not imported into the item.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The parent's single proof step contained the
entire Gabriel-Popescu/Brown/summand argument but had no declared proof dependency;
Tag 0F5X is now isolated as the actual next item. The smaller theorem does not
assert compact generation of D(A). Mathlib `IsHomological` implies additivity,
so no unexpressed additive hypothesis is needed.

Read Tags 0F5X and 0F5Y and the upstream `injectives.tex` section-brown directly.
The new statement includes all indexing sets in max(w,vA,vH), allowing the value
and derived Hom universes to differ via natural bijections (RepresentableBy).
Edge cases checked in the source argument: the zero functor is represented by
zero; empty coproducts/products and singleton indexing sets are included by the
unrestricted `∀ I`; no nonzero generator or compact generation of D(A) is assumed.
A representable Yoneda functor satisfies exactly this conclusion.

LeanSearch was unavailable (HTTP internal server error), not a negative search.
LeanFinder returned only Ext/HasExt-related results; Loogle returned zero matches;
Mathlib grep returned only unrelated subcanonical-site results. The full local
DAG/source search found the compactly generated results, with extra hypotheses.
Blueprint searches for Grothendieck Brown, representable, and 0F5X found no duplicate
of the proposed general cohomological theorem. No section I is present in the
current `coord/delivery-errors.md`; its existing stage-3 and relabelling rules
were checked against this decomposition.

## New nodes

`lem-grothendieck-derived-brown-cohomological-representability`, in
`dag/nodes/sec-smooth-purity/`, carries
`CategoryTheory.grothendieckDerived_cohomological_isRepresentable` in
`Sheaf.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability`.
It is the cohomological input, Tag 0F5X (`injectives-lemma-brown`), to the parent's
Tag 0F5Y argument. Its docstring and node contain the complete localization,
compact-generator representation, splitting, and Yoneda argument. Its single
remaining hole becomes the next proof item; no further nodes or interfaces were
changed and no change record is needed.

## Second reading by H4

1. Compared the delivered item module with the repository version. The theorem
   signature and existing declaration text are byte-for-byte unchanged; only
   proof-only imports and the proof body differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no
   compiler errors or warnings, no forbidden declarations, and no `sorry` in the
   item theorem. The only remaining `sorry` is the named theorem in the new
   module, with its source, proof description, and DAG node. Verdict: pass.
3. Checked the new representability statement against the source and existing
   Brown declarations. It is a strict cohomological input, has no target functor
   or adjunction conclusion, and its edge cases and universe convention are
   recorded in the report. No duplicate declaration was found. Verdict: pass.
4. Read the proof from the target downward. It uses the shortest available
   objectwise representability route and retains the unit's Tag 0F5X step; all
   added imports are used and no old dependency is pruned. Verdict: pass.
5. Compared the DAG proof steps, dependencies, origins, and Lean declarations
   with the delivered code. The parent now records the new representability node
   as its proof dependency, while the split node records its source proof and
   remaining hole. Verdict: pass.

Changed during this reading: added this section to satisfy the stage-3 report
contract. No Lean code, statement, definition, or DAG content was changed.
