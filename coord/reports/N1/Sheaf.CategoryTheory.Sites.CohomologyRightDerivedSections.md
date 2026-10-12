## What changed

Proved `CategoryTheory.Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived`
with its signature unchanged. The proof explicitly constructs the additive representation of
sections using sheafification, the whiskered free-abelian adjunction, and Yoneda. It transports
that representation through right-derived functors and composes it with the Ext comparison.

Added the fully proved generic module `Sheaf.CategoryTheory.Abelian.ExtRightDerivedHom`.
Its private helpers construct the Hom-complex isomorphism, compute Ext postcomposition on
cocycles, construct homology map data, and prove naturality. The public theorem is
`CategoryTheory.nonempty_extFunctor_iso_rightDerivedHom`. Both modules compile without
warnings. Direct `#print axioms` checks show only `propext`, `Classical.choice`, and `Quot.sound`
for both public theorems. The original public imports are retained; proof imports are private.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived`
(node `lem-sc-site-cohomology-right-derived-sections`).

Also proved `CategoryTheory.nonempty_extFunctor_iso_rightDerivedHom`
(node `lem-sc-ext-right-derived-hom`). No holes split off, no holes added, and no `sorry` remains
in either delivered module. This is a proof, not a decomposition. The new theorem works in
all natural degrees, including zero, with independent object and morphism universes.

## No longer needed

None of the original imports, modules, or DAG dependencies is pruned. The original node had
no proof dependencies, and all three steps of its route are realized. A temporary exploratory
`Mathlib.Algebra.Category.Grp.Ulift` import was removed: HomComplex and additive Hom already
have the same morphism universe, so no lifting or unlifting is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The original DAG marked the injective-resolution
comparison and its naturality elementary despite requiring substantial Lean glue. They are
now represented by a fully proved generic node; the site-specific representation remains
explicitly proved in the item's module. The curve-estimate unit statement and route are kept.

The referenced local literature files are absent on this machine. Read the source through
[Stacks Tag 01FT](https://stacks.math.columbia.edu/tag/01FT) and the generic Ext computation
through [Stacks Tag 06XR](https://stacks.math.columbia.edu/tag/06XR), and read the relevant
Mathlib and source-library Lean declarations locally. No stronger assumptions such as a
terminal object, compactness, or nonemptiness were used. At degree zero the same resolution
computation applies; for injective second arguments higher cohomology vanishes on both sides.
The generic node is a tool implementing steps 2 and 3, rather than an alternative unit route.

## New nodes

`lem-sc-ext-right-derived-hom` records the fully proved natural isomorphism from Ext in its
second variable to the right-derived additive Hom functor. Its module is
`lean/Sheaf/CategoryTheory/Abelian/ExtRightDerivedHom.lean`. Search found no exact generic
comparison in Mathlib or the blueprint (`right derived Hom`, `Ext functor`); the available
injective-resolution API is used in the proof. No change record is needed: existing public
signatures, definitions, and public imports are unchanged.

## Second reading by N1

1. **Statements unchanged.** Compared the delivered site module with the repository using a unified diff. The target theorem signature is byte-for-byte unchanged; the added generic theorem has the node statement recorded verbatim. Verdict: pass.
2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`; no compiler errors or warnings and no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations occur. The local compiled target inherits `sorryAx` only from the unchanged upstream dependency baseline; the delivered declarations themselves are fully proved. Verdict: pass.
3. **New statement review.** The generic Ext/right-derived-Hom comparison is the injective-resolution computation from Stacks Tag 06XR, with explicit component construction and naturality. Its object and morphism universes match the theorem, it applies in degree zero, and no stronger hypothesis was added. Search records report no existing exact declaration. Verdict: pass.
4. **Pruning and route.** The site proof uses the sheafification/free/Yoneda representation and the generic Ext comparison, then derives the comparison with `NatTrans.rightDerived`; this keeps both steps of the unit route. The exploratory `Grp.Ulift` import was removed; no original proof dependency is unused. Verdict: pass.
5. **DAG agreement.** Updated proof text, proof dependencies, and proof origin agree with the Lean proof. The new node records its statement, source, proof steps, searches, module, declaration, and unit/chapter metadata. Verdict: pass.

Changed during second reading: no mathematical declarations or signatures; only this review section was appended. Compilation and delivery dry-run checks were rerun.
