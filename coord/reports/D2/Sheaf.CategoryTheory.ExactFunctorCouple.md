## What changed

Proved `CategoryTheory.BigradedExactCouple.exactFunctor_couple` in
`Sheaf.CategoryTheory.ExactFunctorCouple`, with its statement byte-for-byte unchanged.
All new constructions and helpers are private. The mapped exact couple is built
componentwise using preservation of exact short complexes. Image, kernel and
cokernel comparisons give one derived step; recursive comparisons give every page
and its monic D inclusion. Normalization at D(0,n) and integer induction give the
colimit comparison. Image and cokernel preservation give the filtration and graded
comparisons. The existing proved `exactFunctor_halfPlane` supplies the limiting
and explicit large-page comparisons. Cancellation proves adjacent stable-page
naturality.

Added the proof-only `import all
WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits` to reuse its existing
private `alpha_iso_left` lemma. Updated the existing node's proof, proof dependencies
and proof origin to match these constructions; removed its unused couple-morphism
tool approval. No new node, exported helper, definition repair, statement change,
or consumer adaptation is needed. The public import is unchanged.

Change record: `coord/changes/D2-exact-functor-couple-proof-context.md` documents
the private-helper `variable`/`omit` commands classified by the static checker.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.BigradedExactCouple.exactFunctor_couple`
(node `lem-sp-exact-functor-couple`). Proved 1 of 1 original holes. Added 0 holes;
split off 0 statements. Every new private helper is proved, and there is no
`sorry` in the delivered module, including its definitions.

The server single-file compile passes without warnings. The existing signature
was compared byte-for-byte with the library source. All lines are at most 100
characters. The delivery preflight checks all declarations and their axioms.

## No longer needed

Removed the redundant direct proof imports:

- `WeilConjectures.CategoryTheory.ExactCouple`
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`
- `WeilConjectures.CategoryTheory.HalfPlaneConvergence`
- `WeilConjectures.CategoryTheory.PBCFiltration`
- `WeilConjectures.CategoryTheory.Abelian.Filtration`

The first four remain available through the unchanged public
`Sheaf.CategoryTheory.HalfPlaneConvergence` import. The last module's separate
`DecreasingFiltration` interface is unused: the exact-couple convergence API uses
`PBCDecreasingFiltration`. The filtration notion itself remains needed.

The unused approved tool `lem-sp-couple-morphism` and its
`Sheaf.CategoryTheory.ExactCoupleMorphism` module are unnecessary for this proof:
the explicit cross-category comparisons use preservation isomorphisms directly.
Its stale `tool_uses` entry is removed. No other node or transitive module is
claimed globally unreachable. All current proof dependencies are used, including
`lem-sp-exact-functor-half-plane` and the diagonal-colimits ingredient. The realized
unit route in `sk-thm-properbasechange` is preserved.

## Where the brief, the DAG or earlier work was wrong

The theorem was restored after the upstream synchronization, but its full proof
had been removed. The current upstream couple has explicit fields; constructing
it requires mapping all three zero-composition equations and all three exactness
equalities. Its derived-map equations are obtained from the unique `DerivedMaps`
chosen by `derived`, rather than from the removed helper names of the older
proof. The construction here uses the current interface throughout.

The existing DAG proof already describes the right mathematical route. Its
reference to the private diagonal alpha-isomorphism argument is now explicitly
recorded as `lem-sp-half-plane-diagonal-colimits`. No mathematical statement was
false or weakened. The finite-page construction treats page zero and every type
s; the colimit induction includes negative indices, and existing half-plane
lemmas supply the zero and stable-page cases.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
