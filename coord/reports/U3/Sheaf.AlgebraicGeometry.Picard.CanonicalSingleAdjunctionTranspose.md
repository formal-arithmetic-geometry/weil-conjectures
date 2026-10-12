## What changed

Proved `AlgebraicGeometry.Scheme.Modules.canonicalSingleAdjunctionTranspose` in
`Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose`, with its signature
and visibility unchanged. Added two private, fully proved helpers:
`single_complex_transpose` checks the underived single-complex identity degreewise;
`single_homotopy_transpose` descends it through the homotopy quotient. The main proof
uses the specified factorization of `exists_schemeDerivedAdjunction` and the unit law
for `leftAdjointUniq`. Updated the node's proof and proof origin to describe this
calculation. All three original public imports remain necessary for the statement.
The added proof elaboration settings are documented in
`coord/changes/U3-canonical-single-adjunction-proof-settings.md`; no importer-visible
interface changes and no downstream adaptations are needed.

Searches: Lean Finder found the single-functor and quotient comparison APIs; Loogle
found `Adjunction.homEquiv_naturality_right`; grep found
`singleMapHomologicalComplex` and the quotient-unit identity. Searches in Mathlib,
WeilConjectures, and Sheaf found no existing theorem stating this precise specialization.
The generic adjunction and single-complex APIs suffice without new dependencies.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.canonicalSingleAdjunctionTranspose`
(node `lem-pc-canonical-single-adjunction-transpose`).

Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
Both private helpers are fully proved. No statement is split off and no definition
or other module is changed. This is a proof from the existing declarations, rather
than a decomposition into new holed declarations.

The local single-file compiler passes without errors or warnings. The delivery dry
run performs the compiler and axiom probe checks; a probe timeout is reported by
the tool for the merge to recheck, rather than treated as an axiom result. This result still has the
existing dependencies of the chosen derived-category and adjunction constructions;
it does not claim that their whole transitive closure is sorry-free.

## No longer needed

None. No import, planned dependency node, or module is removed. The proof uses
`def-pc-derived-base-change-map`, `lem-pc-module-pullback-adjunction`, and the
constructions in `lem-pc-canonical-single-pullback-comparison` and
`lem-pc-canonical-single-direct-image-comparison`. It does not use the invertibility
theorems from the latter two modules. The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement or interface fault was found. The former proof description named the
counit law for `leftAdjointUniq`; the actual proof uses its unit law together with
naturality in the right argument. The docstring and node proof now describe that
calculation. Degree-zero identities are checked using the single-object isomorphisms;
all other degrees use the zero source, covering zero modules and empty schemes.

## Second reading by U3

1. **Unchanged visible declarations.** I compared the delivered module with the repository
   version. The public theorem signature and all existing declarations are byte-for-byte
   unchanged; only proof code, private helpers, elaboration settings, and explanatory text
   changed. The node records the same statement and proof route.

2. **Proof and axioms.** The module compiles with `lcompile.py` and contains no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The two private helpers and the
   target theorem are proved by category-theoretic rewriting. The degreewise helper handles
   degree zero by the single-object identities and all other degrees by the zero source; the
   homotopy helper descends through the quotient. No new public assumptions are used.

3. **Statements and searches.** No statement was split off. The target statement is unchanged,
   and the private helper statements are internal proof facts rather than importer-visible API.
   The worker's Mathlib, Lean Finder, and grep searches found no existing theorem duplicating the
   target specialization.

4. **Route and pruning.** The proof follows the unit route: it uses the selected derived
   adjunction factorization, the tensor pullback adjunction and `leftAdjointUniq`, then the
   canonical single pullback/direct-image comparisons. All three original public imports remain
   necessary, and no proof dependency or module can be pruned.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` match the code,
   including the degreewise and quotient transpose calculation and the unit law for
   `leftAdjointUniq`. The unit's realized route is unchanged.

I changed only the report section required for second reading; no Lean statement or definition
was altered.
