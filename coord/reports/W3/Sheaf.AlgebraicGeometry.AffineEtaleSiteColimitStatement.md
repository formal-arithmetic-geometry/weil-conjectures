## What changed

Proved AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit in
Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement, with its signature unchanged.
The proof follows the four recorded steps: coherent base change; object and finite-cover
descent; direct map descent and eventual equality from scheme pullback descent; assembly
with exists_affineEtale_colimit_presentation_finite. Both morphism clauses are proved in
this file, without new intermediate holes. The descended stage map is constructed by
IsPullback.lift. Updated the node's proof and proof_origin; proof_deps are unchanged,
because all six recorded dependencies are used. The unit sk-thm-p1 and its realized
statement and steps stay unchanged.

Replaced broad public imports with the smaller statement APIs, and removed unused proof
imports. Change record: coord/changes/affine-etale-site-colimit-proof-imports.md.
No other library module is edited. Added one theorem-local elaborator transparency option
for the existing over-category and full-subcategory maps.

Validation: the item compiles cleanly through lcompile.py in about 12 seconds. The sole
direct importer, Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing, compiles
unchanged against the sandbox's compiled item in about 12 seconds. Its source copy was
removed from the delivered lean/ directory after this check. The delivery dry run is the
final validation.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit
(lem-weil-pbc-affine-etale-site-colimit): 1 of 1 original holes.
Added: none. Left in the item: none. Split off: none.

This is a stage-3 proof from existing statements. It does not complete the entire
transitive dependency closure: the existing
AlgebraicGeometry.Scheme.exists_affineEtale_colimit_presentation_finite in
Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentationFinite still has its own sorry,
is unchanged here, and remains its current holder's item.

The finite-presentation hypotheses are established explicitly: etaleness gives local
finite presentation, affine domains give compactness and quasi-separatedness, and the
quasi-separated base gives quasi-compactness of the structure morphisms. Both 01ZM
lemmas are applied with precisely these hypotheses. The two pullback projections prove
the comparison formula and stage equality. Finite-cover descent, including Fin 0, is
passed through unchanged. Empty affine schemes and a singleton directed preorder need
no strengthened assumptions or special exclusions.

## No longer needed

Removed direct imports:

- Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit: withdrawn empty module.
- Sheaf.AlgebraicGeometry.FullAffineEtaleTopos: replaced by FullAffineEtaleSite;
  its cohomology declarations are not used directly in this statement or proof.
- Sheaf.AlgebraicGeometry.LimitAffineTransition: no limit-existence theorem is needed;
  a limiting cone is already supplied, and the actual descent dependency supplies
  the Mathlib facts needed about affine transitions.
- Sheaf.CategoryTheory.SiteSystemStrictification: no direct use; strictification is
  supplied by the existing finite colimit presentation theorem.
- Sheaf.CategoryTheory.ColimitSites: no direct use; ArrowsFunctor supplies Cat.arrows
  in the statement. Colimit-site theory remains part of the presentation item's work.
- Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentation: withdrawn empty module;
  the existing finite version is used instead.

No direct work is needed here on lem-weil-pbc-limit-affine-transition,
lem-weil-pbc-site-system-strictification, or lem-weil-pbc-colimit-of-sites. These are
removed direct import edges, not claims of global unreachability: the nodes may remain
needed by other modules and by the finite presentation theorem. No recorded proof
dependency of this item is pruned; all six are used. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old proof_origin described an earlier withdrawal rather than the proof of this
restored statement. Updated it to the actual argument. The fourth proof step and the
existing docstring refer to the old presentation theorem name; the correct dependency
is exists_affineEtale_colimit_presentation_finite, already attached to that dependency's
node. The earlier imports retained both withdrawn empty packages and unused broad APIs.

The mathematical plan is otherwise sound. Read the qcqs paragraph of
https://stacks.math.columbia.edu/tag/0EYL and parts (2), (3) of
https://stacks.math.columbia.edu/tag/01ZM. The local literature source named by the node
is absent here, so those primary-source pages were used for checking. Searches:
msearch.py LeanFinder for morphism descent along affine-transition inverse limits;
Loogle for the exact 01ZM declaration (no indexed match); msearch.py grep and local rg
through Sheaf, WeilConjectures and Mathlib. The local library's existing 01ZM declarations
give the direct proof. No new nodes are needed.

The cached downstream inventory repeatedly restarted while the shared origin advanced
and waited for its cache lock. The initial tools/downstream.py run succeeded; the change
record's complete user table was regenerated from the same source-import graph using
the project's lexer without the cache. No project tool was edited.

## Second reading by W3

1. **Signatures and accidental changes.** Compared the delivered module with the
   repository version. The theorem declaration is byte-for-byte unchanged; only imports,
   comments, transparency options, and the proof differ. No other existing declaration or
   target statement changed. Verdict: pass.
2. **Proof and axioms.** Compiled the module and all sandbox modules with `lcompile.py`.
   There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions in
   the delivered module. The theorem's only `sorryAx` comes from its still-open imported
   dependency theorems; no new hole was introduced. Verdict: pass.
3. **Split statements.** No theorem was split off and no new node or statement was added.
   The existing node's statement and six proof dependencies match the proof route, and the
   finite presentation declaration used in the final step is the declaration recorded by
   the existing presentation node. Verdict: pass.
4. **Shortest route and pruning.** The proof uses the existing base-change, descent,
   pullback-limit, finite-presentation, and finite-colimit declarations. Removed imports
   are listed above and are not needed by the statement or proof; the unit `sk-thm-p1` and
   its realized route remain unchanged. Verdict: pass.
5. **DAG agreement.** The node records the four proof steps, their dependencies, and the
   updated proof origin. The source and edge-case checks in the report cover empty finite
   covers and singleton directed systems. Verdict: pass.

Changed in this reading: appended this review record only; no Lean, DAG, or change-record
repair was necessary.
