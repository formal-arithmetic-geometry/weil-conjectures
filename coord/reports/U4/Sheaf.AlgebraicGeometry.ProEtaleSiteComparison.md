## What changed

Proved `AlgebraicGeometry.Scheme.preservesFiniteLimits_proEtaleSiteComparison`.
The proof establishes finite-limit preservation of the opposite left Kan extension by
pointwise evaluation, filteredness of the costructured-arrow categories, and the
filtered-colimit finite-limit theorem for types, then applies the constructed sheaf
pullback finite-limit instance. The unused planned imports were removed; the public
comparison definitions and the `ModuleCat` Abelian import remain.

The item's DAG node now records this shorter universe-general route and its actual proof
dependencies.
The public import pruning is recorded in `coord/changes/pro-etale-site-comparison-import-pruning.md`.

## Proved and sorry left

Holes closed: `AlgebraicGeometry.Scheme.preservesFiniteLimits_proEtaleSiteComparison`
(node `def-weil-pbc-site-comparison-morphism`). Holes added: none. No `sorry` remains in
the delivered module.

## No longer needed

Removed imports `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
`Sheaf.CategoryTheory.RingedSiteModules`, `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`,
`Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`, and
`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`.

The old proof dependencies removed from `proof_deps` are:

- `def-weil-etale-morphism`
- `def-weil-unramified-morphism`
- `def-weil-open-immersion`
- `def-weil-flat-morphism`
- `def-weil-weakly-etale-morphism`
- `def-pc-fibre-product`
- `lem-weil-pbc-fpqc-finer-than-etale`
- `lem-weil-pbc-adjunction-lifts-group-ring-objects`
- `lem-weil-pbc-sheaf-algebraic-structures-objects`
- `def-weil-sheaf-of-modules-category`
- `def-weil-pbc-constant-sheaf`
- `def-weil-pbc-sheafification`

Their planned intermediate arguments are replaced by the canonical upstream inclusion,
comparison adjunction and Mathlib APIs. No global module-pruning count is claimed;
the import-closure ledger determines that count.

## Where the brief, the DAG or earlier work was wrong

The original plan treated the set-valued finite-limit step as requiring a separate
small-site lemma. The actual sites have the larger universe, so the small-category
instance does not apply directly; the imported universe-general `lanEvaluationIsoColim'`
and pointwise filtered-colimit argument are required. No statement or definition was
changed.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The three declaration
   signatures are unchanged byte for byte; only the proof of
   `preservesFiniteLimits_proEtaleSiteComparison` and imports changed, as recorded in
   `coord/changes/pro-etale-site-comparison-import-pruning.md`. Verdict: pass.

2. Compiled the module and the sandbox import closure with `lcompile.py`. The module
   contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or
   `debug.skipKernelTC`. Axioms for all three declarations are only
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. Checked the finite-limit proof against the stated node and searched the library and
   Mathlib for an existing declaration. The proof uses the universe-general Kan
   extension evaluation and filtered-colimit route, and does not introduce a duplicate
   statement or a hollow definition. Verdict: pass.

4. Checked pruning and the unit route. The retained public comparison definitions and
   the `ModuleCat` Abelian import are used; the five listed imports are removed and
   recorded in the change record. The proof still realizes the comparison-morphism
   unit through the canonical sheaf pullback construction. Verdict: pass.

5. Checked that the DAG node's proof text, dependencies, origin, and Lean records agree
   with the delivered file, and that no new nodes or holes were introduced. Verdict:
   pass.

Changed after this reading: added this independent review record; no Lean or DAG
   changes were needed.

## Earlier second reading (a previous round; superseded)

Reserved for the independent U4 reader. The first reading found the retained public
signatures unchanged, the finite-limit proof compiled cleanly, and no new declaration
or axiom was introduced; the independent reader should verify the proof route, import
pruning, and revised node metadata.


## Second reading by U4

1. Compared the complete module against the repository version and checked all three
   declaration signatures byte for byte. Both definition bodies are unchanged; the only
   Lean changes are the finite-limit proof and five removed imports. The two removed
   public imports are declared in the change record. Independently enumerated its 17
   direct importers and verified every row, including all five named in the return of
   2026-10-16 05:31 UTC. Verdict: pass.

2. Compiled the module and the complete delivered Lean set using `lcompile.py`. Compiled
   a scratch copy with `#print axioms` for `proEtaleSiteComparison`,
   `preservesFiniteLimits_proEtaleSiteComparison` and `proEtaleSiteComparisonModules`:
   each has only `propext`, `Classical.choice` and `Quot.sound`. Scanned the module for
   forbidden declarations/options and holes: none. The two data definitions remain the
   explicit canonical adjunction constructions, with no arbitrary existence witness.
   Verdict: pass.

3. No statement was split off or added. Independently searched LeanFinder for the flat
   Kan-extension finite-limit theorem, Loogle for
   `lan_preservesFiniteLimits_of_preservesFiniteLimits`, Mathlib with `msearch.py grep`,
   and the upstream and Sheaf sources with `rg`. The Mathlib shortcut requires small
   categories; the upstream AB5 variant does not directly supply the set-valued instance.
   The delivered proof instead checks filteredness using `structuredArrowOpEquivalence`,
   evaluates via the universe-general `lanEvaluationIsoColim'`, and uses filtered
   colimits of sets. This works for all schemes, including the empty scheme, and handles
   the empty finite diagram because the comma categories are filtered (hence nonempty).
   Verdict: pass; no duplicate or replacement hole.

4. Read the inclusion, continuity and representable-flatness instances in the upstream
   pro-etale site module, and the constructed sheaf-pullback finite-limit instance in
   Mathlib. The retained public comparison-definitions import supplies the actual sites
   and constructions; ModuleCat.AB supplies coefficient-category structure used by the
   module adjunction definition. No proof-only public import remains. Enumerated every
   old proof dependency removed by the new route under `No longer needed` above.
   Read `dag/units/sk-thm-properbasechange.json`: its realized statement and three steps
   are the projective-line/reduction/torsion-assembly route. This supporting comparison
   construction changes none of them and bypasses no realized unit step. Verdict: pass.

5. Compared the node's changed fields against the repository: only `proof`, `proof_deps`
   and `proof_origin` change. Checked that `proof_deps` equals the step's `uses`, and
   that the Lean record still names all three unchanged declarations. The step correctly
   records the pointwise filtered-colimit route, canonical adjunction definitions and
   sheafification. Corrected its final description: the constructed-pullback instance
   directly composes limit preservation; this proof does not transfer it through an
   adjunction isomorphism. No new nodes are required. Verdict: pass after correction.

Changes from this second reading: corrected that DAG proof description, made the list
of removed proof dependencies explicit, and added this independent review. No Lean
repair was needed. Holes closed: one; holes added or split off: zero.
