## What changed

Proved `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_ratFunc`
without changing its signature, universe, field hypotheses, or definition of local torsion.
The source library already proves this blueprint node as
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_one_ratFunc` in
`WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension`.
Its conclusion uses `Sheaf.H`. Apply it to each torsion sheaf and degree, then use
`AlgebraicGeometry.Scheme.nonempty_sheafH_extDerivedIso` to transfer subsingletonness
through the injective inverse of the comparison isomorphism. Both modules are
proof-only imports; the three public imports are unchanged.

Updated the existing node's proof, proof dependencies and proof origin to record this
reuse and comparison. An existing proof of this node is not represented by a new
self-dependency. The source theorem itself follows the prescribed curve bound,
purely inseparable base change, and affine-limit route, using nonempty affine opens
of the affine line. The unit record `sk-prop-sf-cbc` has no realized steps that this
reuse bypasses. No declarations, definitions, or statements outside this item changed.

Validation: the file compiles cleanly through `lcompile.py`. Separate axiom probes
of the source rational-function theorem and the comparison theorem both print only
`propext`, `Classical.choice`, and `Quot.sound`. Import-direction checks accept both
new imports. The required delivery dry run is run after this report is written.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_ratFunc`
(node `lem-sc-one-variable-field-cd`).

Added 0 holes. Split off 0 statements. No `sorry` remains in the item or any new
module (there are no new modules). This is proof reuse and comparison, not a
new decomposition. Both imported results pass the standard-axiom check.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.CategoryTheory.MorphismProperty.Limits`
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
- `Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit`

The item no longer needs these as separate direct proof-dependency nodes:
`lem-weil-pbc-spec-colimit-limit`, `lem-weil-pbc-affine-scheme-qcqs`,
`thm-weil-pbc-universal-homeomorphism-invariance`,
`def-weil-universal-homeomorphism`, `lem-sc-arbitrary-curve-cd`, and
`lem-sc-cd-affine-limit`. The mathematical curve/base-change/limit facts are
already implemented in the reused source proof. `def-sc-etale-torsion-cd`
remains a statement dependency. Withdrew the old direct `tool_uses` entry
`thm-weil-pbc-universal-homeomorphism-invariance`; the generic derived comparison
is now the sole direct proof dependency.

The import closure of this item loses these five modules:
`Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension`,
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`,
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismIdentity`,
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismComposition`, and
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismPullback`.
This is an item-local closure comparison; other target branches may still use them.
The affine-limit module remains a transitive dependency through the source theorem.
No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The planned argument was already implemented in the source library. The missing
work here was the conversion between its `Sheaf.H` formulation and the derived
cohomology formulation. The existing public statement and all mathematical
hypotheses were correct. The full current-blueprint statement and proof at
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/` agree with the
older source cited by the node.

Searches run through `msearch.py`: LeanFinder for the torsion etale cohomological
dimension of the rational function field over a separably closed field returned
unrelated fraction-field and inseparability results; Loogle `RatFunc` returned
rational-function definitions; the msearch grep for the source theorem name had
zero Mathlib hits. Direct `rg` in `lean/WeilConjectures` found the exact source
theorem. Its complete signature and proof, the comparison theorem, the unit record,
and the original DAG proof were read before reuse.

## Second reading by F3

1. **Visible declarations: PASS.** Compared the delivered module and node with the
   shared repository using `diff`. The sole existing theorem's signature, universe,
   namespace, visibility, and three public imports are byte-for-byte unchanged.
   Only private proof imports and the theorem body change in Lean. The node changes
   only `proof`, `proof_deps`, `proof_origin`, and removal of the old `tool_uses`
   entry. No statement or definition change requires a change record.
2. **Proof and axioms: PASS.** Independently compiled the delivered file through
   `lcompile.py` without warnings or errors. Compiled a scratch copy containing
   `#print axioms` for the delivered theorem and both applied upstream theorems:
   all three print exactly `propext`, `Classical.choice`, and `Quot.sound`.
   No forbidden construct or `sorry` occurs in the delivered module. Read both
   cohomological-dimension definitions and the comparison signature: the torsion
   predicate, universe and inequality `1 < q` agree, and the inverse comparison
   injects the required derived cohomology into the known subsingleton. The proof
   eliminates existence of an isomorphism inside a proposition; it constructs no
   data from an unproved existence statement.
3. **Split statements: PASS (none).** There are no new declarations, nodes or
   residual holes to audit. Read the full source rational-function proof and the
   comparison proof, and searched the site's cohomological-dimension declarations
   under both spellings. The exact source theorem already supplies the geometric
   argument; no additional split or shorter bound-conversion theorem is needed.
   No new hypotheses or exceptional-field restrictions enter the argument;
   degree two and all larger degrees are covered uniformly.
4. **Route and pruning: PASS.** The source proof uses the affine-curve bound over
   a separably closed field, purely inseparable algebraic-closure descent, and
   the fraction-field inverse limit, as prescribed. The unit's `realized` statement
   and step lists are empty and no unit route is bypassed. The two new private
   imports supply the two declarations applied; the public imports supply the
   statement's notions. Independently recomputed the old and new item import
   closures: exactly the five modules listed above leave this item's closure.
   Every old proof dependency no longer directly used is listed under
   `## No longer needed`, including the definition retained as a statement
   dependency. These item-local removals assert no global target-closure count.
5. **DAG agreement: PASS.** Read the original and delivered node and the unit
   record. The two proof steps describe the actual upstream application and
   subsingleton transport; `proof_deps` is exactly the union of their `uses`.
   The reused theorem proves this same blueprint node, so no circular DAG
   self-edge is introduced. `proof_origin` identifies both actual sources.

Second-reading changes: appended this independent review and added a scratch-only
axiom probe. No Lean proof, import, signature, or node repair was necessary.
