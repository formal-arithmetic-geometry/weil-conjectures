## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.ProEt.qcqs_finite_family_geometry` with a complete proof.
The declaration's statement, universes, and existing public imports are unchanged.

The proof combines `qcqs_site_limits`, Mathlib's pro-etale subcanonical instance,
and `finite_coproduct_evaluation`, exactly along the existing DAG route. Affine
objects are qcqs by Mathlib instances. For each slice, the scheme preservation
provided by `qcqs_site_limits` is reassociated using `Over.post_comp`. The remaining
factor is the postcomposition of the fully faithful pro-etale forgetful functor,
followed by the iterated-slice equivalence, so it reflects finite limits.
`preservesFiniteLimits_of_reflects_of_preserves` gives preservation by the slice
inclusion. The coproduct witness and all its clauses are passed through together,
including naturality and the empty-family clause.

Added a declaration-scoped `linter.unusedVariables false` option: the existing
statement names the hypotheses `hqc` and `hqs`, which do not occur in its existential
conclusion. This avoids warnings without editing the statement. No file-level
option, public interface, definition, or other module changed. The second reader
also made the existing node's first proof step describe the slice-reflection
argument explicitly; its dependencies and statement are unchanged.

Validation: the module compiles alone through `lcompile.py` without diagnostics.
LeanFinder and Loogle found the reflection lemma, and source searches checked
`Over.post_comp`, the fully faithful postcomposition instances, the iterated-slice
equivalence, affine qcqs instances, and pro-etale subcanonicity. Searches of both
library roots found no duplicate of the target theorem.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.ProEt.qcqs_finite_family_geometry`
(node `lem-weil-pbc-proetale-qcqs-finite-family-geometry`), one of one original holes.

No `sorry` remains in the item; no holes or declarations were added elsewhere.
The proof uses the existing named statements
`AlgebraicGeometry.Scheme.ProEt.qcqs_site_limits` and
`AlgebraicGeometry.Scheme.ProEt.finite_coproduct_evaluation`, which remain upstream
proof obligations in their own modules. This delivery proves the planned
combination from those existing statements, rather than closing those dependencies.

## No longer needed

None. Both existing imports are needed by the public statement and their named
theorems are used in its proof. All three planned proof-dependency nodes remain
needed (subcanonicity is supplied directly by Mathlib). The optional finite-limits
clause over a qcqs base in `qcqs_site_limits` is unused; the dependency itself is
still needed and is not pruned.

## Where the brief, the DAG or earlier work was wrong

The site-limits theorem does not explicitly include preservation by the slice
inclusion into the pro-etale site, although the target does. Its stated preservation
in schemes implies this by reflection through fully faithful postcomposition and
the iterated-slice equivalence. This gap required only the Mathlib argument above;
no new statement, dependency node, or change to the planned route was necessary.

## Second reading by C4

1. **Interface: pass.** Compared the complete module with the repository using
   `diff -u`, and checked the theorem signature byte for byte in Python. The only
   Lean changes are its proof and the declaration-scoped unused-variable linter
   option. Universes, public imports, docstrings, visibility, hypotheses, and all
   conclusion clauses are unchanged. No definition or other module is delivered.
2. **Proof and trust: pass.** Compiled the delivered module with `lcompile.py`
   without errors or warnings. Scanned the complete source: no `sorry`, forbidden
   declaration, or new data definition. A scratch copy with `#print axioms` for
   the target and its two project dependencies reports only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected from
   the existing `qcqs_site_limits` and `finite_coproduct_evaluation` holes; this
   delivery removes its own hole and introduces none. Checked affine qcqs and
   subcanonical instances directly in Mathlib. The slice step uses full
   faithfulness and the iterated-slice equivalence to reflect finite limits;
   `Over.post_comp` gives exactly the preserved composite from the dependency.
3. **Split statements: pass, none.** No statement or hole was split off, and no
   arbitrary witness is turned into a definition. The coproduct witness, common
   coprojections, naturality, and empty-family assertions are passed through
   together from the existing coproduct theorem, without excluding empty schemes
   or empty index types.
4. **Route and pruning: pass.** Read both dependency modules and the unit
   `sk-thm-properbasechange`, including `realized`. The proof uses precisely the
   existing planned route: site limits, Mathlib subcanonicity, finite coproduct
   evaluation. Independent LeanFinder search for detection of finite-limit
   preservation through a fully faithful functor found the Mathlib lemma already
   used. Source searches in both library roots found no shorter existing theorem
   providing this conjunction. Both public imports provide names used in the
   signature and their project theorems are used in the proof. No old proof
   dependency is unused, so `No longer needed: None` is complete; the unit route
   and its `realized` record are preserved.
5. **DAG: pass after clarification.** Read the item node and all three proof
   dependencies. The existing dependency list matches the two explicit theorem
   applications and the Mathlib subcanonical leaf. The cited Stacks source and
   `proof_origin` still describe the mathematical route. Updated only the first
   `proof` step to record the actual Mathlib reflection argument, rather than
   leaving preservation by the slice inclusion implicit. No statement, dependency,
   unit, source, or Lean record changed; no new node or change record is needed.

Second-reading changes: clarified the existing node's first proof step and added
this review. The Lean proof needed no repair. Closed one original hole, added
zero holes; the two imported project obligations remain open.
