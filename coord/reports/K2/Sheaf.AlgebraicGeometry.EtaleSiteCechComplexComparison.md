## What changed

Proved `AlgebraicGeometry.Scheme.nonempty_etale_siteCech_complex_iso` by specializing the
existing `CategoryTheory.SiteCechComplex.mathlib_complex_iso_exists` to `X.Etale`.
Added the proof-only import `Sheaf.CategoryTheory.SiteCechMathlibComparison`.
The original signature, public imports, and docstrings are unchanged. Updated the item's
DAG proof and proof dependencies to record the specialization. Both nodes belong to
`sk-thm-p1`; no unit statement or realized step is bypassed.

The existing generic module is copied unchanged into the sandbox solely because its
local compiled object was missing. It is not a source change or a new module in this
delivery. Compiling the sandbox in import order validates the specialization.

## Proved and sorry left

The item's sole original sorry is replaced by a complete Lean proof:
`AlgebraicGeometry.Scheme.nonempty_etale_siteCech_complex_iso`
(node `lem-weil-pbc-etale-site-cech-complex-comparison`). No sorry remains in the item,
and no new sorry is added.

The existing dependency `CategoryTheory.SiteCechComplex.mathlib_complex_iso_exists`
(node `lem-weil-pbc-site-cech-mathlib-comparison`) still has its original sorry.
The delivery is a proof from this existing general statement, not a claim of
transitive sorry-freedom. Its hypotheses fit: Mathlib supplies finite wide pullbacks
for the small etale category, and both the index and coefficient universes are `u+1`.
The generic statement has no nonempty-index, covering, or sheaf assumption, so its
specialization also handles empty families and degree zero without extra hypotheses.

## No longer needed

No imports removed and no module globally pruned. The original local construction of
product isomorphisms and differential compatibility is subsumed by the existing generic
comparison node. `def-weil-pbc-site-cech-complex` and `def-weil-pbc-cech-complex` are no
longer direct proof dependencies of this node; they remain statement dependencies and
are needed beneath the generic comparison. They are not claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The item's earlier search predates or missed the existing generic comparison module.
Repository search found it, and its exact signature specializes directly. The import
cycle checker permits the new import. LeanFinder found related Cech nerve isomorphisms
but no SiteCechComplex theorem; Loogle found only `cechComplexFunctor`; the requested
Mathlib grep query returned no hits. No new lemma or mathematical correction was needed.
The local compile initially reported the generic comparison's missing compiled object;
compiling an unchanged sandbox copy together with the item resolved this local issue.

## Second reading by K2

1. **Statement unchanged.** Compared the delivered module with the repository version; the theorem signature and public imports are unchanged except for the proof-only import.
2. **Proof validity.** Compiled both sandbox modules with `lcompile.py --all`; no errors or warnings, no new `sorry`, and the item proof is an exact specialization of `mathlib_complex_iso_exists`.
3. **Statements and dependencies.** No new theorem statements were added. The existing generic dependency is used with the correct finite-wide-pullback instance and universe parameters; the DAG proof and `proof_deps` match the Lean proof.
4. **Pruning and imports.** The generic comparison gives the shortest route and retains the unit route through `lem-weil-pbc-site-cech-mathlib-comparison`; the added import is proof-only and no unused imports remain.
5. **Nodes and unit.** The item node records the specialization, its origin, and dependencies; the unit `sk-thm-p1` and its realized route are preserved.

Changed only the item proof, added the proof-only import, and updated the item DAG proof metadata. No split-offs or statement changes were needed.
