## What changed

Completed `CategoryTheory.precise_vanishing` without changing its existing signature,
visibility, definitions, or public imports. The retained, proved comparison helper
`CategoryTheory.precise_vanishing_of_homotopy_zero` is in `PreciseVanishingCore`.
The second reader replaced the proposed remaining homotopy vanishing hole by a full
lower-truncation argument: `K.truncLE (n - 1) → K` is a quasi-isomorphism, every chain
map from `P` to this truncation is degreewise zero, and the comparison helper plus
cancellation of the localized truncation isomorphism gives the result.

Both added imports in the item are proof-only imports. In the new core module,
`DerivedCategory.Basic` supplies the public signature; `DerivedCategory.KProjective`
is a plain proof-only import. Removed the unused Terminal import and the disabled
haveI/letI linter; ordinary local instances suffice.

## Proved and sorry left

Original hole closed: `CategoryTheory.precise_vanishing`
(node `lem-pc-ring-precise-vanishing`), 1 of 1 original holes.
New proved helper: `CategoryTheory.precise_vanishing_of_homotopy_zero`
(node `lem-pc-ring-precise-vanishing-core`).
Holes added: none. Sorries left in all delivered modules: none.
The proposed `CategoryTheory.homotopy_precise_vanishing` and its node were removed,
not delivered as a renamed replacement hole. This is a proof, not a decomposition:
one original hole closed and zero added. No whole-library ledger measurement is claimed.

Both files compile cleanly through `lcompile.py`. Scratch-copy `#print axioms` for
both delivered theorems reports exactly `propext`, `Classical.choice`, `Quot.sound`.

## No longer needed

Of the original node's four proof dependencies, these are no longer used:
- `lem-sf-derived-truncation-triangle`;
- `lem-weil-pbc-hom-into-triangle-exact`;
- `lem-pc-ring-projective-into-acyclic-zero`.

`lem-pc-ring-derived-map-representative` remains used through the core comparison
node, whose proof names Mathlib's K-projective comparison bijection.
No import of the original item was removed: it imported only
`Mathlib.Algebra.Homology.DerivedCategory.Basic`. Removed the first worker's unused
`Mathlib.CategoryTheory.Limits.Shapes.Terminal` import from the new core module.
The three bypassed nodes are Mathlib-backed leaves, so no existing Sheaf module is
claimed globally pruned. Removed the proposed new homotopy-vanishing node and theorem.

## Where the brief, the DAG or earlier work was wrong

The previous report called all four old dependencies undeclared; each is actually
Mathlib-backed. The previous remaining theorem concluded `Qh.map g = 0`, not `g = 0`,
and under the comparison bijection was essentially the original vanishing problem.
It is now removed and the proof completed. The previous main node changed
`proof_deps` without updating the proof steps, and the new nodes depended on the
item's own statement. The core now has a self-contained statement and depends for
its signature only on the derived-category definition, avoiding a circular edge.
The proof steps and dependencies now describe the compiled proof.

Read [Stacks Tag 064D](https://stacks.math.columbia.edu/tag/064D), Lemma 13.19.10:
its hypotheses are bounded projective `P`, terms zero below `n`, and homology of
`K` zero at and above `n`; these are unchanged in Lean. The proof retains its
projective comparison and canonical lower truncation. Since the upper part is
acyclic, Mathlib directly identifies the lower-truncation inclusion as a
quasi-isomorphism; explicitly invoking the triangle's exact Hom sequence is unnecessary.

## New nodes

`lem-pc-ring-precise-vanishing-core`: the fully proved localization comparison wrapper,
with a self-contained bounded-projective hypothesis and the assumption that all
homotopy morphisms localize to zero. It retains the first worker's valid comparison
proof. No new unproved statement and no change record are needed.

Fresh searches with different queries used LeanFinder (null-homotopy), Loogle
(`CochainComplex.truncLE`), and grep (`Qh_map_bijective`,
`isKProjective_of_projective`, `quasiIso_ιTruncLE_iff`). They found the Mathlib tools
used in this proof. LeanSearch was attempted and returned Internal Server Error;
this is recorded as unavailable. Searches of `lean/Sheaf` and `lean/WeilConjectures`
found comparison applications, but no existing copy of the core wrapper.

## Second reading by T2

1. Compared the delivered item with the repository version using `diff` and an
   exact signature-string comparison: the existing `precise_vanishing` signature
   is byte-for-byte identical. No existing definition or public import changed.
   The new helper is additional API with no changes to existing callers. Verdict: pass.
2. Compiled both files in import order through the launcher, with no warnings or
   errors. Scanned both files for sorry and forbidden declarations; none remain.
   Scratch-copy axiom checks on both theorem names return only the three allowed
   axioms. No data is chosen from an unproved theorem. Verdict: pass.
3. Read the remaining proposed statement and rejected its near-restatement of the
   item. Replaced it with the complete proof and removed its node. The retained core
   wrapper is fully proved from the Mathlib bijection. Checked boundary i=n: the
   target truncation is zero there, while below n the source is zero. Zero P, zero K,
   empty support interval, and arbitrary negative n are covered by the same argument;
   no positive-degree assumption or enough-projectives assumption is introduced.
   Fresh searches are recorded above and in the sandbox search log. Verdict: pass.
4. The proof now uses the shortest found concrete truncation argument, retaining the
   first worker's correct comparison. Imports are minimal by role, and the three
   unused old dependencies are explicitly listed. Read
   `dag/units/sk-thm-picard-duality.json`: the item is a supporting node below the
   unit, not a node in its `realized.statement` or `realized.steps` (both are empty
   in this repository snapshot). No unit statement, route or realized record is
   changed; the lower-truncation step of Tag 064D is retained. Verdict: pass.
5. Updated the main node's proof steps, proof_deps and proof_origin to match the
   direct quasi-isomorphism proof. The core node cites the existing representative
   node, has a self-contained statement, correct signature text, source, creation
   fields, blueprint ancestry and refreshed searches. Removed the unused homotopy
   node. No other existing-node field is changed. Verdict: pass.

Second-reading changes: closed the remaining hole; removed its theorem and node;
fixed import visibility, an unused import and unnecessary linter suppression;
corrected DAG proof records, signature encoding and circular statement dependencies;
rewrote the report to name exactly what closed and what was pruned.
