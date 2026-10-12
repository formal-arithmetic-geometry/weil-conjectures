## What changed

`Normal.fixedField_purelyInseparable_and_galois` retains its exact original signature
and is proved by combining two new, fully proved component theorems. The new modules
are imported only for the proof. All original public imports are unchanged.

`Normal.fixedField_purelyInseparable` uses normal conjugacy to show that each fixed
element has a singleton set of distinct minimal-polynomial roots, then applies
Mathlib's separable-degree criterion for pure inseparability.
`Normal.fixedField_separable_normal` explicitly constructs the polynomial with the
finite set of distinct minimal-polynomial roots, proves its coefficients fixed,
and descends separability to the minimal polynomial over the fixed field.
Normality follows from the intermediate-field normal instance.

## Proved and sorry left

Original hole closed:

- `Normal.fixedField_purelyInseparable_and_galois`, node
  `lem-weil-pbc-normal-extension-purely-inseparable-then-galois`.

The second reading also closed both holes introduced in the first attempt:

- `Normal.fixedField_purelyInseparable`, node
  `lem-weil-pbc-normal-extension-fixed-field-purely-inseparable`.
- `Normal.fixedField_separable_normal`, node
  `lem-weil-pbc-normal-extension-fixed-field-separable-normal`.

No holes are added by this delivery and none remain in its three modules. This is a
complete proof of the item's one original theorem, not a decomposition. Relative to
the repository, one original hole is closed and zero are added. A scratch copy with
`#print axioms` for all three declarations reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

No original module import is removed, so no module is claimed globally pruned.
The new Galois component's unused public import
`Mathlib.FieldTheory.PurelyInseparable.Basic` was removed before delivery.

The parent's nine old direct proof dependencies are replaced by the two component
nodes. Three old dependencies remain used through those components:
`lem-weil-pbc-normal-extension-conjugate-by-automorphism`,
`lem-weil-pbc-normal-extension-normal-over-intermediate`, and
`lem-weil-pbc-distinct-linear-factors-separable`.

The following old nodes are no longer needed as proof dependencies of this route:

- `def-pc-field-extension`;
- `def-weil-pbc-separable-algebraic-extension`;
- `def-weil-algebraic-element`;
- `def-weil-pbc-finite-purely-inseparable-extension`;
- `def-pc-separable-polynomial`;
- `def-weil-polynomial-ring`.

Definitions needed to state the mathematics remain in `stmt_deps`; no deletion from
the global graph or target import closure is claimed. The Galois component also no
longer uses the conjugacy node: invariance of root equations suffices there.
The unit `sk-thm-p1` and all its `realized` statement and step nodes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The retained first attempt was a decomposition: one original hole was replaced by
two new component holes. Its report correctly acknowledged this, but both components
can be closed with existing Mathlib tools. The pure-inseparability proof needs no
characteristic-dependent coefficient argument. The separability proof needs no
transitivity of the automorphism action on roots, only invariance and finiteness.
Both component DAG routes have been updated to the actual proofs.

The repository's literature sources are not materialized on this machine. The reader
checked the source statements at https://stacks.math.columbia.edu/tag/030M and the
root-product argument at https://stacks.math.columbia.edu/tag/09I3. No source file,
contract, tool, or repository file was edited directly.

## New nodes

`lem-weil-pbc-normal-extension-fixed-field-purely-inseparable` records the proved
pure-inseparability component, with its singleton-root and separable-degree route.
`lem-weil-pbc-normal-extension-fixed-field-separable-normal` records the proved
separability/normality component, with the explicit root-product construction.
Neither is a restatement of the whole item. No change record or forced adaptation
is needed: existing signatures, definitions, and public imports are unchanged.

## Second reading by W2

1. Compared the delivered parent module with the repository using `diff -u`.
   Only its proof and two plain proof imports change. Its existing signature and
   docstring are byte for byte unchanged. No existing definition is changed; the
   two component modules and their nodes are new. Verdict: unchanged interface.
2. Compiled the three modules in import order through `lcompile.py --all`, without
   errors or warnings. Scanned for forbidden declarations and remaining holes.
   Checked all three declarations with `#print axioms` in a scratch copy; only the
   three permitted axioms occur. The polynomial over the fixed field is constructed
   by `Polynomial.toSubring`, not chosen from an unproved existence theorem.
   Verdict: complete kernel-checked proof, no holes or hollow definitions.
3. Read both component statements, docstrings, and nodes. Checked trivial extensions,
   characteristic zero, purely inseparable positive-characteristic extensions, and
   infinite normal extensions; finiteness is used only for an individual polynomial's
   root set. Ran independent LeanFinder, Loogle, and grep searches, with queries about
   invariant separable elements, finite orbits, separable products, and separable
   degree. Read the matching Mathlib tools and searched both Lean roots for existing
   statements. The fixed-field Galois instances found require a finite group and do
   not cover the item's infinite case. Verdict: true, nonduplicated components; both
   are now proved, so no split-off hole remains.
4. Read from the parent down to each component and took the shorter Mathlib route for
   pure inseparability. Removed the unused new-component import and recorded every
   former parent proof dependency above. Read `dag/units/sk-thm-p1.json`, including
   `realized`; this below-unit refinement bypasses none of its statement or steps.
   Verdict: shortest available reduction checked, unit route preserved.
5. Compared parent node changes: only `proof`, `proof_deps`, and `proof_origin` differ.
   Checked both new nodes' identifiers, source, statement dependencies, creation,
   blueprint provenance, chapter/unit, searches, and Lean signature records. Rewrote
   their proof steps and dependency unions to match the now-complete Lean proofs.
   Verdict: nodes agree with the Lean and remain acyclic.

Second reading changed: closed both component holes, shortened the pure-inseparability
route, removed an unused import and unnecessary component proof dependencies, and
updated proof docstrings, DAG routes, and this report. The parent's correct conjunction
proof was retained.
