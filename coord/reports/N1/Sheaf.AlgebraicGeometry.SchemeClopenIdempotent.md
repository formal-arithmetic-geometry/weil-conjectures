## What changed

Replaced the sole sorry in `lean/Sheaf/AlgebraicGeometry/SchemeClopenIdempotent.lean`,
`AlgebraicGeometry.scheme_clopen_idempotent`, with a complete proof of every clause.
Added the proof-only import `Mathlib.Topology.Sheaves.CommRingCat`; the proof-only
import `WeilConjectures.Mathlib.RingTheory.LocalRing.Basic` was already present in the
repository. Statements, definitions and existing public imports are unchanged.

The proof follows the node's five steps. Idempotent germs are zero or one by the existing
local-ring lemma, identifying the nonzero locus with both the one locus and the basic open.
The complement is the locus of `1 - e`, giving closedness. Equality of loci forces equality
of germs and hence of sections. For a clopen set, glue `(1, 0)` using
`objSupIsoProdEqLocus`, with compatibility on the empty intersection proved by
`section_ext`. Compute the germs of the glued section, prove its idempotence by stalk
extensionality, and deduce surjectivity and the unique inverse with the required germ values.
Finally, use the ring homomorphism `appTop` and `preimage_basicOpen_top` for pullback.

The gluing construction and restriction calculations adapt the proved argument inside
`AlgebraicGeometry.Scheme.connectedSpace_iff_isIdempotentElem` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`; that module is not imported because only
its constituent lemmas are needed. The proof imposes no nonemptiness assumption. Empty
schemes and empty/full clopen subsets are handled by the same gluing and extensionality
arguments. Local rings at points are nontrivial, which justifies the one/nonzero equivalence.

## Proved and sorry left

Proved `AlgebraicGeometry.scheme_clopen_idempotent`
(node `lem-weil-pbc-scheme-clopen-idempotent`): all four conjunction components.
One of one original sorries removed. No sorry remains in the delivered module, and no new
statement or module with sorry was added. Local compilation passed without warnings.

## No longer needed

None. No original import was removed, and all six original proof dependencies remain used:
`def-pc-scheme`, `lem-weil-pbc-local-ring-idempotent-zero-one`,
`lem-weil-pbc-basic-open-function`, `lem-weil-pbc-sheaf-sections-determined-by-germs`,
`lem-weil-pbc-sheaf-disjoint-union-product`, and `lem-weil-pbc-basic-open-pullback`.
No new route replaces a unit statement or step; the existing DAG proof remains accurate.
The affine correspondence and affine-cover gluing modules remain unnecessary, as already
recorded by the original node's split report; they were not imported or proved here.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The brief correctly points to the proved source
argument: its gluing construction can be reused without the nonemptiness hypothesis needed
by that source theorem's connectedness conclusion. The on-disk blueprint Markdown path
recorded in the unit is absent on this machine; its complete statement, steps and realized
nodes were read from `dag/units/sk-thm-p1.json`.


## Second reading by N1

1. Compared the sole delivered module against the repository with `diff -u`. The existing
   definition, theorem signature, docstrings and public import are byte-for-byte unchanged.
   Only the proof and one proof-only import changed. No change record is needed. Verdict: pass.
2. Compiled the delivered file with `lcompile.py`, without errors or warnings. Inspected the
   entire proof and scanned for forbidden declarations and proof escapes: no sorry, axiom,
   unsafe, opaque, implemented_by, extern or kernel-check bypass is present. A scratch copy
   with `#print axioms` for both `idempotentOpen` and `scheme_clopen_idempotent` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Verdict: fully proved.
3. There are no split-off statements or new declarations to audit. The local helpers are
   proper parts of the argument, proved in place. Checked the empty-scheme case (germ
   extensionality is vacuous), empty/full clopens (the same empty-overlap gluing works), and
   zero/one germs (stalk nontriviality supplies `one_ne_zero`). Verdict: pass.
4. Read the upstream `Scheme.connectedSpace_iff_isIdempotentElem` proof and searched the
   scheme and sheaf sources for idempotent/clopen correspondence declarations. The upstream
   theorem supplies the same gluing argument inside its proof, not a reusable theorem of
   this signature; no shorter complete declaration was found. The proof uses the planned
   stalk, basic-open, sheaf-gluing and pullback route. Tested deletion of each proof-only
   import in scratch copies: the gluing API and local-ring lemma respectively become
   unavailable. The public Scheme import is needed by the signature. All six original
   proof dependencies are used, so `No longer needed: None` is complete. Read the unit
   `sk-thm-p1` and its `realized` fields: no unit statement or step is bypassed. Verdict: pass.
5. Read the item's node and its dependencies. Its five proof steps and six `proof_deps`
   match the Lean proof; `proof_origin` already records the same Stacks/stalk route and
   upstream construction. The minor choice to verify glued idempotence by germs rather
   than restriction injectivity uses the already-listed sheaf-extensionality dependency.
   No node change or new node is required. Verdict: pass.

Changed only this report: corrected the claim that the existing local-ring import was
newly added, and appended this second reading. The reviewed Lean proof needed no repair.
