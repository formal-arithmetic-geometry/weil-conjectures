## What changed

The item theorem `HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi`
now has a real reduction using the existing henselian etale retraction and
finite-product-local theorems. The retraction is transported across `ULift` to
handle the different universes of the base and its test algebras. Module
finiteness is transferred through the product equivalence and its projections.
Integral contraction proves locality; Mathlib proves residue-field finiteness.

The new module `Sheaf.RingTheory.FiniteLocalHenselian` isolates only henselianity
of a module-finite algebra already assumed local. The former
`FiniteOverHenselianLocalProductCore` module and its new node were removed from
this delivery: omitting only residue-field finiteness postponed almost all of
the item's argument. Both existing etale-retraction/product-local imports are
retained as plain proof-only imports; the new helper import is also proof-only.
No existing declaration signature, definition, or public import was changed.

## Proved and sorry left

One of one original theorem bodies is filled:
`HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi`.
This is a conditional proof from the existing decomposition declarations and
`HenselianLocalRing.finite_local_henselian`, not a claim that its transitive
axiom closure is sorry-free.

One new named theorem remains `sorry`:
`HenselianLocalRing.finite_local_henselian`, node
`lem-weil-pbc-finite-local-henselian`, module
`Sheaf.RingTheory.FiniteLocalHenselian`. It has a source and a complete
componentwise idempotent-lifting proof in its docstring. There is no `sorry`
in the item's module and no definition is added.

## No longer needed

No original Lean import or original dependency module is pruned: both
`Sheaf.RingTheory.EtaleRetractionFiniteProductLocal` and
`Sheaf.RingTheory.HenselianEtaleRetraction` are used by the repaired proof.
The preliminary core module and node are withdrawn, not delivered.

Of the old `proof_deps`, `def-pc-field-extension` and
`def-weil-pbc-henselian-terminology` are removed from the proof dependency list;
they remain statement dependencies. All three old theorem proof dependencies
(henselian etale retraction, product-local decomposition, and finite-algebra
local radical) remain used. No unit realization is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The preliminary split into a core product-henselian theorem was insufficient:
the whole decomposition and henselianity argument remained unproved under a
new name. The second reader repaired that by carrying out decomposition,
finiteness, locality, and residue-field finiteness in Lean, leaving only
henselianity of a single finite local algebra open.

The existing etale retraction declaration uses one universe for both rings,
whereas the product-local criterion tests rings in `Type (max u v)`. The
`ULift` transport proves the required instance of the criterion without
changing that existing declaration or introducing another unproved retraction
statement. No target statement was changed.

## New nodes

`lem-weil-pbc-finite-local-henselian` states Stacks Tag 04GH (2), the henselianity
of a local module-finite algebra. Its proof decomposes finite algebras over
that local algebra using the old decomposition dependencies, then applies the
idempotent/simple-root equivalence. Its hypotheses exclude a zero local
algebra; the auxiliary finite algebras may be zero and are handled by the
empty product. Mathlib searches (LeanFinder, Loogle, and grep; LeanSearch unavailable) and the upstream
and project source search found no existing transfer declaration. No change
record is needed: all existing signatures are preserved.

## Second reading by C2

1. Compared the item module with the repository using `diff` and checked its
   declaration signature verbatim: unchanged. No existing definitions or
   public imports changed. The only extra statement is in its new module.
2. Compiled both delivered modules in import order through `lcompile.py`:
   clean, no warnings. Inspected for forbidden declarations and hollow
   definitions: none. Scratch-copy `#print axioms` for both declarations
   reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is expected from the named split and the still-open imported
   statements. Only the reported helper theorem has a textual `sorry`.
3. The finite-local-algebra statement is a strict part of the original
   argument, not another product-decomposition theorem. Checked the field
   case, A=R, finite nilpotent local algebras over a field, and zero auxiliary
   algebras. The idempotent-vector proof handles all these cases. Its new node
   and complete docstring match. Independent LeanFinder, Loogle, and grep
   searches found no matching Mathlib lemma; project and upstream searches
   found no duplicate statement. LeanSearch returned an HTTP server error,
   recorded as unavailable. The Stacks source at
   https://stacks.math.columbia.edu/tag/04GH confirms the helper as clause (2).
4. The repaired proof takes the existing decomposition route before the new
   helper. All proof imports are plain `import`; public imports serve the
   original statement. The no-longer-needed section lists every removed old
   proof dependency. `dag/units/sk-thm-iff.json` realizes its statement and step
   with `lemma-weil-pbc-property-iff-acyclicity`; this subordinate ring-theoretic
   proof preserves that route and the same generic decomposition tools.
5. The item's `proof`, `proof_deps`, and `proof_origin` describe the Lean
   reduction, including the universe transport and Mathlib finiteness steps.
   The new node records the remaining henselianity argument, source, searches,
   creation, blueprint ancestry, unit, and verbatim Lean signature.

Second reading changed the near-restatement split into a genuine reduction,
restored the two used decomposition imports, isolated finite-local
henselianity, repaired node dependencies, and corrected this report.
