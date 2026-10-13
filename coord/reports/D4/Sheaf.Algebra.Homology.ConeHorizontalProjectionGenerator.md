## What changed

Proved `HomologicalComplex₂.coneHorizontal_projection_generator_vanishing` with its
original signature, definitions and docstring unchanged. The source and target cone
block calculations use the signed shift differential, the tail differential identity,
and naturality of the column projection. Added proof-only imports of
`Sheaf.Algebra.Homology.HorizontalProjectionNaturality` and
`Sheaf.Algebra.Homology.HorizontalProjectionTailDifferential`, completing and reusing
the two fully proved helper modules already present in the earlier sandbox. Added their
DAG records and updated the generator node's proof route. Existing public imports stay
because the original statement uses the projection and summand definitions.

## Proved and sorry left

Closed the one original hole:
`HomologicalComplex₂.coneHorizontal_projection_generator_vanishing`
(`lem-sp-cone-horizontal-projection-generator-vanishing`).

The two new named theorems are fully proved:
`HomologicalComplex₂.horizontalProjection_naturality`
(`lem-sp-horizontal-projection-naturality`) and
`HomologicalComplex₂.horizontalProjection_tail_differential`
(`lem-sp-horizontal-projection-tail-differential`). Their private helpers and the
private cone block and successor transport helpers are also proved. No holes are left
in any delivered module; no holes were added or split off. All three modules compile
without warnings. The tail proof covers negative degree, indices past the diagonal,
index p, and indices strictly greater than p. Thus the cone result also covers n=-1,
n=p-1, p=0, and the extension-by-zero boundary without extra hypotheses.

## No longer needed

None of the original imports or modules can be removed: the original theorem statement
uses both `ConeHorizontalProjection` and `ConeHorizontalStepStable`. The latter node
is now needed only for its summand definition, not its stability theorem. The proof
uses the two new projection theorem modules, each with only the public imports its
statement needs. The original proof dependency `lem-sp-cone-horizontal-step-stable` is no longer
used as a stability theorem and is removed from the generator node's `proof_deps`.
Its module remains needed for `coneHorizontalSummand`, so no module is pruned. An exploratory duplicate
extended differential module was removed from the sandbox and is not delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left two complete projection helper proofs but no completed parent
proof, node records or report. These are completed here. The existing DAG plan was
mathematically correct; the new nodes record its separate naturality and differential
calculations. No signature or definition correction, forced adaptation, or unit-route
change is required. The unit's realized lists are empty, and no unit step is bypassed.
LeanSearch returned an internal server error for both new-node searches; the records
mark it unavailable. LeanFinder and Mathlib source searches supplied the component APIs.
The local literature tree is absent on this machine; Stacks Tag 012X was read from its
published page. The calculations are marked agent-written refinements of its first
filtration and signed E0 differential, not a claim that Stacks states the cone identity.

## New nodes

`lem-sp-horizontal-projection-naturality`:
`dag/nodes/sec-abelian-varieties/lem-sp-horizontal-projection-naturality.json`, realized
by `lean/Sheaf/Algebra/Homology/HorizontalProjectionNaturality.lean`. Naturality is
proved on total summands, conjugated by extension isomorphisms, and transported to
an arbitrary equal column degree. This is a proved tool, not a new open item.

`lem-sp-horizontal-projection-tail-differential`:
`dag/nodes/sec-abelian-varieties/lem-sp-horizontal-projection-tail-differential.json`,
realized by `lean/Sheaf/Algebra/Homology/HorizontalProjectionTailDifferential.lean`.
The proof kills the horizontal differential term and computes the surviving signed
vertical term, including zero and invalid summands. This is a proved tool, not a new
open item. No change records are needed: every existing public signature, definition,
visibility and public import is unchanged.


## Second reading by D4

1. Compared the item against the repository version and checked its existing theorem
   signature byte for byte with a script: unchanged. Existing definitions, visibility,
   docstring and public imports are unchanged. The only new imports of the item are
   proof-only imports. The two additional modules declare genuinely new proved lemmas;
   no change record or forced adaptation is needed. Verdict: pass.
2. Compiled all three modules locally in import order, without errors or warnings.
   Searched all delivered Lean sources for sorry, axiom, unsafe, opaque, extern and
   implemented_by: none. A scratch copy with `#print axioms` for the generator and both
   new public lemmas reports only propext, Classical.choice and Quot.sound. No hollow
   definitions or arbitrary witness constructions were introduced. Verdict: pass.
3. No statements are split off with sorry. Read both helper proofs and their complete
   docstrings: naturality follows on coproduct summands, and the differential identity
   follows by killing the horizontal term for h >= p and computing the vertical sign.
   Checked m < 0, h > m.toNat, h = p, h > p, p = 0, and the source boundary n = p-1;
   the explicit zero-inclusion branches cover invalid summands. Repeated LeanFinder
   search with “total complex column component commutes with map and vertical
   differential on upper filtration”, and searched repository Lean sources with
   projection/commutation/naturality/differential terms. Only component APIs or unrelated
   projections were found; no existing lemma replaces these project-specific helpers.
   Each helper is strictly one part of the cone calculation, not a renamed parent.
   Verdict: pass.
4. Read the parent from its two cone blocks downward. It uses existing Mathlib cone,
   shift, total-summand and degree-transport APIs, then the two fully proved helper
   calculations. All imports are needed by statements or proofs; new public imports
   expose only definitions used in the new statements. The original stability theorem
   is unused, although its summand definition remains necessary: corrected the
   No longer needed section to identify that removed proof dependency explicitly.
   Read dag/units/sk-prop-av-pqf-finite.json: its realized statement and step lists are
   empty, and this tool calculation replaces no realized unit step. Verdict: pass.
5. Read all three delivered nodes and compared their statements, proof steps and
   dependency unions with the Lean proofs. The generator records the block calculation,
   tail differential and naturality actually used; new nodes have source, proof origin,
   searches, creation, blueprint and Lean records. Read Stacks Tag 012X: the first
   filtration and signed E0 vertical differential agree with the source attribution;
   the cone calculation is correctly identified as an agent-written refinement.
   Verdict: pass.

Second reading changed only this report: clarified the removed old stability proof
edge and recorded the independent checks. No Lean or DAG repair was needed. One
original hole closed, zero added, zero split off; the two new helper lemmas are proved.
