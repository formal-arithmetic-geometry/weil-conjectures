## What changed

Added the proved theorem
`CategoryTheory.brownHypothesesFor_iff_compact_thick_generators` in the assigned
module. It reduces Brown compactness to compactness on any constructible finite-Tor
family whose thick envelope contains the constructible finite-Tor objects. It
uses the canonical inherited shift in the actual localizing full subcategory.
Generators may have arbitrary index universes and need not represent every
isomorphism class. All coproducts retain the fixed universe of the Brown bundle.

Reproved `CategoryTheory.brownHypothesesFor_iff_compact_representatives` from the
new criterion: lift the family to the full closure, and place every eligible
object into the thick envelope by the supplied representative isomorphism. This
criterion is already used by the supported finite-field assembly. No signature,
visibility or definition body changes. The arbitrary-field theorem is unchanged.

Added public import Mathlib.CategoryTheory.Triangulated.Generators because the new
statement uses its thick envelope. Added private proof import
WeilConjectures.CategoryTheory.CompactObjectsThick. Its complete existing proof
supplies closure of compact objects under shifts, triangles and retracts; Mathlib
supplies the thick-envelope universal property. Updated the representative node
and item proof route, and added one proved node. No source-library edits.

Change record: coord/changes/A7-brown-thick-generator-compactness.md.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
The sole direct sorry remains `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`. The new criterion and the revised representative-family
proof are complete. This is a proved part of the compactness assembly, not a
proof or holed decomposition of the disputed arbitrary-field assertion.

Validation: the final server single-file compile passed in 44.5 seconds, exit 0,
with no warnings. All 19 existing declaration signatures are unchanged, the original
disputed theorem is verbatim, and the direct hole count remains one. The delivery
tool performs the declaration-axiom probe and required preflight checks.

## No longer needed

The representative-family proof no longer repeats objectwise compactness transport
via the private compact_of_iso helper. Its node now uses the thick-generator
criterion and structural theorem. compact_of_iso remains required by the existing
objectwise Brown criterion, so it is retained. No whole module, import or declaration
is withdrawn. No module is claimed pruned from the targets' closure. The smallness,
structural, compactness and generation inputs of the finite-field assembly remain.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the sole remaining hole asserts Brown compactness for separated
finite-type schemes over arbitrary positive-characteristic fields. The supplied
compactness inputs require the algebraic closure in a FiniteFieldDatum, or an
explicit Ext bound. An arbitrary field does not supply those hypotheses. The
existing infinite-transcendence-degree Kummer-symbol counterexample is retained
as a natural-language diagnostic, not claimed as a formal field-cohomology proof.
The current consumers also assert arbitrary-field results, so simply restricting
the theorem to the supported finite-field case would not repair them. No false
compactness assertion, renamed hole or weakened target is introduced.

The prior representative criterion required every isomorphism class in its
hypothesis. For its formal compactness step, a thick-generating family suffices;
this is the precise generalization proved here and reused by that criterion.
The unit's route is retained: geometric compactness inputs still give compactness,
and the existing localizing orthogonality argument still gives generation.

Edge cases: zero objects are adjoined to the generating property so an empty family
has the correct thick envelope. The covering hypothesis then implies compactness
only for objects actually in that envelope. Repeated generators and arbitrary
index universes are allowed. Membership proofs of a full-subcategory object lie
in Prop, so compactness for the canonical lift is exactly compactness for every
lift in the unchanged representative criterion. No witness data is chosen from
an unproved existence theorem. The new proof uses no assumption of geometric
compactness beyond the explicit compactness premise.

## New nodes

`lem-sfb-brown-thick-generator-compactness-criterion` records the new proved
equivalence. The forward direction restricts the existing objectwise criterion;
the reverse direction applies compactObjects_isThick and Mathlib's universal
property of triangEnvelope, then the objectwise criterion. It has no sorry.
Sources: the current Brown unit, proof paragraphs 1--2, and Stacks Tag 09QH,
derived.tex, lemma-compact-objects-subcategory. Search of the entire blueprint
found no matching thick-generator Brown criterion. LeanSearch and LeanFinder
returned triangulated object-property and t-structure infrastructure. Loogle and
grep found triangEnvelope_le_iff, while direct project search found the existing
proved compactObjects_isThick; these are reused.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
