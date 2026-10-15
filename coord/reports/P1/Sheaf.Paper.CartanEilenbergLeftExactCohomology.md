## What changed

Replaced the sole `sorry` in
`Sheaf.Paper.CartanEilenbergLeftExactCohomology` with a complete proof of
`CategoryTheory.cartanEilenberg_leftExact_cohomology`, preserving its signature.
Added proof-only imports of
`Mathlib.Algebra.Homology.ShortComplex.ShortExact` and
`Mathlib.CategoryTheory.Abelian.Exact`.

For each degree, the proof constructs the boundary inclusion into cycles and
splits the boundary–cycle–homology short exact sequence using injectivity of the
boundaries. It also splits the preceding cycle–term–boundary sequence using
injectivity of the preceding cycles. Applying the additive functor preserves
these splittings. Left exactness preserves the cycle kernel. The mapped split
cokernel, precomposed with the mapped split epimorphism onto boundaries, supplies
left homology data for the mapped complex. Its canonical homology isomorphism
satisfies the required equation by the homology-data projection identity and
monomorphism cancellation.

This is the node's existing three-step argument, with its second short exact
sequence used one degree earlier. The unit route and DAG dependencies are
unchanged; no node edit is needed.

Validation: the module compiles through `lcompile.py` without warnings.
The delivery dry run checks the declaration axioms and compilation again.

## Proved and sorry left

Closed: `CategoryTheory.cartanEilenberg_leftExact_cohomology`
(node `lem-sp-cart-eilenberg-left-exact-cohomology`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes remaining: none.
No decomposition, additional modules, or new statements.

## No longer needed

None. No existing imports removed, and no DAG nodes or modules bypassed.
The proof uses Mathlib directly and imports no additional Sheaf modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was needed. Boundedness is unnecessary
for this degreewise argument; the hypothesis remains in the unchanged statement
and its lower-bound witness is unpacked without further use. The node's proof already points to
Stacks Lemma 015J for the split-sequence calculation, while the existing module
and theorem docstrings cite Lemma 015I; these existing citations are preserved.

## Second reading by P1

Independent second reader, 2026-10-16. Verdict: pass on all five review points.

1. Compared the delivered module with the shared repository using `diff -u` and
   checked the text through the theorem's `:= by` byte for byte after excluding
   the two added import lines. The existing declaration signature, visibility,
   docstrings, and all definitions are unchanged. There are no other delivered
   modules, statement changes, change records, or forced adaptations.
2. Independently compiled the delivered module using `lcompile.py`: exit 0,
   no warnings. Compiled a scratch copy with
   `#print axioms CategoryTheory.cartanEilenberg_leftExact_cohomology`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
   Read the complete proof and checked for forbidden declarations and proof
   escapes: none. The kernel and cokernel universal properties are proved,
   and the final equation identifies the constructed isomorphism as required.
   All data comes from actual Mathlib constructions with proved properties;
   there is no arbitrary witness chosen from an unproved existence theorem.
3. No statements are split off and no new declarations or holes are added.
   Checked the degree indices: `prev q = q - 1`, and the second split sequence
   is used at degree `prev q`, giving an epimorphism onto precisely the incoming
   boundary. No argument assumes a nonzero differential or nonzero homology,
   so zero complexes and zero boundary or cycle objects cause no exception.
4. Repeated LeanFinder and Loogle searches using split-cokernel and additive
   splitting queries, and searched Mathlib and both library roots with `rg`.
   The relevant results are the splitting machinery already used by the proof;
   the general homology-preservation theorem requires preservation of cokernels
   not supplied by left exactness alone. No direct shorter theorem was found.
   Tested removal of each added proof-only import in scratch copies:
   without `ShortComplex.ShortExact`, `ShortExact` is unavailable; without
   `Abelian.Exact`, `Exact.isColimitImage` is unavailable. Both additions are
   necessary and correctly non-public. No old proof dependency or Sheaf import
   is bypassed, so `## No longer needed` is complete. Read the unit record
   `dag/units/sk-thm-picard-rr.json`: its `realized` fields are untouched and
   this argument does not bypass any realized statement or step.
5. Read node `lem-sp-cart-eilenberg-left-exact-cohomology`, its three definition
   dependencies and their Mathlib matches. Its three proof steps agree with
   the Lean: construct and split the two short exact sequences, map the
   splittings and preserve the cycle kernel, then identify the homology
   quotient canonically. `proof_deps` and `proof_origin` remain accurate.
   Confirmed the splitting argument in the proof of
   [Stacks Lemma 015J](https://stacks.math.columbia.edu/tag/015J).
   The existing 015I citation concerns the resolution construction; the report
   already distinguishes it from the 015J proof origin. No DAG edit is needed.

Changes made by the second reader: appended this independent review and its
validation evidence to `report.md`. No Lean or DAG changes were necessary.
The hole accounting remains: one original hole closed, zero added, zero left;
this is a complete proof, not a decomposition. Scratch checks are not delivered.
