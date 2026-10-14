## What changed

Added a module documentation note identifying upstream review #1428. The current
repository already has the unpadded witness conclusion and its complete proof;
this delivery changes no signature, definition, proof, or import. The queued
repair is already satisfied by that existing implementation.

## Proved and sorry left

Holes closed by this delivery: none (0). Holes added: none (0). No sorries remain
in this module. Both existing theorems are fully proved:
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` and
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`.
The explicit scratch-copy `#print axioms` checks for both report only `propext`,
`Classical.choice`, and `Quot.sound`. This is a review of an already completed
repair, not new proof progress or a decomposition.

## No longer needed

None. The witness uses `lem-sc-ext-epi-effacement`, and the final theorem uses
`lem-sc-presheaf-free-ext-local-killing-witness`; these are exactly their existing
`proof_deps`. No modules or dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The repair queue still names the padded witness interface from upstream review
#1428, but the checked-out repository already contains the corrected conclusion,
complete proof, and matching DAG statement-change record. No further interface
change or change record is needed in this delivery.

## New nodes

None.

## Second reading by J3

1. PASS: compared the complete module with the repository by `diff`. Only the
   module documentation note differs. Every existing signature, definition,
   visibility, proof, and import is byte-for-byte unchanged.
2. PASS: compiled the delivered module using `lcompile.py` with no errors or
   warnings. Searched for forbidden declarations and sorry tokens: none. A
   scratch copy with `#print axioms` for both public theorems compiled and showed
   only `propext`, `Classical.choice`, and `Quot.sound`. The private helpers use
   genuine subtype and free-group constructions; no data is chosen from an
   unproved existence theorem.
3. PASS: no new or remaining split-off statements. The existing witness theorem
   has a complete proof, so the final theorem's application of it is not a
   relocation of a hole. Checked the empty-generator case (the constructed
   subtype is empty), zero classes, and degree one: the argument uses only
   positivity and works in each case; degree zero is correctly excluded.
4. PASS: read the proof top-down and searched Mathlib and both library roots for
   local-surjectivity and cover-lifting alternatives, including a fresh msearch
   grep query. Mathlib's general epi/local-surjectivity equivalence has additional
   concrete-sheafification hypotheses; the image-subsheaf argument here works
   directly with the stated small-value-universe hypotheses. The two public
   imports supply names in public signatures; ExtEpiEffacement is correctly a
   proof-only import. Both old proof dependencies remain used. The unit
   `sk-prop-cd` has no realized attachment to these nodes, and no unit route or
   record changed.
5. PASS: read both node records and their proof/proof_deps/proof_origin. They
   describe epi effacement, the locally generated abelian image, the explicit
   generator-lifting presheaf, the free/sheafification lift, and Ext associativity
   exactly as written in Lean. The recorded Lean statements match the unpadded
   signatures. No new nodes require checking.

Second reading changed only the report: corrected its progress accounting and
recorded the independent review. No proof repair was necessary.
