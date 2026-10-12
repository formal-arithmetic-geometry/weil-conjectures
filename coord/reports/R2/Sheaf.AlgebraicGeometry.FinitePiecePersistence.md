## What changed

Replaced the only sorry in Sheaf.AlgebraicGeometry.FinitePiecePersistence with a complete
proof of AlgebraicGeometry.finitePiece_persistence_of_isIso_residueFieldMap. Its signature,
visibility, docstring and three imports are unchanged. Two fully proved private helpers
implement the field-tensor arguments of the existing plan: pullback_point_unique and
pullback_fst_residue_iso. No other library module is adapted.

The cartesian ambient square follows from IsPullback.paste_horiz_iff. Restricting to the
inverse-image open and pasting proves the cartesian square over U, and stability under
base change proves finiteness. Existence uses Scheme.exists_preimage_of_isPullback.
Uniqueness uses carrierEquiv and the fact that the tensor inclusion is an isomorphism
when the right base residue-field map is. The residue-field helper uses the existing
exists_residueField_equiv_ofPointTensor, its quotient-field clause and left-factor
compatibility. Composition with the original projection proves the remaining clauses.
The existing DAG node records these concrete implementations of its four steps, with
proof_deps pruned in the second reading. No unit statement or realized unit step is bypassed.

Searches through msearch.py: LeanFinder on unique points under residue-field-preserving
base change returned PullbackCarrier's tensor/point APIs; Loogle on residueFieldMap
returned composition and open-immersion instances; grep on residueFieldMap/isIso found
only the open-immersion instance. Read the dependency records and signatures, the unit
sk-thm-p1, and the landed import change for SpecFieldPointResidueField. The literature
files are absent in this clone; checked the official Stacks pages for Tags 02LK and 01JT:
https://stacks.math.columbia.edu/tag/02LK and https://stacks.math.columbia.edu/tag/01JT.

## Proved and sorry left

Closed: AlgebraicGeometry.finitePiece_persistence_of_isIso_residueFieldMap
(lem-weil-pbc-elementary-etale-finite-piece-persistence), 1 of 1 original holes.
Added holes: none. Sorries left in the item or added modules: none.
Both private helpers are proved without sorry. This is a proof, not a decomposition.
The local #print axioms check reports only propext, Classical.choice and Quot.sound.

## No longer needed

No imports removed. Pruned proof-dependency nodes:
lem-weil-pbc-open-fibre-product and def-weil-open-immersion. The direct restriction
square replaces the former construction; the proof does not use the latter definition.
No module becomes unused through removing an import in this delivery.
Mathlib.AlgebraicGeometry.Morphisms.Finite supplies finiteness and its base-change
instance, Mathlib.AlgebraicGeometry.ResidueField supplies the statement's maps and
composition laws, and Sheaf.AlgebraicGeometry.FibreProductPointResidueField supplies
the residue-field comparison used in the proof. No new modules are introduced.
The inverse-image restriction square implements the planned open-fibre-product step
directly rather than introducing its auxiliary open-immersion image construction.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The compatibility hypothesis hx is redundant in this
proof, but its binder and the entire public signature are preserved. The proof records
it locally to satisfy the unused-binder linter. Stacks 02LK states the final assertion
for elementary etale neighbourhoods; the existing generalized statement needs only
the residue-field-map isomorphism, as the tensor argument and the Lean proof confirm.


## Second reading by R2

1. Compared the complete module with the repository by diff. Pass: the existing
   public theorem signature, visibility and docstring are byte-for-byte unchanged;
   all three imports are unchanged. The only Lean additions are its proof and two
   proved private helpers. No definitions, public interfaces or targets changed.
2. Compiled the delivered module through lcompile.py --all, then compiled the scratch
   copy with #print axioms of the public theorem. Pass: no errors or warnings, no
   sorry, and precisely propext, Classical.choice and Quot.sound. Checked the entire
   file for forbidden constructs: none. The helpers construct no data from an
   unproved existence statement; all used residue-field comparisons are proved.
3. No statements were split off and no nodes added. Pass. Checked the helpers on the
   identity-base-change case and over spectra of fields: tensoring along an isomorphism
   leaves the left field unchanged, so both uniqueness and the residue-field result
   have the expected strength. Empty fibres do not occur in the main existence step,
   because v and u1 have equal image. The uniqueness helper only compares points
   with both projections equal; it does not incorrectly assert global injectivity.
4. Read the proof top down and the residue-field comparison it uses. Pass after
   pruning metadata: Mathlib pasting and restriction handle the square and finiteness;
   carrierEquiv handles points, and the existing proved Sheaf comparison handles
   residue fields. An independent LeanFinder query for base-change projection
   residue-field isomorphisms returned the same tensor APIs and an ideal-level fibre
   equivalence, not a shorter scheme-level theorem. Loogle's unqualified IsPullback
   query failed identifier resolution, so was not counted as a negative search.
   Searched lean/Sheaf and lean/WeilConjectures for equivalent residueFieldMap results;
   no replacement found. Both public Mathlib imports supply signature symbols, while
   the Sheaf proof-only import is already plain import. Read sk-thm-p1.realized:
   this item is below its realized unit steps, and none is bypassed.
5. Compared the node's proof, proof_deps and proof_origin with the Lean and read each
   dependency's Lean or Mathlib match. Pass after repair: the restriction square
   directly replaces the old open-fibre-product construction, so removed
   lem-weil-pbc-open-fibre-product and def-weil-open-immersion from proof_deps and
   step 2 uses, and rewrote that step to describe the universal property actually
   used. The remaining dependencies agree with the four proof steps.

Second reading changed only DAG route metadata and this report (including the
No longer needed list). The compiled Lean proof required no repair. Closed one
original hole, added zero holes; no decomposition.
