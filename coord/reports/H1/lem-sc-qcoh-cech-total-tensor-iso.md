Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-qcoh-cech-total-tensor-iso.json` (statement, split; no new nodes; Mathlib searches found no match)
- `citations.json` (empty because every proof step is elementary linear algebra from the stated field and complex definitions)

Attachments: none.

WANTED: none.

The item was not present as a declaration in the Lean source. The source is Varieties, Lemma `varieties-lemma-kunneth` (the field-linear algebra conclusion following the tensor-total Cech construction). The DAG and blueprint were searched for an existing complex Kunneth node; the only matching artifact was this same statement imported as an unsplit child of `lem-sc-picard-kunneth-qcoh`, so it was not duplicated.

## Review by H1

I checked the statement against the field-linear part of Varieties, Lemma `varieties-lemma-kunneth`: both complexes are bounded below, the tensor total differential has the Koszul sign, and the map sends the tensor of cohomology classes to the class of the tensor representative. I also searched the Lean source for the item id, Kunneth terminology, and the blueprint tag; no project declaration states it.

Step 1 reads the source's field-linear splitting argument. For each complex I explicitly introduced cycles and boundaries, chose complements over the field, and checked that the differential identifies each complement with the next boundary, producing a homology summand and contractible two-term summands. The bounded-below condition was checked where finite total-degree sums are used.

Step 2 expands the tensor of those direct-sum decompositions. Every summand containing a contractible factor is contracted by the signed tensor homotopy; the mixed differential terms cancel by the displayed Koszul sign. The homology summand has zero differential. This is a direct calculation from the decompositions in Step 1, so no additional node is cited.

Step 3 identifies the cohomology of the surviving summand degree by degree and checks that inclusion of chosen representatives is precisely the canonical map in the statement. The contractions imply it is an isomorphism. I tested the formulation on the zero complex, complexes concentrated in degree zero, and a two-term identity complex; all give the asserted map and isomorphism. No statement-only child was necessary, and no duplicate or Mathlib leaf was created.

## Not duplicates

lem-sc-qcoh-cech-total-tensor-iso vs lem-sc-picard-kunneth-qcoh: the existing parent is the quasi-coherent scheme-cohomology Kunneth theorem, while this item is only the field-linear tensor-total complex lemma used in its Cech proof.

## Second reading by H1

- Statement: checked against Stacks Tag 0BED, label `lemma-kunneth`, and the tensor-total display labelled `equation-kunneth-on-cech`; the auxiliary field-linear complex assertion has the required field, bounded-below, differential, and cohomology definitions, with verdict correct.
- Step 1: checked the complement decomposition and the finite-range claim against the field-linear argument following `equation-kunneth-on-cech`; injectivity and surjectivity of each restricted differential are now explicit, verdict correct.
- Step 2: checked the signed tensor contraction against the total differential in `equation-kunneth-on-cech`; the two mixed terms and their signs are written out, verdict correct.
- Step 3: checked the surviving zero-differential summand and representative map against the induced map in `equation-kunneth-on-cech`; verdict correct.
- New nodes: none; no statement-only child was needed, and searches of existing DAG nodes found no smaller duplicate or Mathlib Kunneth declaration.
- Changed the source metadata from the non-source name `varieties-lemma-kunneth` to Tag 0BED and label `lemma-kunneth`.
- Rewrote the statement to define cochain complexes, bounded-below, cycles, boundaries, and cohomology self-containedly.
- Expanded the contraction calculation and the restricted-differential verification to repair C1/E5 concerns.
