## What changed

Proved `TopCat.closed_embedding_restriction_transport_square` without changing its
signature. Added two proof imports: the new, fully proved supporting module
`Sheaf.Topology.EmbeddingPushforwardTransport` and the existing
`Sheaf.CategoryTheory.InverseMateEquivalence`.

The new module constructs the equivalences of sheaf categories, the natural
global-sections isomorphism, and the commuting direct-image square. Its private
helper proves that a homeomorphism gives a dense subsite on opens across arbitrary
universes. The existing categorical theorem proves invertibility of the mate. The assigned theorem constructs the section equivalences and proves the
square using naturality and `unit_mateEquiv_symm`.

Both delivered files compile locally without warnings. All constructions apply to empty
spaces and empty images: no nonemptiness or choice of a point is assumed. The
embedding homeomorphism uses only injectivity and the induced topology. The unit's
route is preserved; this node is not itself a realization of a unit statement or step.

## Proved and sorry left

- `TopCat.closed_embedding_restriction_transport_square`
  (`lem-weil-pbc-closed-embedding-restriction-transport-square`): proved.
- `TopCat.embedding_pushforward_transport`
  (`lem-weil-pbc-embedding-pushforward-transport`): proved.
- Private `TopCat.homeomorph_opens_dense`: proved inside the geometric module.

No `sorry` remains in any delivered module; none was split off as unfinished work.

## No longer needed

The original proof dependency `lem-weil-pbc-conjugate-iso-unit-equation` is no
longer used. The final proof uses the existing
`lem-stage3-inverse-mate-equivalences` and Mathlib's `unit_mateEquiv_symm` instead.
No original Lean import is removed: both public imports are needed by the unchanged
signature. This records the local dependency removal, not a claim that the old
node has no other users.

Second reading removed the newly proposed duplicate
`Sheaf.CategoryTheory.EquivalenceMateIsIso` and its node
`lem-weil-pbc-equivalence-mate-is-iso` from this delivery. No unit realization is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The old proof plan did not state the geometric transport of sheaf categories and
pushforwards; it is now explicit and fully proved. The actual unit equation used is
`CategoryTheory.unit_mateEquiv_symm`, which permits the vertical equivalences directly.
The old docstring named the same-right-adjoint uniqueness equation instead. The proof
text and DAG have been updated to the actual mates argument.

The literature paths named by the nodes are absent from this machine. Read the
corresponding sources at [Stacks 09ZG](https://stacks.math.columbia.edu/tag/09ZG) and
[Stacks 0B65](https://stacks.math.columbia.edu/tag/0B65), and used the local Mathlib
sources for the precise transport and mates constructions. Tag 09ZG is the application
context; the cross-universe transport itself is the explicit auxiliary argument in
the assigned node, constructed here from Mathlib's opens and site equivalences.

The initial dry run required the second-reading section prematurely. The final
dry run accepts its absence for the first worker and prints OK, explicitly
deferring that section to the second reader. No second-reading section is supplied
by this worker. All delivered modules pass compilation and the remaining preflight
checks; nothing was pushed.

## New nodes

`lem-weil-pbc-embedding-pushforward-transport` records the geometric part (original
steps 1–2). Its module proves the statement, including global-sections naturality and
the direct-image comparison. It assumes no inverse-image comparison or unit equation.

No change records: no definitions or existing statements changed.

## Second reading by H2

1. Compared every delivered module with the repository: the assigned theorem's
   entire signature is byte for byte unchanged. The other delivered module is
   new. No existing definition, statement, target or public import changed.
   The proof docstring records the actual mate argument.
2. Compiled both final modules individually in import order through lcompile.py,
   with no errors or warnings. Searched all delivered Lean for sorry and forbidden
   trust escapes: none. Scratch-copy #print axioms checks for the assigned
   theorem, geometric transport theorem, private dense-subsite helper and reused
   categorical theorem show only propext, Classical.choice and Quot.sound.
3. No unfinished statement is split off. Read the geometric theorem and its
   pointwise covering-sieve proof: the equivalences preserve covers, top opens,
   and the direct-image square. Empty spaces, empty embedded images, and identity
   embeddings require no point choices or extra hypotheses. Independent rg
   searches and launcher Loogle/LeanFinder searches found the existing
   isIso_inverseMate_of_equivalences; replaced the duplicate categorical theorem
   with it. The same-universe presheafEquivOfIso search hits do not replace the
   cross-universe sheaf transport statement. Both geometric and categorical
   results are strictly parts of the original argument, not restatements.
4. The final proof constructs sheaf transport, takes the inverse mate, and uses
   its unit equation and naturality to build the section square. All imports are
   needed; new supporting imports remain proof-only. The old proof dependency
   removed by this route is now listed under No longer needed. Checked
   dag/units/sk-thm-p1.json realized: the assigned node is not a unit statement or
   step realization, and no realized route is bypassed.
5. Read all delivered nodes against the Lean. The existing node's proof,
   proof_deps and proof_origin now reference the reused inverse-mate node.
   The sole new node records the exact geometric statement, complete proof,
   source, searches, origin, blueprint, chapter/unit and Lean record. No
   statement or definition change record is needed.

Changed: removed the duplicate categorical module and node, reused
Sheaf.CategoryTheory.InverseMateEquivalence, updated the proof docstring and DAG,
and corrected the pruning and final-delivery report. Kept the sound geometric
construction and section-square proof.
