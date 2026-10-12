## What changed

Proved `exists_popescu_maximal_bad_quotient` with its signature unchanged.
Mathlib selects a maximal member of the set of ideals that are zero or whose
quotient map is bad. In the zero branch the proof keeps the original rings and
uses maximality directly. In the other branch it constructs the two quotient
rings and obtains their Noetherian instances. Regularity follows from
`RingHom.regular_base_change` and the tensor-quotient equivalence. A proved private
helper transports regularity through an algebra equivalence; another proves that
a bad algebra has nontrivial base using smoothness of a zero algebra.

For each nonzero quotient ideal J the proof shows that its inverse image K
strictly contains the selected ideal, obtains ind-smoothness modulo K by
maximality, applies the existing
`Algebra.ind_smooth_quotient_compatibility`, and rewrites map(comap J)=J.

The new imports are proof-only:
`Sheaf.Algebra.IndSmoothQuotientCompatibility`,
`Mathlib.RingTheory.TensorProduct.Quotient`, and
`Mathlib.RingTheory.Smooth.StandardSmoothCotangent`.
No existing statement, definition, visibility, public import, or module-level
option changed. No forced adaptations or change records were needed.

The final module compiles without warnings with `lcompile.py`.

## Proved and sorry left

Closed the original hole `exists_popescu_maximal_bad_quotient`. No `sorry` remains
in the delivered module; no holes or new modules are added. Holes closed: 1;
holes added: 0; split off: 0.

The proof uses the existing theorem
`Algebra.ind_smooth_quotient_compatibility` (node
`lem-weil-pbc-ind-smooth-quotient-compatibility`), which still has its own named
`sorry` in the repository. That dependency is used as intended in stage 3 and is
not modified or redeclared in this delivery.

## No longer needed

No original repository imports, nodes, or modules were pruned. The original
`Sheaf.RingTheory.RegularBaseChange` import remains necessary.

The earlier sandbox core module and its proposed nodes were deleted. Provisional
new modules for regularity, quotient-zero transport, and quotient-tower transport
were also deleted. Regularity and nontriviality are proved directly; the separate
zero branch avoids quotient-zero transport; the already stated
`Sheaf.Algebra.IndSmoothQuotientCompatibility` supplies tower transport. No new
nodes are delivered. Discarded sandbox proposals are not whole-library pruning.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt moved almost the whole conclusion into a core
statement and supplied a separate unproved nontriviality lemma. Its node records
were incomplete. That attempt has been replaced. Its old second-reading section
was removed so the independent reader can write their own assessment.

The original DAG's maximal-ideal route is valid. Including zero explicitly in the
set lets that branch keep the original rings and avoids quotient-zero transport.
The final library-wide duplicate search found the existing successive-quotient
compatibility theorem under `Sheaf.Algebra`, replacing the proposed new lemma.

Edge cases checked: zero base forces zero target and hence smoothness, contradicting
badness; J≠0 is used precisely for strict containment; quotient compatibility needs
only containment and does not require nilpotence or nontriviality. The source's
first paragraph was checked against Stacks Tag 07F5 online. The blueprint unit
route and all target statements are preserved.

## Second reading by Y3

1. Interface: PASS. Diffed every delivered Lean module against the repository
   (one module). The existing theorem signature is byte for byte unchanged, as
   are its docstring, visibility, definitions and public imports. Only the proof,
   two proved private helpers and three proof-only imports were added. No change
   records or forced adaptations are needed.
2. Proof: PASS. Compiled the module with lcompile.py, without errors or warnings.
   A scratch copy with #print axioms for the main theorem and both helpers compiles.
   Both helpers use only propext, Classical.choice and Quot.sound. The main theorem
   additionally uses sorryAx through existing open dependencies, including
   Algebra.ind_smooth_quotient_compatibility; it is not yet axiom-free in closure.
   The delivered module has no sorry, axiom, unsafe, opaque, implemented_by or extern,
   and contains no new definition or choice of data from an unproved existence theorem.
3. Split statements: PASS, none. Checked the existing quotient compatibility
   theorem used by the proof: the containment I <= comap J is exactly its required
   hypothesis, and the third isomorphism theorem justifies its conclusion without
   nilpotence. Checked zero base, zero selected ideal, and nonzero J; J may be the
   top ideal. Nontriviality follows from smoothness of a zero algebra, and J != 0
   is precisely what makes the lifted ideal strictly larger.
4. Route and pruning: PASS. Read the proof from maximality downward and checked
   Stacks https://stacks.math.columbia.edu/tag/07F5, first proof paragraph. Searched
   the library for regularity/equivalence and successive quotient transport, and
   queried Loogle for AlgEquiv with RingHom.Flat. The existing general theorem
   RingHom.IsRegular.of_ringEquiv offers a more general transport argument; the
   current proved helper directly handles the fixed-base special case with two
   tensor equivalences, so no repair is needed. The added imports supply tensor
   quotient identification, quotient ind-smoothness compatibility, and the
   standard-smooth-to-smooth instance, respectively. No old import or proof
   dependency is pruned. The item is below the unit level, absent from
   dag/units/sk-thm-p1.json realized; no unit statement or step is bypassed.
5. DAG: PASS after repair. Compared the node against the repository: only proof,
   proof_deps and proof_origin change. The four steps agree with the Lean proof,
   and proof_deps is their union. The Lean record still matches the unchanged
   signature; there are no new nodes. Restored def-weil-pbc-noetherian-ring to the
   first step and proof_deps, since maximality and quotient Noetherian instances
   still use it. All old proof dependencies are therefore retained.

Second-reading changes: restored the omitted Noetherian-ring dependency in the
DAG and added this review. The Lean proof is unchanged. Holes closed: 1
(exists_popescu_maximal_bad_quotient); holes added: 0; split off: 0. This closes
one local hole using existing dependencies, not the entire axiom-free closure.
