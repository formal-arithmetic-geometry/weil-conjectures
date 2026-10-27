# Stage-1 worker report: lem-sfb-local-colimit-residue-field

Group Q45, 2026-10-23. Direct delivery; author self-review below.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-local-colimit-residue-field.json`: existing statement item, now split into eight proof steps. The statement and statement dependencies are unchanged. Mathlib searches found ingredients, not the full statement. Zero new nodes and zero new Mathlib leaves.
- `citations.json`: seven verbatim cited-statement excerpts, one for each cited node in each step.
- `report.md`: this report. `searches.jsonl` was written by the required msearch command and is retained.

## Attachments

None. Searched the entire project `lean/WeilConjectures/` for the exact blueprint tag and for colimit/local-ring/residue-field notions. `AlgebraicGeometry.exists_isColimit_residueField_of_isLimit` in `AlgebraicGeometry/LimitResidueField.lean` treats points of an inverse scheme limit and does not give locality or the specified maximal ideal. `IsLocalRing.flat_local_tower_directLimit` in `RingTheory/FlatLocalTowerDirectLimit.lean` assumes a field-valued cocone, flatness, and generation of stage maximal ideals from a base; it cannot attach this item, which has none of these extra data. The source declaration supplying a stronger-hypothesis theorem is not an exact attachment.

## WANTED

None. The needed Stacks sources are present locally.

## Findings and changes

The statement is correct as written. Stacks Algebra Tag 04GI, `lemma-colimit-henselian`, explicitly says that the ring colimit is local and its residue field is the colimit of stage residue fields, then says "argument omitted". The delivered proof fills this omission and is marked `proof_origin.by = agent`; it does not claim that the source supplies the details. It leaves henselianity and separable closedness to their separate existing items.

Reused `lem-pc-filtered-colimit-commrings-elementwise` rather than making a new eventual-equality or representation node. The nearby `lem-weil-pbc-filtered-colimit-algebras-elementwise` gives representation for an algebra colimit but lacks eventual equality, and `lem-weil-pbc-filtered-colimit-sets-elementwise` alone would require proving preservation by the ring forgetful functor. The chosen commutative-ring node states both facts directly. Reused `lem-weil-pbc-local-ring-unit-criterion` instead of creating an outside-maximal-ideal unit lemma. Ideal closure, maximality, quotient inverses, and the quotient map universal property are explicit elementary calculations, not new nodes restating clauses of the item.

The inherited `blueprint.from.node = null` is retained: the ancestor command reports that the chain has no imported blueprint ancestor. The precise inherited place and dependency-chain `via` list remain. I read the current blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3); the algebra input serves its open-image branch through the existing tame-boundary/root-tower chain. Neither its route nor its chapter/unit records are changed. Whole-blueprint searches `colimit local`, `direct limit`, and `local colimit` found no blueprint statement of this precise algebra lemma. The last search returns 47 broadly related nodes; the ring-locality candidate `lem-weil-pbc-local-rings-ind-zariski` concerns maps identifying localizations, not directed colimits of local rings.

## Mathlib searches

Retained all six inherited Q83 search records. Ran six more logged searches for this item using msearch.py: leanfinder for the full locality/residue-colimit statement, Loogle `IsLocalRing, DirectLimit`, grep for local/residue-colimit combinations in `RingTheory`, LeanSearch for the residue-field colimit, a second leanfinder phrasing about the union of maximal ideals, and grep for local-ring names in `Algebra/Colimit`. All services answered successfully; none is recorded as unavailable. I read the hits: residue-field maps/lifts and ring-colimit constructions do not assert the required theorem. The second semantic search also found `map_nonunit`, maximal-ideal facts, and `Ring.DirectLimit`, again ingredients only.

I also read the pinned Mathlib sources of `IsLocalRing.ResidueField.map` and its functoriality, `Concrete.isColimit_exists_rep` and `Concrete.isColimit_rep_eq_iff_exists`, `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`, and `IsLocalRing.notMem_maximalIdeal`. The existing DAG leaves accurately state the two mathematical inputs used here; there is no claimed new Mathlib match.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The generic filtered-ring-colimit and local-unit results are citations of existing nodes. The other Tag 04GI nodes concern henselian simple-root lifting or separably closed field colimits; neither is recreated or cited for a clause it does not state.

## Review by Q45

I read Stacks `algebra.tex`, Tag 04GI (`lemma-colimit-henselian`), including the exact omitted sentence. I also read Tag 00E9 (`lemma-characterize-local-ring`) and Tag 07BJ (`lemma-characterize-local-ring-map`), and the elementary representative construction in Tag 00D6 (`lemma-directed-colimit`). This item is exactly the omitted auxiliary algebra argument, so I supply its argument rather than extracting a duplicate of either of its conclusions. There are no new nodes needing separate source review.

For step 1, I opened `def-weil-pbc-category-colimit` and checked that its statement includes nonemptiness and the fact that a nonempty directed poset is filtered. I opened the full statement of `lem-pc-filtered-colimit-commrings-elementwise`: it covers an arbitrary small filtered diagram in commutative rings, every element has a stage representative, and equality is witnessed by arrows to one common object. Its hypotheses match the given colimit, so no construction of a different colimit or algebra structure is silently used. In a poset its arrows are exactly the inequalities needed.

For step 2, I use clause (2) of that same node, quoted in citations.json, to turn equality of two images into equality at one common stage. I checked both uses of the local-transition hypothesis: first it sends the representative from the stage maximal ideal into the later maximal ideal, then its inverse-image equality contracts membership back to the original stage. No coprojection is presumed injective. The direction from stage membership to membership in M is its definition.

Step 3 is a direct ideal calculation using step 1. Sum and multiplication are explicitly computed at a common stage, and negation at the original stage. Nonemptiness supplies the zero representative. Properness follows from step 2 applied to 1, not from an unjustified assertion that every ring colimit is nonzero.

For step 4, I opened `lem-weil-pbc-local-ring-unit-criterion`: its statement gives precisely an inverse for an element outside the unique maximal ideal of a commutative local ring. All A_i have that hypothesis; I use it at A_i, not at A before A is known local. Mapping the inverse to A proves the outside-M unit criterion. The arguments that an ideal containing a unit is the whole ring and that all proper ideals lie in M prove maximality and uniqueness directly. The contraction formula from step 2 then proves locality of the coprojections.

Step 5 uses the same existing unit-criterion statement at A_i and the explicit outside-M inverses already obtained in step 4. I check that the quotients are nonzero using properness before calling them fields; every nonzero class has an inverse by the displayed representative calculation.

Step 6 computes the maps on quotient classes. The local-transition condition and step 2 respectively ensure differences of representatives vanish in the appropriate quotient. Ring laws, system identities, and the cocone identity are checked on classes. Kernel-zero, proved by contraction, gives injection by applying it to a difference; this does not assume any original transition map is injective. These are elementary computations from preceding steps, with no unstated functoriality lemma.

For step 7, the statement of `def-weil-pbc-category-colimit` gives exactly the unique ring map g from the compatible cocone h_i q_i. I checked the compatibility equation and the assertion that g kills M on a representative in a stage maximal ideal. The induced map on A/M is defined on classes and its independence of representatives is written out. The target B is any commutative ring, so the proof really establishes a colimit in rings rather than merely in fields. Step 8 uses the same universal-property statement for uniqueness after composing with the quotient; surjectivity of the quotient is simply that its elements are classes.

Small cases: for a one-element index poset, every construction reduces to the original maximal ideal and quotient field. For a directed system of fields, M=0 and the argument recovers the field colimit. The noninjective local surjection Z/4Z -> F_2 is allowed: its maximal-ideal image vanishes in the target, but the inverse image remains (2), as step 2 requires. Z_(p) -> Q illustrates why the local-transition condition matters: its maximal ideal contracts incorrectly, so it is excluded. The empty diagram is excluded by the explicit nonemptiness hypothesis; the zero ring is excluded at each stage by the existence of a unique maximal ideal, while the cocone target B is allowed to be zero. No flatness, finiteness, algebraicity, or surjectivity hypothesis is used.

I checked delivery-errors B--E against the files: no new statements with hidden objects; no unrun searches; no source section number substituted for a tag; no duplicated/relabelled clause nodes; no unsupported source theorem masquerading as a citation; no circular dependency. The only proof dependencies are the three existing Mathlib leaves just inspected. Every cited node has its own verbatim quote. All proof steps are under 700 characters, so none crosses the long-step threshold. Nothing was corrected in the statement; the repair is solely the missing proof and its citations.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled. Delivery validation and push are performed using the required launcher commands after this report is written.
