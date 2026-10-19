# Q61: lem-per-prime-to-ell-uniformization-standard-form

## Files written

All node files are under `dag/nodes/sec-deligne-laumon-a1/` in this sandbox.

- `lem-per-prime-to-ell-uniformization-standard-form.json`: item, statement preserved, four-step split; no Mathlib match.
- `def-per-prime-to-ell-alteration-topology.json`: new definition, unsplit; no Mathlib match.
- `lem-per-gabber-prime-to-ell-regular-cover.json`: new statement-only theorem, unsplit; no Mathlib match.
- `lem-per-alteration-cover-standard-refinement.json`: new statement-only theorem, unsplit; no Mathlib match.

Also wrote `citations.json`, containing the verbatim statement of the node cited by each of steps 2 and 3. Three new nodes, zero Mathlib leaves. The previous sandbox contained the unsplit item and searches but no report or completed split. I compared that copy with the current repository, retained the unchanged statement and inherited search records, read the saved search responses, and reused their actual queries and results. The script `finish_split.py` is sandbox-only working material, not part of the delivery.

## Attachments

None. Searches under the project declarations in the read-only slopmaster2 and master checkouts for the blueprint tag and alteration/uniformization concepts did not locate a declaration giving this item. The source's ordinary regular-scheme definitions and regularity lemmas do not state this theorem. No compiler was invoked.

## Wanted

None. The ILO PDF is already available in literature; I used the retained sandbox text extraction for the passages below.

## What was wrong or incomplete

The inherited item had no proof. Its prior search verdicts referred to an ordinary etale finite-coefficient result although the statement is a geometric uniformization diagram; I corrected those descriptions without changing the recorded historical queries/results. I added the definition dependencies for finite locally free morphisms, finite type, and residue fields. No statement dispute or change to the mathematical statement was necessary.

The blueprint's nearest ancestor is `lem-per-artin-gabber-affine-curve`, proof Step 3 on Verdier duality. This item is a generic geometric finiteness input several levels below that step, not a replacement for the chapter or unit route. I read the current main-20261015 ancestor statement and proof and the chapter and unit records; no unit realization file needs modification because this item is not the unit's key statement.

## Not duplicates

- `def-per-prime-to-ell-alteration-topology` vs `def-weil-pbc-topos`: the existing node defines general sieves and Grothendieck topologies, not the category of reduced generically finite maximally dominant schemes or the prime-to-ell generating covers. The new definition cites that existing definition.
- `def-per-prime-to-ell-alteration-topology` vs `def-trf-orgogozo-induction-data`: the existing node defines individual alterations and modifications but not the alteration category, residue-degree decomposition condition, or generated topology.
- `lem-per-gabber-prime-to-ell-regular-cover` vs `lem-per-prime-to-ell-uniformization-standard-form`: the new theorem regularizes pairs in the alteration topology for a reduced quasi-excellent base; it does not supply a birational/etale/finite-flat diagram. The item's proof must turn that covering into such a diagram with a different, general theorem.
- `lem-per-alteration-cover-standard-refinement` vs `lem-per-prime-to-ell-uniformization-standard-form`: the new theorem refines an arbitrary alteration cover and has no regularity or boundary conclusion. The item constructs its input cover by the independent Gabber theorem.
- `lem-per-alteration-cover-standard-refinement` vs `lem-trf-alteration-finite-refinement`: the existing theorem treats a single proper alteration and modifications of its source and target. It does not handle a cover in the generated alteration topology, preserve a degree prime to ell, or provide a completely decomposed etale middle family.
- `lem-per-alteration-cover-standard-refinement` vs `lem-trf-alteration-blowup-finite`: the existing theorem treats a single alteration, without completely decomposed etale families, refinement of arbitrary covering families, or a prime-to-ell degree assertion.

I searched the whole DAG's statements for alteration/uniformization and the specific ILO theorem references, and ran `tools/blueprint_refs.py search` separately for alteration, uniformization, and Gabber. There are no blueprint nodes for these two geometric theorems. The Gabber hits concern Artin-Gabber affine pushforward, affine henselian comparison, or effacement, not this result. No new source is represented by a Stacks tag: the sources here are precisely the ILO theorems, identified by expose, theorem and printed page, rather than an invented Stacks equivalent.

## Review by Q61

I read ILO II 1.1.2, 1.1.8, 1.2.2, 2.1.1--2.1.2 and 2.3.1 (printed pp. 23--28) for the new definition. I checked that the category requires reduced sources, finite type, and a finite residue extension at every generic point mapping to a generic point of the base. The definition distinguishes a prime-to-ell degree at some generic point over each generic target point in the image from the etale decomposition condition at every point. It does not incorrectly use the ordinary scheme fibre product as a fibre product of alteration objects. I opened the existing definition statements for reduced schemes, finite type, properness, surjectivity, residue fields and Grothendieck topologies and used only the notions they actually define.

For `lem-per-gabber-prime-to-ell-regular-cover` I read IX Theorem 1.1 (printed p. 131) and the use in XIII 3.2.1 (printed p. 199), against `def-trf-strict-normal-crossings-boundary`. The hypothesis is quasi-excellence and an invertible prime, not excellence or finite dimension. The boundary condition concerns the support of the inverse image of a closed set: it does not assert that a scheme-theoretic inverse image with arbitrary multiplicities is reduced. The node states existence of a reduced strict normal crossings boundary with that support. The sources lie in alt/S, so their morphisms are finite type; the theorem's finite covering family is retained.

For `lem-per-alteration-cover-standard-refinement` I read II Theorem 3.2.3 (printed pp. 30--31), II Corollary 2.2.4 (printed p. 27), and XIII 3.2.1. The general input is a covering family in the generated topology, not just a single proper prime-to-ell alteration. The output factors through individual input members. II 3.2.3 makes all schemes irreducible; in the reduced alteration category they are integral. Its proper birational map gives the dense-open isomorphism. The completely decomposed etale family has a finite subfamily by II 2.2.4; refining by affine opens supplies separated finite-type etale maps. The finite flat maps over these integral Noetherian bases are finite locally free, have constant rank equal to their positive prime-to-ell generic degree, and are surjective. These are part of this general statement's interface, still unsplit, not an unsupported conversion inside the item's proof. I checked the existing `def-pc-finite-locally-free` states finite, flat and locally of finite presentation and defines its degree by fibre dimension.

In item step 1 the open U has closed nowhere dense complement Z; integrality supplies reducedness. This uses only definitions and the stated hypotheses. In step 2 I use exactly the statement of the new Gabber node: it supplies a finite covering by regular Noetherian Y_b, its finite-type maps, and boundary supports equal to the inverse image of Z. The equality of the open inverse image of U with the complement of that support follows directly, without pulling a boundary along the later refinement maps. In step 3 the new standard-refinement node applies because X is integral Noetherian quasi-excellent and the family from step 2 is actually covering in the required topology. Its statement explicitly supplies every type, separation, rank, decomposition, and factorization clause used there; I did not borrow an argument hidden in another node's proof. Both citations are copied verbatim into citations.json. In step 4 the disjoint union is built with the component structure sheaves, and composing each factor map with its summand inclusion gives an X-map because its structural composite is q_b h_i = p e_i a_i. This is an elementary assembly, not a further non-elementary comparison. All non-elementary steps have cited theorem nodes; no step exceeds 2000 characters.

I checked B1--B10: new theorems have complete self-contained statements and empty proof/dependency lists; their definitions are cited; all new nodes carry source places, ancestry, and searched same_as fields; none is a Mathlib leaf or a project attachment. I checked C1--C8 against the actual cited statements and dependency directions; no result depends back on the item, and both source theorems inherit this item's unit. I checked D1--D5: the two source results have independent general inputs and different outputs, and the item constructs the regular cover, standard-refines it, and writes the actual component compositions. This is not the same item renamed. I checked E1--E7: no extra excellence, finite dimension, regularity of the refinement schemes, etaleness of the finite flat maps, or generic identity for the boundary open has been assumed.

Small cases checked: for a regular X with an existing strict normal crossings boundary, the identity diagram with rank 1 is admissible; for X the spectrum of a field and U=X, the empty boundary is allowed by the existing boundary definition; for U=X but singular X, Gabber still regularizes X while the boundary remains empty. In characteristic p the prime ell remains distinct from p, as required by invertibility; degree prime to ell does not require separability. The finite subfamily retains residue-field-isomorphism lifts, not just pointwise surjectivity. An integral base is nonempty, so an empty covering cannot accidentally witness the theorem.

I read all retained LeanFinder, LeanSearch and Loogle results and their grep logs before reusing them. The hits are standard smooth/etale maps, normalization, Noetherianity, general covers or general scheme topologies, not these results. For standard refinement the LeanSearch service and initial unrestricted grep timed out; both remain recorded as unavailable, while the already logged AlgebraicGeometry-restricted grep succeeded with no hits. No query was invented or rerun with an unchanged search question. No new Mathlib match is asserted. Sources and scripts remained read-only outside the sandbox.

## Unfinished work

The three new nodes deliberately remain unsplit for future stage-1 work. Nothing in the requested one-level split remains unfinished. Server dry-run and delivery results will be reported after running the authorized delivery command.
