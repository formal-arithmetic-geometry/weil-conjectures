# Stage-1 delivery: lem-sfb-henselian-flat-finite-module-residue-free-colimit

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-henselian-flat-finite-module-residue-free-colimit.json`: item, split; statement and statement dependencies unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-henselian-flat-point-free-affine-neighbourhood.json`: one new statement-only unsplit geometric lemma, no Mathlib match, no proof or proof dependencies.
- `citations.json`: one verbatim statement quotation for each step/dependency pair.
- `searches.jsonl`: actual msearch.py search log; original item searches are retained and the searches of this worker are appended in mathlib_searches.
- `report.md`: this report.

## Attachments

None. I searched the live WeilConjectures library by the item tag, henselian/colimit, closed-fibre injection, and affine-neighbourhood freeness. None gives this item or the new geometric lemma. The Mathlib result Module.free_of_flat_of_isLocalRing (RingTheory/LocalRing/Module.lean:304, read) assumes Module.Finite A P. Our P is finite over B, so it is not a match. No Lean was written or compiled.

## WANTED

None. The source files used are present locally.

## Corrections and scope

The imported statement is correct against Stacks 05U7, flat.tex, lemma-flat-finite-type-local-colimit-free, first assertion. The additional Mittag-Leffler conclusion is intentionally outside this item. The original proof was empty. I expanded the source argument rather than moving its conclusion to a new node. I also made explicit that the category is a set of opens, that intersections have smaller free affine neighbourhoods, and that the closed-fibre comparisons carry the actual restriction maps. There is no finite-rank assertion over A.

I read SETUP's chapter/unit/node distinction, the recorded chapter and unit, GOAL.md, stages/1-dag.md, and delivery-errors B--E (including the merged copy). The current blueprint is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. Its proof's direct-image/compactification paragraph is the ancestor route. The DAG item's inherited blueprint.from.node is null, and blueprint_refs.py ancestor prints None; I retained that inherited provenance, supplied a precise supporting place and the complete via chain for the new node, and did not invent an imported blueprint ancestor. The unit record is not this item's statement, so no realization fields are edited. coord/dag-sync.md and a repair note for this item are absent in this read clone.

## Not duplicates

lem-sfb-henselian-flat-point-free-affine-neighbourhood vs lem-sfb-henselian-flat-finite-module-residue-free-colimit: the new node is the geometric local existence theorem of Tag 05MF for an arbitrary finite-type quasi-coherent module flat at a closed-fibre point; it asserts only one free affine neighbourhood. The item constructs a filtered colimit of a localized finite module with residue-injective transitions. The shrinking, kernel detection, index and colimit arguments remain in the item.

DAG/source searches for 05MF and lemma-flat-finite-type-affine-neighbourhood-projective found no existing node. Whole-blueprint searches (blueprint_refs.py) for 05MF, colimit free, free module and henselian were read; they supply no duplicate. I also searched the live blueprint text and Lean source for the tag and affine-neighbourhood freeness. Associated-point finiteness and detection were already present and were reused, not recreated. The new node cites only Tag 05MF in its source, so there are no existing same-source-tag pairs to distinguish.

## Review by NV

For the item I read flat.tex Tag 05U7, its proof in full, and the preceding Tag 05MF (lemma-flat-finite-type-affine-neighbourhood-projective). For the new node I read that same 05MF statement and proof, which reduces through the finite-presentation version 05ME. Its elementary etale-neighbourhood conclusion specializes to the claimed A-module conclusion because A is henselian and the marked residue field is unchanged: 04GG's retraction criterion (read in algebra.tex) gives the marked section, and an etale section is an open immersion, giving the same local ring at the marked point. This explanation is source interpretation here, not a proof hidden in the new statement; the new node remains a theorem to split. Applying it inside arbitrary open neighbourhoods is what yields a basis, not a stronger unrecorded clause of its statement.

Step 1 uses the exact localization definition of essentially finite type, finite generators, the principal-open localization formula in lem-weil-pbc-spec-module-tilde-sections, the finite-type affine equivalence in lem-weil-pbc-quasi-coherent-finite-type-affine, and the germ criterion in def-weil-pbc-module-stalk. I opened and read each statement. The finite module model is constructed as C^r/K; no finite presentation is asserted. Locality ensures that q contracts to m. I checked the possible issue that essentially finite type means localization at an arbitrary multiplicative set: because the result is local, localizing C at the contracted maximal ideal gives exactly B, as written. The germ calculation gives the original A-action, not merely an abstract group isomorphism.

Step 2 applies lem-weil-pbc-finite-type-algebra-noetherian only to the residue algebra R over the field k, never to C over the possibly non-Noetherian A. I read its exact statement and the candidate Mathlib declaration Algebra.FiniteType.isNoetherianRing, RingTheory/FiniteType.lean:187. The existing 00LC node gives finiteness of associated primes of the finite R-module H (also checked against algebra.tex lemma-finite-ass); the existing 02OK node translates them to points (divisors.tex lemma-associated-affine-open, both implications read). The existing tilde pullback node (schemes.tex 01I9, lemma-widetilde-pullback, read) gives precisely the closed-fibre sheaf. None of these nodes needs a Noetherian hypothesis on A.

Step 3 uses only the associated-point dictionary and the prime/specialization convention, writing out the finite product which removes every bad point while keeping x. Open restriction leaves local rings and stalk modules unchanged, hence the associated points are exactly the intersection, not a claim about arbitrary base change of associated points. The chosen product remains outside q because q is prime. The empty bad set gives h=1. This is the actual shrinking argument behind the source's sentence, rather than a new lemma for an elementary shrinking.

Step 4 cites the new geometric lemma and the stalk definition. I checked local finite type, quasi-coherence and finite type on every open restriction, the closed-point image, the unchanged flat stalk P, and henselianity. For any pair of objects, another application inside their intersection gives a common target, even when that intersection is not affine. The category is the subset of all affine opens with free sections, so no choices of bases enlarge the objects; every hom set is empty or singleton. The source says fundamental system, and this step supplies it with the required smallness and filteredness.

Step 5 uses lem-pc-flat-affine-base-change-sections. I opened its statement and checked that despite its name it explicitly assumes no flatness of the base change. It applies with R=A, S=k, and W'=the inverse image of each affine W. Its pure-tensor formula supplies compatibility with restriction: both composites send bar(a) tensor z to bar(a) times the restricted pullback of z. The quotient/tensor identification is written with its two inverse maps. Thus the transition reduction is exactly the map tested in step 6. This uses the statement, not the proof, of the cited node.

Step 6 uses the finite-type affine criterion, lem-sbc-affine-section-associated-stalk, localization permanence and the definition of locally Noetherian. I read all four statements. I added the principal-open Noetherian covering argument during self-review so the local Noetherian hypothesis is explicitly justified, instead of merely asserting it for a fibre open. The detection theorem is used only on the locally Noetherian closed fibre and with a finite affine section module. I read divisors.tex 0B3M (lemma-restriction-injective-open-contains-weakly-ass) and its proof as the source kernel argument; the existing detection node is a sufficient stronger interface for the particular nonzero section. An associated point detected there is associated on the ambient closed fibre because its stalk is unchanged. Specialization to x then forces it into the target open, where the section vanishes, giving the contradiction. This proves every transition clause rather than using a theorem about the same colimit.

Step 7 uses only the stalk/germ and categorical colimit definitions. I read both statements. The representative formula for maps to an arbitrary A-module is well-defined by equality on a smaller neighbourhood; the free-neighbourhood basis refines that neighbourhood. A common refinement verifies linearity. Existence and uniqueness of the factorization are both explicit. This step is elementary relative to those definitions, not an appeal to an unrecorded cofinality theorem.

The four off-unit non-Mathlib tools are declared in split_report.tool_uses with their purposes: the affine finite-type dictionary, tilde pullback, affine section base change, and associated-stalk detection. They are generic black boxes for this commutative-algebra argument, and do not replace a step of the six-functor unit. Every cited statement has a verbatim quote in citations.json. The proof dependencies equal the union of uses. Each non-elementary step is below 2000 characters, so no long step hides a separate standard comparison. No SGA source is cited.

I tested the assertions on P=0 (the finite module and all associated-prime sets may be empty; free means rank zero), on A a field (m=0 and vector spaces, with no finite-rank bound), on B=A and finite flat P (already free), and on a finite-type closed fibre with embedded associated points such as k[u,v]/(u^2,uv). The shrinking uses all associated primes, including embedded ones. A non-Noetherian henselian base is permitted throughout: only its finite-type residue algebra is Noetherian. The new geometric theorem also permits infinite-rank A-freeness and a zero stalk; no Nakayama argument for an infinitely generated A-module is used. The empty source scheme has no x and hence causes no counterexample. No statement dispute or unproved extra hypothesis was found.

## Unfinished work

The new geometric node is deliberately statement-only, for a later stage-1 split. The item has a complete argument conditional on its cited nodes. No Lean or compiler verification is part of this authorized stage.
