## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-line-twist-double-annihilator-reverse.json`: existing statement item, now split into six steps; no Mathlib match.
- `citations.json`: ten entries, one for each cited node in each proof step, with literal statement substrings.
- `searches.jsonl`: actual search-command log; `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. No Lean or repository files were written, and no compiler, Lake, or local delivery-check scripts were run.

Attachments: none. A project-wide search for the exact blueprint tag returned no declaration. Searches for annihilation, reverse maps, line twists, and kernel/cokernel constructions found the existing `AlgebraicGeometry.RingedSpace.sheafified_cokernel_local_image` in `lean/WeilConjectures/Topology/SheafCokernelLocalImage.lean:53`; it supplies the local-lifting dependency, not this item's reverse map. The double-annihilator results in `Mathlib/LinearAlgebra/Dual/Lemmas.lean` concern reflexivity and do not state the item.

WANTED: none.

The statement is unchanged. The initial item had no proof; its source explicitly omits the needed factorization detail. I supplied the local construction, including independence of lifts, linearity, gluing under changes of frame, both composite identities, and the arbitrary-integer twist. The proof is marked agent-written rather than attributed to an unwritten argument in Stacks.

Nothing mathematical remains unfinished in this split. No new statement-only node is needed: the non-elementary local-image assertion already has a closed DAG node, and the rest is a direct construction from the module and sheaf axioms. Every step is shorter than 2000 characters; the six proof texts total 2750 characters.

## Sources and searches

I read `literature/stacks-project/local-cohomology.tex`, Tag 0GAC (`lemma-factor-hom`), especially the paragraph after the bound on the kernel and cokernel of the dual comparison, and Tag 0GA9 (`lemma-annihilated`) immediately preceding the cohomology bounds. Tag 0GAC is the provenance of the omitted reverse-map input, not a claim that Stacks literally states this general theorem for arbitrary module sheaves and arbitrary sections. The generalization is proved here without using coherence, regularity, or cancellation of the section. I also read `literature/stacks-project/modules.tex`, Tag 01AH (`lemma-limits-colimits`), for the sheafified cokernel description, and the existing local-image Lean declaration and docstring. No SGA source is used.

The chapter and unit records were read. I read the latest blueprint ancestor proof at `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`, particularly its current Step 3. As the inherited `blueprint.from.place` already explains, that step concerns Verdier exchange and does not itself state the long algebraization branch inherited by this item. I retained that ancestry and recorded the precise supporting-source place, rather than inventing an assertion in the current ancestor or altering the unit route.

Whole-DAG title, statement, and tag searches covered kernel/cokernel, image/coimage, annihilation, invertible modules, and local module Hom. Whole-blueprint searches with `tools/blueprint_refs.py search` included `annihilat`, `exact tensor`, `reverse map`, `kernel and cokernel`, `cokernel local image`, and `local module hom`. No blueprint node states the item. The existing local-image node is reused instead of duplicated; the local Hom sheaf node is unnecessary because the gluing argument is written explicitly. The inherited source searches are preserved. The additional five Q11 searches actually ran through `msearch.py`: LeanFinder twice (line-bundle and scalar phrasings), LeanSearch, Loogle, and source grep. All services answered. Their records, queries, and hit digests are preserved verbatim in the item's added search entries and the sandbox log.

I read the search hits. The first LeanFinder query gives free-sheaf presentations and relations in `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`; these need free presentations and do not construct the required reverse map. The second gives flat equational factorizations, scalar exact sequences, regularity across exact sequences, and finite localized-map comparison; these do not give the line-twisted theorem. LeanSearch gives scalar operations in module sheafification and restriction of scalars. Loogle returned no hits. The grep hits on dual annihilators concern subspaces of dual modules; the other reverse-map hits are path homotopies, Clifford reversal, braiding calculations, or unrelated structures. None is an exact match or a one-line specialization for the item.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs requiring disambiguation. The item's double annihilating twist is different from dual-annihilator involution for vector spaces or reflexive modules.

## Review by Q11

I checked the statement against the explicit hypotheses, not just the source's special case. The sheaves are arbitrary module sheaves on the Zariski ringed space underlying the scheme. Invertibility supplies local frames on any scheme; neither an affine cover with affine intersections nor quasi-coherence of the other sheaves is used. The two annihilation assumptions are exactly what the construction uses, separately: cokernel annihilation supplies local lifts and kernel annihilation makes the multiplied lifts unique. No hypothesis is added or dropped.

Step 1 uses the statement of `def-sc-invertible-module`, which explicitly says locally free of rank one, and `def-pur-sheaf-tensor-product`, which defines tensor product by sectionwise tensor and sheafification. In a frame the maps are multiplication by the stated powers; the inverse identification sends a tensor to its scalar coefficient and is defined on the whole sheaf by the tensor universal property. `def-weil-sheaf-of-modules-category` explicitly supplies sectionwise kernels and sheafified sectionwise cokernels, so the chosen q really is the cokernel in the hypothesis. No exactness of arbitrary tensoring is silently assumed.

Step 2 cites `lem-weil-pbc-sheaf-cokernel-local-image`. I opened its entire statement: it applies to every ringed space and arbitrary module-sheaf morphism and identifies the kernel of precisely this q with sections locally in the image. Applied to a^c g, killed by q, it gives the local lifts actually used. Its statement does not assert global surjectivity on sections, and no such assertion appears here. The cited node is Lean-closed and is a permissible generic tool from another unit; its exact use is quoted in citations.json.

Step 3 uses the module/sheaf definition again. On intersections the difference of two lifts lies in the actual sectionwise kernel and a^c times it is zero by the hypothesis. Thus the section gluing, independence, and restriction law follow from the sheaf axiom. I checked additivity using a common refinement of two covers and scalar linearity using scalar multiples of lifts; both formulae are written in the step. These are elementary calculations, not an invocation of a missing descent theorem.

Step 4 uses only those same definitions. I checked the frame change explicitly: if e'=u e and a'=u a, then u^c x lifts (a')^c g, and its multiplied value is u^(2c) times the old value. This is exactly the transition of the source G(2c), with no transition on the target F. Gluing the values of the resulting local morphisms gives the global morphism and its restriction/linearity laws by uniqueness. No separate non-elementary gluing claim is hidden here.

Step 5 computes both composites, not only the one needed by the parent. For alpha beta, apply alpha to a^c x. For beta alpha(2c), choose the specific lift a^c f of a^c alpha(f). Equality is local and the sheaf's separatedness gives equality globally. This needs no additional node beyond the previous construction.

Step 6 uses the invertible-module dual and tensor definitions. The tensor frame, or its dual in negative degree, gives the displayed beta_r formula. Applying alpha gives the same a^(2c) coefficient and the correct target frame of exponent r-2c, verifying the stated arbitrary-integer conclusion. It does not identify twists by cancellation of the section.

For the B--E audit I checked self-contained objects and definition citations, single TeX escaping, unchanged source/provenance fields, and that every non-elementary use is the literal statement of an existing cited node. There are no unsplit new nodes with hidden proofs, no clause moved to a new node, and no circular step. I checked all ten citation quotes against the live statements. The union of step uses is precisely proof_deps. No missing construction was replaced by a definition citation: the only theorem-level use is the explicit local-image result, and all remaining algebra and gluing are written out.

Small cases: for c=0, the two zero maps in the hypotheses are identity maps on the kernel and cokernel, so these sheaves vanish and the construction is the inverse of alpha. For s=0 and c>0 the construction is zero and both required composites are zero. If F or G is zero, the remaining annihilation hypothesis makes the required delta_(2c) zero. On the empty scheme the sheaf axiom supplies the unique maps. For nilpotent or zero-divisor a, only a^c(x-y)=0 is used, never division by a. A nontrivial line bundle is covered by the explicit unit transition calculation. Negative r uses the dual frame, so no nonnegative-degree restriction is introduced. There is no statement dispute or source correction in this delivery.
