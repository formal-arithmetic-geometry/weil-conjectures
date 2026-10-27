# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-line-dedekind-extension.json`: statement, split with ten proof steps; no Mathlib match.
- No new nodes and no Mathlib leaves created. Existing generic tools cover every non-elementary input.
- `citations.json`: one verbatim statement quote per step/node citation. `searches.jsonl` is the unmodified msearch log. `write_split.py` is the sandbox-only regeneration script.

## Attachments

None. Searches in the live `lean/WeilConjectures` by exact blueprint tag and by multiplicative/primitive line, rigidified, and Dedekind concepts found no declaration stating all the clauses. The only rigidified/frames hits concern Artin–Schreier sheaves and coefficient towers, not this geometric result. No sorry declaration was treated as finished.

## WANTED

WANTED: `literature/bosch-lutkebohmert-raynaud-neron-models.pdf`, Section 10.1 Proposition 7, printed p.292 (PDF page 298), for this item. The primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf was read online. It asserts primitive-line extension using factorial local rings and constructs the connected extension before translated-chart gluing. The local original remains absent; nothing was downloaded.

WANTED: `literature/moret-bailly-pinceaux-varietes-abeliennes-Asterisque129-1985.pdf`, II 3.2.2–3.2.3, source of the already existing rigidified big-open extension node. Its existing statement is used, not an unrecorded proof from the missing book. I also read Deligne's primary Numdam scan, Section 4.2, printed p.142 (https://numdam.org/item/AST_1985__127__131_0.pdf), on extension by regularity, correction at the identity, and uniqueness from irreducible fibres. No SGA source is used.

## Audit and changes

The item statement is unchanged. The imported node had no proof. In particular BLR's sentence on primitive lines is not itself a proof of extension of the specified multiplication, of the coherence identities, or of all the frame-group geometry; these arguments are now written out. The proof is marked agent-written. No statement dispute was found.

I read AGENTS.md, GOAL.md, the worker/stage-1 brief, the three blueprint levels in SETUP.md, the chapter and unit records, and the latest unit text. `coord/dag-sync.md` is absent on this read clone. The assigned node is an auxiliary descendant, not the unit key node, so no unit realization fields are changed. `blueprint_refs.py ancestor` returns None; the existing null ancestor and via chain are retained. Whole-blueprint searches for the full multiplicative-line concept, rigidified, and frame give no matching imported node. The latest unit has changed relative to the historical unit record; this delivery does not amend either one or claim to realize its theorem. It completes only the existing BLR auxiliary prerequisite.

I searched the entire DAG for generic line extension, vertical divisors, factoriality, invertible-limit descent and frame geometry, then opened the statements of the candidates. This avoided creating a duplicate of rigidified big-open extension, a duplicate of vertical-Cartier descent, and a duplicate of invertible affine-limit descent. The existing frame-product Laurent algebra assumes a representing scheme, so I did not cite it for existence: the frame charts are explicitly glued first.

The prescribed msearch commands were run for the item: LeanFinder, LeanSearch, Loogle and Mathlib grep, followed by a second semantic phrasing. Actual returned signatures were read. Abstract `GroupExtension`, ring Picard functors, Selmer groups, and smooth manifold group sheaves do not assert this scheme-theoretic theorem. The msearch log records these exact searches; the item retains its older searches as source history and adds only the searches actually performed here. There are no new nodes to search.

## Not duplicates

No new nodes. All required facts already have cited DAG nodes; no same-tag pair requires a new-vs-existing comparison.

## Review by Q41

I checked the statement against BLR 10.1 Proposition 7's primitive-line paragraph and checked the detailed arguments against local Stacks sources: limits.tex Tag 0B8W (`lemma-descend-invertible-modules`), Tag 01ZR (`lemma-descend-modules-finite-presentation`); divisors.tex Tag 0BD7 (`lemma-in-image-pullback`) and Tag 0BD9 (`lemma-extend-invertible-module`, source for the existing trait extension); schemes.tex Tags 01JB/01JC (`lemma-glue`, `lemma-glue-schemes`); constructions.tex Tags 01M2/01LX for vector and affine charts; groupoids.tex Tags 0499/049A for the local frame-torsor interpretation. Every step's citation was opened and its full statement copied verbatim into citations.json. No proof-internal construction of a cited node is used.

1. The stalk/localization node supplies exactly the affine stalk identification, and normal-localization supplies normality. The base domain hypotheses are those of the item. Noetherian finite-type and quasi-separated nodes give the qcqs stages. Ring finite type implies finite presentation here because D is Noetherian. The neighbourhood-limit and base-change-of-limit nodes actually state the necessary limits and affine transitions; the index is the set of affine neighbourhoods, not a large category. Base dimension at most one is the prime-chain calculation written in the step.

2. Invertible affine-limit descent states existence of the line model, and the finite-presentation isomorphism descent node states descent of the specified frame and its inverse. The isomorphism is descended on the base, not confused with a global section of Q. Big-open rigidified extension requires normal integral locally Noetherian S and a smooth separated commutative finitely presented group with connected geometric fibres; each has been checked. Its conclusion contains every point of local dimension at most one, hence all of this S. This uses its full statement and does not assume the generic point is open in an arbitrary Dedekind scheme.

3. Smooth base change/composition, separated/finitely-presented composition, finite-type composition/base-change, and geometric connected-product components supply precisely the properties claimed for Q^n. All powers have an identity and nonempty fibres. The normal-group vertical-divisor node applies with that group structure. Smooth-flatness gives the explicit injection after localization at D minus zero; the local difference of two line maps is a scalar, so equality on the generic fibre implies equality everywhere. This is the elementary calculation later reused for coherence.

4. Tensor/pullback and duality nodes supply the Hom line M. The divisor node states the local-rational-section divisor and the zero-divisor criterion as well as vertical descent. The support has finitely many irreducible components because Q^2 is Noetherian; the cited finite-components node states exactly that. A component disjoint from the generic fibre lies over one closed point of the one-dimensional integral base, so a dense open V exists. The identity tuple has a canonical frame of M from the extended unit. Locally s=hvw, with v a regular unit; its generic coefficient at the identity is one. Thus h is a base unit. I specifically corrected the tempting invalid inference of pulling an arbitrary rational function back along the identity: only the regular unit v is pulled back. This proves extension of the specified multiplication rather than merely an unspecified primitive isomorphism.

5. Pullback/tensor coherence supplies the common source and target lines. Associativity, symmetry and the two unit axes are compared on Q^3, Q^2 and Q respectively. They agree generically by the hypotheses and hence everywhere by step 3. The step is elementary after that calculation; it does not assume coherence automatically.

6. The gluing node states existence of a scheme with the prescribed open charts. The overlap coordinate formula is written with the inverse transition unit and its cocycle follows from changing frames. The representability bijection is proved by gluing local units to frames, not asserted from the Laurent-algebra node, whose statement assumes representability. Empty list r=0 gives Q directly. No new gluing or frame lemma was created because the argument is a direct application of the existing gluing theorem and the definition of an invertible module.

7. The scheme Yoneda node is the full Hom(h_X,F)=F(X) statement and supplies morphisms from natural test-scheme formulas. Duality gives the perfect pairing along (1,[-1]); local inverse coordinate c^{-1}z^{-1} is a unit, so inversion is a scheme morphism. This checks the missing inverse axiom rather than constructing only a monoid. Commutativity is supplied by the symmetry hypothesis, and associativity and unit by step 5.

8. Fppf covers are fpqc by the cited covering node, and the representable-descent node explicitly gives unique gluing of maps to any scheme, hence representable fppf sheaves. The scalar-frame calculation computes the kernel on every scheme, and local trivializations lift each point of Q on a Zariski cover, which the covering node says is fppf. This is sheaf exactness, not surjectivity on all global point sets. No hypothesis of a global trivial line or a proper group is used.

9. Only after representability is established is the frame-product Laurent-algebra node applied. Its arbitrary-scheme-base hypothesis covers this Dedekind situation, unlike the existing field-only torsor-frame geometry node. Smooth affine-space and smooth-open/source-locality nodes apply to Laurent charts. The finite presentation R[z,w]/(zw-1) is explicit; finite-type composition proves finite type over S. Affineness gives quasi-compactness; the surjective multiplication ring map proves the relative diagonal is closed on its covering charts. The separated composition node then proves separatedness over S.

10. Smooth-flatness and flat-lfp-openness give openness after every base change. The Laurent polynomial ring over each residue field is a domain, so the fibre is integral and connected. The clopen partition argument shows connectedness over every field extension of every residue field; it does not confuse geometric connectedness with connectedness just over the original base field. The zero-dimensional group Q=S, trivial input line, nontrivial line pulled from S, empty list, and residue fields of any characteristic were all checked. The identity rigidification cancels any base twist, and no excellence or properness is introduced.

No step exceeds 2000 characters. I checked B1–B10, C1–C8, D1–D5 and E1–E7: there are no new statement-only nodes to restate a clause, no unsearched facts, no source-proof references in place of a proof, and no dependence cycle through the line/divisor nodes. Generic tools outside the unit are declared in split_report.tool_uses; these do not alter the unit route. The preliminary server review_split passed with zero new nodes. There was no returned-delivery order and no second worker in this direct-delivery brief.

## Unfinished work

None in the authorized stage-1 split. No Lean is written or compiled. The existing lower nodes retain their own current proof status. Full delivery dry run and push are performed after this report.
