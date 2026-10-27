# Worker report: lem-sfb-space-noetherian-ample-neighbourhood

1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-noetherian-ample-neighbourhood.json`: existing statement, split by the proof of Stacks 0D3A. Statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-ample-fibre-section-lifting.json`: one new statement-only prerequisite, unsplit; no Mathlib match. This is the degree-zero lifting consequence of Stacks 0D39 for the structure module.
- `citations.json`: quotes for all 41 step/node citations.
- `report.md`: this report. Search requests and complete responses are retained in `searches.jsonl` and `search-results.json` in the sandbox.

2. Attachments

None. Searches throughout `lean/WeilConjectures/` for the item's blueprint tag and ampleness/fibre/neighbourhood terminology found no declaration proving this assertion. The analogous section-lifting and projective-neighbourhood nodes for schemes do not apply while X is an algebraic space.

3. WANTED

None. All mathematical sources used are available in `literature/stacks-project/`.

4. Problems found and corrections

The item had no proof. The main risk was silently assuming the total space was already a scheme: the existing trace-formula nodes on section lifting, lifted coordinates and a finite projective map all assume this. The argument now establishes schematicity using a finite morphism to a scheme, before applying ordinary scheme ampleness results.

Stacks 0D3A explicitly omits the details of the projective-space construction for algebraic spaces. Step 5 supplies these through the existing scheme quotient-classification and etale morphism-descent nodes, including descent of the twist isomorphism and identification of the prescribed fibre map. No new node restating the item or its schematicity conclusion was created. A proposed separate projective-map node was unnecessary once those existing statements were read in full. A proposed proper/locally-quasi-finite node was also unnecessary: the statement of `lem-sfb-stack-separation-composition` already explicitly asserts that a proper locally quasi-finite algebraic space over a scheme is finite and is a scheme. Step 7 quotes that actual sentence, not its proof or an inferred stronger theorem.

The source concludes ampleness from the finite pullback of O(1). Step 9 instead writes the affine standard-chart argument: the lifted sections are sections of a positive power of L and have affine nonvanishing opens, so the definition gives ampleness of L itself. This also avoids incorrectly using a node which only gives the forward implication about positive powers.

The inherited `blueprint.from.node` is null; `tools/blueprint_refs.py ancestor` also returns None for this created-item chain. I retained that provenance rather than inventing an ancestor. The detailed inherited `from.place` and `via` chain are retained and extended in the new node. I read the newest blueprint direct-images proof at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). It currently invokes proper direct-image stability as a black box; this item supplies a lower-level algebraic-geometric prerequisite in the existing alteration/moduli chain. No unit statement or route was changed. Generic tools from other units are declared in `split_report.tool_uses`.

5. Unfinished work

The single new prerequisite is intentionally statement-only and remains a stage-1 queue item. No Lean was written and no compiler, Lake or build tool was run. The delivery checks run only by the required server-backed tools.

## Not duplicates

The new node's source tag 0D39 has no existing DAG node. I searched all `dag/nodes/` for 0D39, `lemma-ample-on-fibre`, lifting/fibre/sections and the mathematical statements; I also ran `tools/blueprint_refs.py search` on ampleness, sections/fibre, sections/projective and proper/quasi-finite. The broad ampleness search returned 47 blueprint nodes, none with this algebraic-space lifting statement.

- lem-sfb-space-ample-fibre-section-lifting vs lem-trf-ample-fibre-section-lifting: the existing 0D2M node assumes X is a scheme; the new 0D39 node permits a proper algebraic space with just the given fibre schematic. That difference is essential to the source's proof and cannot be supplied by a one-line specialization of the existing node.
- lem-sfb-space-ample-fibre-section-lifting vs lem-trf-fibre-embedding-lifted-coordinates: the existing node assumes a scheme total space and already chooses a projective embedding of its fibre; the new node only lifts arbitrary sections in high powers, without any embedding or generation conclusion.
- lem-sfb-space-ample-fibre-section-lifting vs lem-sfb-relative-norm-pair-interpolation: the existing node concerns a specific integral H-projective curve with a group action and norm sections, not arbitrary high-power section lifting on algebraic spaces.

The scheme proper/quasi-finite theorem found by Loogle and grep is `AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`, `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:373`; I read lines 373-386. It assumes schemes and cannot prove representability of the source space. Likewise I read the candidate `Proj.fromOfGlobalSections` at `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:443`; its source is a scheme and it uses a graded-ring map to ordinary structure-sheaf sections, not a nontrivial invertible sheaf on an algebraic space. Neither is a match. The new lifting node's other hits concern basic-open localization of regular functions, stalk surjectivity of scheme morphisms, or pullbacks, not the cohomological lifting assertion. Both semantic phrasings and all three kinds of search were actually run with msearch.py; the exact responses are retained and the node records exactly those queries.

## Review by Q113

I read the item against `spaces-divisors.tex`, Tag 0D3A, label `lemma-ample-in-neighbourhood`, from its statement through the entire proof. Its Noetherian base, proper space morphism, invertible module and ample schematic fibre are exactly the hypotheses of the item. The definition in 0D31 and scheme-base sanity check 0D32 justify the item's representable/scheme relative-ampleness interpretation. No statement correction or statement dispute was needed.

For the sole new node I read Tag 0D39, label `lemma-ample-on-fibre`, including the final surjectivity statement and its proof. Specializing F to O_X gives the high-power section lifting used in 0D3A. The bound is chosen before the exponent and section; the representative neighbourhood may depend on both. O_X is coherent in the proper-over-Noetherian situation. The new node does not assert simultaneous lifting for infinitely many sections, or extension over a fixed neighbourhood. It introduces its own objects and definitions, carries no proof sketch or proof dependencies, and was compared with existing scheme nodes and actual Mathlib hits before creation.

Step 1 uses the ringed-etale-topos model and the Zariski/etale quasi-coherent equivalence for precisely their pullback and invertible-module assertions; the comparison is not assumed for a nonschematic total space. The empty-fibre argument uses only closedness in the properness hypothesis, affine neighbourhoods and the vacuous ampleness criterion. Pulling back local trivializations proves the elementary tensor-power identifications explicitly.

Step 2 uses the new lifting statement only for its bound, proper base change only on the fibre, and the existing eventual-power-immersion statement only after X_t is known to be a scheme. I read Morphisms 01VS/01VT for this choice of exponent. The quotient-geometry node explicitly gives separatedness of projective space, and the proper-over-separated and proper-immersion-closed nodes turn the immersion into a closed immersion. The standard-chart node says that pulled-back coordinates generate; quotient classification identifies the resulting fibre map with the chosen immersion. The exponent is positive and satisfies both independent bounds.

Step 3 invokes the lifting node separately for a finite tuple at this same exponent. Finite intersection and the affine-open basis produce one neighbourhood; proper base change justifies the restriction. No Noetherian claim about an arbitrary new base is used.

Step 4 checks the generation locus on etale trivializing scheme charts by the actual principal-open formula. The invariant-open/morphism-descent node explicitly provides descent of that open. Removing the closed image of its complement under the proper map ensures generation on every point, not merely on the fibre.

Step 5 cites the actual statement of `lem-trf-projective-bundle-quotient-geometry`, which gives quotient classification, its twist isomorphism, and naturality for arbitrary scheme pullbacks. I read Constructions 01NE and the quotient discussion after 01OB, together with Spaces Divisors 0D2Z and the omission in 0D3A. `lem-trf-etale-open-chart-morphism-descent` gives the unique descended map and its description on every scheme test. Agreement of the twist maps is checked on their generating coordinates, and their inverses glue as module-sheaf morphisms. Thus no unsupported claim of naturality or identification is hidden in the step. The argument stays below 2000 characters.

Step 6 uses projective-space properness, scheme closed-immersion base change on every test of the diagonal, closed-subspace properness, proper base change and composition. The graph square is specified; its relevant diagonal is Delta_q, not Delta_f or a different fibre product. This establishes properness of phi while X is still a space.

Step 7 uses the open quasi-finite-locus statement and the finite-fibre criterion for spaces with separated finite-type map to a scheme. Properness of phi from step 6 gives exactly those hypotheses. Its fibre over any point of P_t is a base change of j, so it is empty or one point; closed-immersion base change is cited for that assertion. Removing the proper image of the bad locus makes the restriction locally quasi-finite. The existing stack-separation node's explicit proper/locally-quasi-finite space assertion is used at this point. I checked its truth against Spaces More Morphisms 0A4X, `lemma-characterize-finite`; the scheme-only Mathlib theorem is not substituted for it. Both the target W and resulting finite source are schemes.

Step 8 uses closedness of q already proved in step 6 and the affine-open basis to shrink the base, not just P. The finite scheme restriction is verified from the affine definition; there is no unjustified factorization through a closed subscheme merely from image containment. The identified quotient morphism comes from the test-scheme normalization already proved in step 5.

Step 9 reads the exact scheme chart-preimage statement and the standard-chart affineness statement. Finiteness supplies affine inverse images; the proper map over the affine base supplies quasi-compactness. The definition of ampleness applies to sections of L^d itself. For every affine B inside the final affine V, the cited affine-scheme and affine-base-change statements make X_B -> X_V affine, and the affine pullback ampleness node gives the final relative condition. I checked the difference between absolute ampleness on X_V and relative ampleness on every affine inverse image explicitly.

Small cases checked: X_t empty (handled separately); T a field spectrum (section lifts are tautological); d0=0 (the chosen d is still at least one); r=0 (projective space is the base); zero sections not generating away from the fibre (the closed-image deletion is essential); nonreduced closed fibres (closed subschemes of a field spectrum are still empty or a point); a nonflat proper family (no flatness was inserted); and arbitrary nonclosed t (no closed-point hypothesis was used). In the new node, X may be a nonschematic proper algebraic space away from t; no step assumes otherwise before finiteness. I checked all B-E return categories, specifically that no new node merely restates a clause, no citation uses a cited proof rather than statement, and all 41 quotes are verbatim. All nine non-elementary steps are below 2000 characters. The dependency closure inspection found no cycle through the item. All corrected choices above were made during this self-review; no second worker or agent was started.
