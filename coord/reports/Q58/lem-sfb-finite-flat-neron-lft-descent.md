# Stage-1 delivery: lem-sfb-finite-flat-neron-lft-descent

Group Q58, 2026-10-24. Only the sandbox was written; no Lean was written and no compiler, Lake, build or repository git command was run.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-flat-neron-lft-descent.json: item, statement retained, five-step split.
- dag/nodes/sec-six-functors-basics/lem-sfb-neron-lft-weil-restriction-geometry.json: new statement, unsplit, no Mathlib match. Gives a scheme, smoothness, separatedness, adjunction/base-change compatibility, finite-type generic fibre and finite-type identity component, without asserting descent or a Néron mapping property of the restriction.
- dag/nodes/sec-six-functors-basics/lem-sfb-dedekind-lft-generic-subgroup-closure.json: new statement, unsplit, no Mathlib match. Gives the flat closed subgroup closure and factorization from flat test schemes over a Dedekind domain, allowing a non-quasi-compact ambient group.
- dag/nodes/sec-six-functors-basics/lem-sfb-lft-closed-subgroup-group-smoothening.json: new statement, unsplit, no Mathlib match. Gives the universal smoothening of a flat generically smooth closed subgroup in a smooth ambient lft group with finite-type identity component. No Néron mapping property or finite extension occurs in its hypotheses or conclusion.
- citations.json: a literal statement quotation for each use in each proof step.
- searches.jsonl and research/: actual command log, complete returned signatures and research orchestration. The existing item's O4 search records are retained; additional Q58 searches cover the item and each new node with leanfinder, loogle, grep and leansearch, including a second semantic phrasing.

Three new nodes, zero Mathlib leaves. New statement-only nodes have empty proof/proof_deps and null proof_origin. All four node files have blueprint.from.place and blueprint.same_as filled. The ancestor command returns None for this existing created-node chain; that null ancestor and the full inherited via list are preserved, with the item prepended for its children. No blueprint identity was invented. The current latest blueprint unit is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This item is an auxiliary trait-extension input below the ordinary-direct-image route, not the unit's own theorem, so no realization fields were changed.

## Attachments

None. Searched lean/WeilConjectures/ by the exact blueprint id and by Neron, Néron, smoothening and Weil-restriction concepts, and also searched lean/Sheaf/. There is no declaration for the item. The scalar-restriction and smooth-envelope hits concern other notions.

## WANTED

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models (1990), local PDF literature/bosch-lutkebohmert-raynaud-neron-models.pdf, especially 7.1 Theorem 5 and Corollary 6, 7.6 Theorem 4 and Propositions 5–6, and 10.1 following Definition 1 and Proposition 4, for the item and its three new nodes. The local PDF is absent. Read the primary-source scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf (PDF pages 180–181, 200–204, 296–297). No document was downloaded or repository literature list edited. The assembly is conservatively recorded as agent-written while the local copy is wanted.

## What needed repair

The live item had a correct statement and no proof, not an existing completed split. BLR 10.1 Proposition 4 matches finite flat Dedekind extensions and smooth closed subgroups; the commutative restriction here is harmless. The statement is unchanged. No STATEMENT-DISPUTED claim was found necessary.

The source's last sentence refers back to 7.1/6 instead of repeating the mapping-property verification. Step 5 supplies that verification on every smooth test scheme. Finite-type group smoothening over a DVR alone would not justify the lft global case. The smoothening node explicitly retains the finite-type ambient identity component that controls the defect of smoothness in BLR's lft argument. Neither whole model nor test scheme is assumed quasi-compact. Finite flat is not replaced by finite étale, and no separability, excellence, completeness, or perfect-residue-field assumption is added.

## Not duplicates

lem-sfb-neron-lft-weil-restriction-geometry vs lem-sfb-finite-locally-free-weil-restriction: the existing statement gives only an algebraic space, with no scheme representability, smoothness, separatedness or finite-type identity-component assertion; the new statement provides those needed properties for the special group-model input.

lem-sfb-neron-lft-weil-restriction-geometry vs lem-sfb-finite-locally-free-relative-hom-space: that existing general Hom-space representability statement likewise gives an algebraic space only, without the group geometry needed for group smoothening.

lem-sfb-dedekind-lft-generic-subgroup-closure vs lem-sfb-dvr-flat-generic-subgroup-closure: the existing statement requires a DVR base and a finite-type ambient group. The new statement allows any Dedekind domain and a merely lft ambient group; the ambient Weil restriction here can have infinitely many components, so the existing statement cannot be substituted. It also treats a general closed finite-type generic subgroup without requiring smoothness.

lem-sfb-lft-closed-subgroup-group-smoothening vs lem-sfb-group-model-potential-smooth-normalization: the existing node changes the DVR and provides a finite normalization of an affine finite-type model; the new node stays over the given Dedekind base, permits non-affine non-quasi-compact groups and provides a universal bijection on morphisms from smooth schemes. A finite normalization has no such universal property in the existing statement.

lem-sfb-lft-closed-subgroup-group-smoothening vs lem-sfb-trait-group-finite-smooth-cover: a finite cover after changing a trait is not a group smoothening over the original base and does not give the stated universal factorization.

None of the new statements asserts the item's Néron existence conclusion or a clause obtained by dropping H or replacing it with G. The new closure and smoothening nodes do not mention Néron models at all. Blueprint searches for Néron, smoothening, Weil restriction, generic subgroup, schematic closure and smooth group found no matching imported statement. DAG searches used the same concepts and the source places; the two pre-existing Weil-restriction/Hom nodes and the DVR subgroup-closure node were read in full. No matching project declaration exists for any of the three new nodes.

## Review by Q58

I read BLR 10.1 Proposition 4 and its proof, printed pages 290–291, in the primary-source scan. I compared it with the item's finite faithfully flat inclusion of domains, smooth closed subgroup and locally-finite-type Néron definition. I also read the relevant latest blueprint unit and the inherited chapter/unit records. The source's construction is retained; there is no route change.

For the restriction node I read BLR 7.6 Theorem 4 and Proposition 5, printed pages 194–197, and the group-model paragraph following 10.1 Definition 1. The first supplies scheme representability from affine neighbourhoods of finite fibre subsets, the second smoothness, separatedness and finite-type preservation, and the last supplies the finite-type identity component for a Néron lft-group. The model hypothesis is kept in this node rather than silently assuming a general algebraic-space Weil restriction is a scheme. Its natural bijections explicitly include base change and the finite-type generic group, exactly what steps 1 and 3 use.

For the closure node I read the closure paragraph of BLR 10.1/4 and the factorization paragraph of 7.1/6, printed page 175. The new statement writes out the ideal and flat-test-scheme property so that step 5 does not use an unrecorded property of its construction. The underlying calculation is that the quotient by the kernel of restriction to the generic fibre is D-torsion-free; over a Dedekind domain it is flat (Stacks Tag 0AUW, more-algebra-lemma-dedekind-torsion-free-flat, which I read locally). Flat coordinate rings inject into their generic localizations, so a map vanishing on that ideal generically vanishes on it integrally. Flatness of the product lets multiplication and inverse restrict to the closure, and the group identities descend from the generic identities. This is a genuine lft/global extension of the existing finite-type DVR statement, not a second copy. Its future split must expose the closure gluing and flatness inputs; I have not put a proof in this statement-only node.

For the smoothening node I read the definition of group smoothening and Theorem 7.1/5, printed pages 174–175, and the lft extension in 10.1/4. The finite-type intersection with the ambient identity component bounds the smoothness defect, and translations control the remaining components; special-fibre dilatations preserve the group law and lift maps from smooth schemes. This yields the universal property, not merely a bijection on unramified integral points. The new statement includes this full property for arbitrary smooth X and the generic isomorphism, without asserting any Néron property. It leaves the nontrivial defect-bound/gluing argument to this new node's later split, instead of hiding it in the item's assembly.

Step 1 uses precisely the restriction node's scheme and finite-type generic/identity-component clauses. H is finite type because a finite affine cover of G restricts to quotient affine charts on its closed subgroup; this elementary check was added explicitly before invoking the algebraic-group theorem.

Step 2 uses lem-weil-pbc-closed-immersion-base-change for the inclusion over E', lem-a1-algebraic-space-fpqc-sheaf for equality after the cover, and def-trf-scheme-algebraic-space only to identify the representable sheaf, not for a descent theorem. For any E-scheme T, T_E' to T is finite faithfully flat since the nonzero finite field extension is finite free of positive rank, so the equality theorem's cover hypothesis holds, even for inseparable extensions and nonreduced T. I read lem-sfb-algebraic-group-homomorphism-factorization and its local source, Milne Theorem 5.39, printed p.108. Its statement explicitly supplies the closed image and the fppf quotient by the scheme-theoretic kernel. The functor monomorphism makes that kernel the unit sheaf, so the quotient is H itself. This checks all test schemes, rather than just field-valued points. Both source and target are separated finite-type E-groups, as required; W_E finite type comes from step 1.

Step 3 uses lem-pc-smooth-flat for flatness and local finite presentation, and lem-sfb-scheme-lfp-smooth-flat-base-change exactly with U=X, V=S and T=S'. Its statement gives smoothness at every base-changed point under the flat base morphism, which is what is needed. The restriction node supplies both adjunctions. The middle bijection is the given mapping property of M', and the localization of D' at D minus zero is its fraction field because it is a finite domain over E. Thus the composite really is restriction to the generic fibre.

Step 4 takes flatness, separatedness, group structure and the generic identification from the closure node. The smoothening node applies because W is smooth separated lft, W^0 is finite type and C_E is the smooth finite-type group H. Step 5 takes only the two displayed universal factorization clauses of these nodes, plus the restriction bijection established in step 3. It proves existence and uniqueness of the extension and checks that the recovered generic map is the original one using the monomorphism. The group structure and generic group identification were already provided in step 4; no unproved extension of a group law is smuggled into the final step.

I checked delivery-errors B–E: the new nodes are self-contained statements with explicit notions, source places, genuine logged searches and correct TeX; none is elementary, duplicate, or a restatement of the item. All cited statements were opened and copied verbatim into citations.json, so no proof-only clause or definition is being used as a theorem. The proof follows BLR's construction and contains no circular dependency. I tested the identity base extension, H=G, the trivial subgroup, disconnected smooth groups, nonreduced test schemes, purely inseparable finite extensions, and ramified extensions over nonexcellent DVRs. The argument uses no special-fibre smoothness of the closure. The multiplicative group case confirms why no model is assumed quasi-compact. No step exceeds 2000 characters. The off-unit equality, smooth-flatness and closed-base-change inputs are declared as generic tools in split_report.tool_uses.

## Unfinished work

No part of this one-level split remains unwritten. Proofs of the three new statement-only nodes are future queue items, as required. The local BLR copy remains wanted. Server checks and final delivery are performed by the required launcher commands.

## Delivery checks

The initial server review_split check returned PASS, with the standing advisory that the inherited unit has no realization yet. The first full dry run exited with a launcher transport/timeout traceback, not a proof diagnostic: server SSH preflight exceeded 720 seconds, and the launcher's automatic fallback exceeded 600 seconds. No check was manually run on this machine. Before retrying I clarified the restriction node so the given model M' need only be a group model of the commutative generic group; it is not separately assumed commutative. Its commutativity (and thus that of the restriction) is a consequence of the Néron mapping property's uniqueness, applied to the two products on the smooth square. This removes any extra hypothesis on the chosen model. All existing search questions still apply unchanged.
