# Stage-1 delivery: lem-sfb-zariski-torsor-categorical-coarse-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-zariski-torsor-categorical-coarse-descent.json: item split into eight proof steps; no exact Mathlib match.
- citations.json: 23 verbatim statement quotations, covering every step/node citation.
- report.md: this report. searches.jsonl is the search command's unmodified log; write_split.py is sandbox-only preparation.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves used: lem-pc-zariski-coverings-are-fppf and lem-pc-yoneda. No Lean was written or compiled.

## Attachments

None. Searches for the item's blueprint tag, categorical/coarse/quotient-stack names and torsor-invariant constructions in lean/WeilConjectures found no declaration of this statement. The torsor-invariant-section declarations concern coefficient sheaves and do not state maps from a torsor fibred groupoid or its coarse universal property.

## WANTED

None for this item. All sources used are present in literature/stacks-project/.

## Corrections and provenance

The live item was unsplit and the sandbox contained no item, split or report. I retained the live statement and all hypotheses and conclusions, repairing only its doubled TeX backslashes. There is no mathematical statement dispute. In particular, q's universal property is for all algebraic spaces, not merely schemes, and the point-orbit bijection is a separate hypothesis. Neither quotient existence nor projectivity is proved or assumed implicitly.

The nearest-ancestor command reports None: the inherited created.item chain eventually reaches the non-node module item Sheaf.SixFunctors.CtfStabilityDirectImages. I retained the inherited null blueprint.from.node and full via list; the inherited nonempty place explicitly names det-thm-sf-ctf-stability-direct-images proof (3) and the intermediate moduli prerequisite. The current latest blueprint proof (3), read in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, uses compactification. The extra alteration/moduli expansion is inherited agent work, not text I attribute to that source. My split realizes precisely lem-sfb-unpointed-stable-coarse-projective step 7, without changing any unit or chapter record. This item is not the unit's key node, so its realized fields are untouched.

## Not duplicates

No new nodes. The cover-comparison fact already exists as lem-pc-zariski-coverings-are-fppf; the general scheme/presheaf Yoneda evaluation already exists as lem-pc-yoneda. I used these rather than creating auxiliary nodes for them. Blueprint searches for torsor, Yoneda, categorical quotient, algebraic space, 021N and Zariski covering found no blueprint statement of the whole item. Tag and concept searches across the whole DAG found the exact existing auxiliary facts and the parent coarse-moduli applications, which do not supply this argument.

## Review by Q133

I read Stacks examples-stacks.tex Tag 04UV, section-group-quotient-stacks, including the definition of the torsor pairs, their pullback arrows, and the proof of proposition-equal-quotient-stacks. The right-translation-by-inverse formula there fixes the left-action convention in step 5. I read groupoids-quotients.tex Tags 048F (lemma-invariant) and 048J (definition-categorical). The former concerns a quotient SHEAF; it is not used as an unproved identification of functors from our fibred groupoid. The latter describes exactly the categorical property already assumed for q. The proof is marked agent-written because I give the explicit Zariski argument rather than claiming Stacks states this whole lemma.

For step 1 I opened the statements of def-trf-algebraic-space, def-weil-pbc-sites-and-cohomology, lem-pc-zariski-coverings-are-fppf, lem-pc-yoneda and def-trf-scheme-algebraic-space. They respectively give the fppf sheaf, its equalizer condition, the covering comparison, evaluation of natural transformations, and the actual representable sheaf of a scheme. I also read spaces.tex Tag 025Y (definition-algebraic-space), sites.tex Tag 00VM (definition-sheaf-sets), topologies.tex Tag 021N (lemma-zariski-etale-smooth-syntomic-fppf), and categories.tex Tag 001P (lemma-yoneda). Thus gluing takes place in B(T), identified by Yoneda with maps, and applies equally to h_Q. The Mathlib precoverage comparison at Sites/Fpqc.lean:44 was also read. These statements require neither separation nor quasi-compactness of B or T.

Step 2 is an elementary coordinate calculation in the stipulated trivial torsor: in the i-th trivialization the other section has coordinates (g_ij,t), so u(s_j)=g_ij u(s_i) as scheme maps. Invariance therefore gives actual equality on overlaps, not only equality on geometric points. This calculation is written out and is not hidden in a new node. It uses only the objects and hypotheses of the item.

Step 3 uses exactly the same four sheaf/cover/Yoneda statements cited there: glue f u s_i, compare choices on their common open refinement, and test the equality on E using its open cover. The formula for f u on G times U is written explicitly. Uniqueness uses the local sections s_i, so it does not silently apply fpqc descent to E -> T, which need not have any of the finiteness properties required by some descent lemmas.

Step 4 cites the sheaf/cover statements for checking equality on the inverse-image cover and the fibred-groupoid definition in def-sfb-stable-pointed-moduli-groupoids for arrows over base maps. The actual inverse-image sections are specified. Functoriality, identities and composition then follow from equality in a discrete target; no stackification or effective descent of objects is being used.

Step 5 uses the full presheaf Yoneda lemma, not merely fully faithful representables: lem-pc-yoneda's statement explicitly allows every presheaf F. Naturality of A on trivial torsors gives a transformation h_J -> B. I tested the orientation of the equivariant isomorphism P_x -> P_(g x): h maps to h g^{-1}, which commutes with u because (h g^{-1})(g x)=h x. I use the universal pair over G times J, so the argument proves invariance of morphisms, without relying on pointwise equality over fields.

Step 6 uses the cited equalizer condition and covering comparison to prove both inverse identities. A(E,u) locally equals f u s_i because (h,t) maps to h s_i(t) is a torsor-pair isomorphism. The definition node for fibred groupoids states what functors and natural isomorphisms over the base mean. An equivalence e has a quasi-inverse; a natural isomorphism into a discrete fibred groupoid forces equality on objects and then on arrows, so no extra lemma is concealed in the transport. The local formulas also prove naturality under B -> B'.

Step 7 cites the representable-space and coarse-definition nodes; the categorical bijection of q is an explicit hypothesis of the item. Restriction of b pi to the trivial torsor is b q x, exactly the compatibility requested. The universal property is for all algebraic spaces, with no extra hypotheses. There is no new quotient-existence claim.

Step 8 uses only the definition of coarse moduli and elementary torsor formulas. Over Spec Omega a nonempty open is the whole space, so the assumed Zariski local triviality itself gives a section; no theorem about fppf torsors over algebraically closed fields is needed and no smoothness hypothesis on G is added. I checked the two directions of the isomorphism/orbit condition: an equivariant map is h -> h a, commuting with u iff x=a y, and this same formula constructs its inverse when x=a y. The given orbit bijection for q then proves precisely the geometric-class clause. Algebraic closedness is used only to invoke that assumed bijection.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the node and sources. There are no new statement-only nodes to audit, no duplicate-node pairs to distinguish, no unstated auxiliary quotient theorem, and no step over 2000 characters (lengths 550, 627, 578, 541, 551, 797, 467, 870). The mathematical content stays in the item's steps rather than being relabelled as new clauses. Empty T is covered by the empty-cover equalizer; the trivial group gives the ordinary Yoneda map J -> Q; J empty permits only empty torsor-pairs over nonempty bases and causes no failure of the local construction. Nontrivial stabilizers act by automorphisms and become identities in B, as required for a coarse rather than fine moduli statement.

The logged Mathlib searches were all run with msearch.py and read. The second conceptual phrasing returns sheaf-Hom and locally-bijective-module morphism comparisons, whose hypotheses and objects differ from this fibred groupoid. The first phrasing returns scheme local representability, affine-space coordinates and local equality of scheme maps, while LeanSearch returns descent of morphism properties. None states the item or specializes to it in one line. I preserved the inherited searches and appended only the six actual logged queries with their results. Services returned successfully.

## Unfinished work

None in the stage-1 split. The server dry run and direct delivery provide the final mechanical checks; no local DAG/preflight scripts are run.
