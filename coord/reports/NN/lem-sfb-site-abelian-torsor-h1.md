# Stage-1 report: lem-sfb-site-abelian-torsor-h1

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-site-abelian-torsor-h1.json: existing statement, split into eight proof steps. Not a Mathlib leaf.
- citations.json: one verbatim statement extract for every node cited in every step.
- No new nodes; zero new Mathlib leaves. Searches and the sandbox writing script are working artifacts only.

## Attachments

None. Searched the project library by the exact blueprint tag and by torsor/H1/boundary terminology. WeilConjectures/CategoryTheory/Sites/Torsor.lean has the generic torsor notion but its classification declarations require a terminal site object (in particular nonempty_equiv_H_one_torsor around line 1081). TorsorH1BoundaryRepresentative.lean:51 is a Zariski scheme statement. Neither states this arbitrary-small-site package, and neither is an attachment for it. No Lean was changed or compiled.

## WANTED

None. All mathematical sources used are in literature/stacks-project/.

## Findings and corrections

The item had no proof. Its statement is retained verbatim, including the no-final-object clause and the explicit quotient relation. Stacks sites-cohomology.tex, Tag 03AJ (lemma-torsors-h1), explicitly permits any site and uses global sections in the sense of Tag 01FT. The proof leaves mutual inverseness unverified; the delivery supplies it. The arbitrary-extension boundary formula and addition calculation are proved rather than inferred from the mere existence of a classification bijection. The sign in the presentation is correct: the relation (g,[t]-[g+t]) says [g+t]=g+[t].

The existing blueprint ancestry is broken: blueprint_refs.py ancestor returns None, as does the inherited from.node. The existing from.place and via list are preserved, with same_as=[] confirmed by the whole-blueprint torsor search. The current latest snapshot is main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345. Its direct-image detailed proof is now at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md. It is an auxiliary Picard-obstruction input in the inherited unit, not its key statement; no unit record is changed. No blueprint route is replaced.

## Mathlib searches

The seven inherited search records were retained. Five additional commands were run through the required msearch.py wrapper, with their exact queries and returned names appended to the item's mathlib_searches from searches.jsonl: leanfinder twice, leansearch, loogle and grep. No service was unavailable. Read Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean:52-109 and Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean:9-40. The former defines Ext cohomology, whereas the latter expressly defines fixed-family presheaf Cech cohomology and leaves the sheaf classification as TODO. The grep returned no torsor/classH1 declarations in Mathlib/CategoryTheory/Sites. None proves the item's package. No new node requires a new search record.

## Not duplicates

No new nodes are proposed. Existing lem-sc-torsor-h1 and lem-sc-ext-torsor are scheme-etale statements (the former also Zariski); lem-sc-torsor-h1-ext-pushout is Zariski on a scheme; lem-sc-etale-torsor-pushout-extension and its presentation lemmas concern the small etale site of a scheme. Their statements were read and not used as arbitrary-site classification facts. No generic torsor classification node with every clause and no terminal-object hypothesis was found in the DAG or blueprint. The required generic supporting results are reused below rather than created again.

## Review by NN

I read sites-cohomology.tex Tag 01FT (section-cohomology-sheaves), Tag 03AH (definition-torsor), and Tag 03AJ (lemma-torsors-h1), including the omitted-inverse sentence. I also read sites.tex Tags 00WJ and 00WK, sites-modules.tex Tags 03CN and 03CO, and derived.tex Tags 015B and 05TE. The statement uses derived global compatible sections, so none of the arguments evaluates at an assumed terminal object. No SGA source is used.

Step 1 uses lem-weil-pbc-sheafification-exact for sectionwise kernels and lem-weil-pbc-site-sheaves-enough-injectives for the injective embedding. The statement of lem-weil-pbc-right-derived-universal-delta-functor supplies exactness, naturality, additivity and the degree-zero identification for any additive left exact functor. Here left exactness of global sections is explicitly checked on compatible families. The vanishing for an injective is computed by the identity resolution using def-sp-injective-resolutions and lem-sp-derived-well-defined; it is not an additional unrecorded acyclicity theorem.

Step 2 uses def-weil-pbc-sheafification only for its universal property, the exact-sheafification node for kernels and quotients, and lem-weil-pbc-site-sheafification-sections-local for local representatives/equality detection. The inclusion and projection are verified in the displayed inverse coordinates, so the short exact sequence is not assumed from the source's pushout diagram. The abelian-sheaf epi node is genuinely for every site, and gives epicity from local surjectivity. The local-bijection criterion is also for every site and gives the fibre isomorphism. All these cited node statements were read; none is being used for a scheme-only specialization or for its proof rather than statement.

Step 3 constructs the fibre of an arbitrary extension using the general-site epi statement and sectionwise kernels. The map E_P to E is explicitly defined on both G and the generators; the relations and local coordinates check it. Naturality from the derived delta-functor statement then proves the arbitrary-extension formula and invariance under torsor isomorphisms. The sheafification universal property is sufficient to extend the presented map; no plus-construction formula is ascribed to its definition.

Step 4 uses enough injectives, sectionwise kernels, local surjectivity and sheafification to construct L_q and its extension map to I. The map on the quotient integer sheaf sends 1 to q and makes an actual morphism of short exact sequences, so connecting-map naturality gives the correct positive boundary delta_I(q). Surjectivity is exactly the segment of the long exact sequence proved applicable in step 1.

Step 5 uses the definition of injectivity exactly as stated in def-sp-injective-resolutions: G to E_T is monic by step 2, so i extends to b. The invariant q is constructed by ordinary sheaf gluing over coverings of each object, then checked compatible under every restriction. No final object, enough points, or acyclicity of a torsor is assumed. The map to L_q is explicitly bijective on local torsor coordinates and the cited general local-bijection criterion identifies it globally.

Step 6 takes exactness from the same derived delta-functor statement; equality of the two boundaries means q'-q is r(a) for a global section a of I. Translation by a and -a supplies the explicit mutually inverse equivariant maps. This is elementary once steps 4 and 5 and that exactness segment are available. Step 7 uses exactness only: the global generator [0] lifts 1 for the trivial torsor, so its boundary vanishes.

Step 8 checks the sheafified antidiagonal quotient directly, locally using the coordinate g+h. The equivariant map to I is invariant because i(g) and -i(g) cancel, and def-weil-pbc-sheafification gives its unique extension to the quotient sheaf. The sections-local node justifies using local representatives of that quotient. The local-bijection node identifies it with L_(q+q'). Step 4 then computes the boundary, whose additivity is part of the cited delta-functor statement. This proves the group-law clause rather than citing a new node that restates it.

I checked the presentation at T=G, where t0=0 gives E_T=G plus the integer sheaf; at G=0; on the empty site, where the sheaf category and all groups are trivial and global 1=0; and on a site with two discrete objects and no terminal object, where all constructions are componentwise and global sections are compatible families. The translation sign q'-q=r(a) and antidiagonal sign (g,-g) both agree with the displayed maps. No hypothesis of local nonemptiness is replaced by global nonemptiness. Each step is below 2000 characters, and the original arguments remain in the item itself: there is no extracted or hidden new lemma, no clause relabelling and no new statement-only node to audit. B1-B10, C1-C8, D1-D5 and E1-E7 were checked against the cited files; the concrete correction was to fill the source's omitted inverse verification without assuming the scheme-only classification.

The three non-leaf off-unit facts (local sheafification representatives, the local-bijection criterion and the derived delta-functor theorem) are declared in split_report.tool_uses as generic tools. They do not replace the unit's alteration/Picard route.

## Completion

All mathematical steps and citations are complete. Server dry run and delivery follow; their result is reported in the final delivery response.
