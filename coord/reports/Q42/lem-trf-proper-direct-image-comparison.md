# Worker report: lem-trf-proper-direct-image-comparison

## Files written

- dag/nodes/sec-trace-formula/lem-trf-proper-direct-image-comparison.json: statement unchanged; eight proof steps, status split. Existing metadata and recorded searches retained.
- dag/nodes/sec-trace-formula/lem-trf-proper-diagram-compactification.json: new statement-only geometric lemma, status unsplit; no Mathlib match.
- citations.json: one literal statement excerpt for every citation in every item step.

## Attachments

None. I searched both source trees for the exact blueprint tag and for compactifiable/cohomological comparison terminology, and read the proper-correspondence source's interface. There is no project declaration stating the seven requirements of this item. The upstream master is reference only, and no sorry declaration was treated as finished.

## Literature wanted

None. I read Varshavsky, Remark 1.1.3 and §§4.1.1–4.1.4(a), from the local PDF, with its text extracted to varshavsky.txt in this sandbox. The item and the new geometric node both follow that source. I also read the current blueprint locality ancestor and its unit and chapter records. The proof keeps the proper-direct-image factor of the normal-cone route. No SGA source is used.

## What was wrong and what changed

The repository already contained a reviewed proof but status unsplit. Its 2229-character duality step combined trace normalization and the evaluation/internal-adjunction computation; its 3744-character compactification step hid a separate simultaneous graph-closure lemma and the open-restriction comparison. I retained its mathematical argument and hypotheses. The geometric subclaim now has its own node, without moving the seven axioms into a new theorem. The item still constructs all data and proves (I)–(VII). The duality calculation now cites the existing lem-trf-dual-pushforward-evaluation-counit, and the proper mate/restriction calculations cite lem-trf-compact-composition-proper-square-normalization. I removed the no-longer-used Nagata proof dependencies from the item, since those belong to the new geometric node's future split. No statement dispute or unit-route error was found.

No earlier sandbox node, report or search log was present when I started. I copied the current item before editing, preserved its previous searches and reviewed metadata, and recorded only additional actual searches made with msearch.py. All original proof steps are accounted for; the report's geometry notes below retain the previous construction for the next worker.

## Mathlib and duplicate searches

For the new node I ran LeanFinder twice (proper morphisms of correspondences, then simultaneous graph compactification), Loogle with IsProper and compactification, LeanSearch on the commuting graph-closure diagram, and two Mathlib greps. I read the returned signatures: properness cancellation/composition, a quasi-compact immersion's schematic-image pullback, affine image factorization, and closed-immersion lifting do not supply existence of simultaneous proper compactifications. The greps found no compactification theorem in AlgebraicGeometry. These are ingredients, not a one-line specialization proving the new node. The successful LeanSearch result and all other actual records are in searches.jsonl and the new node. A separate item LeanSearch request was rate-limited; I recorded unavailable, not absence. The item semantic hits were generic derived-functor factorization, not comparisons of correspondence fixed diagrams.

I searched all DAG statements by compactification/extension/diagram/correspondence, ran blueprint_refs.py searches for compactification, proper push, proper correspondence and graph closure, and searched the Lean sources. The blueprint search results are saved beside this report. No blueprint node states the new geometric result; its from.node is lem-trf-local-term-locality, with the complete existing ancestry prepended by this item. same_as is empty.

## Not duplicates

lem-trf-proper-diagram-compactification vs lem-trf-proper-direct-image-comparison: the new lemma is a coefficient-free geometric existence theorem, with no sheaves, six operations, tensor maps, duality or seven axioms. The item uses it only for the geometry needed in (VII), then proves the fixed-square and operation restriction assertions itself.
lem-trf-proper-diagram-compactification vs det-nagata-theorem-dense: Nagata compactifies one morphism; the new statement simultaneously preserves two commuting leg equations and gives inverse-image identities for both proper vertical maps.
lem-trf-proper-diagram-compactification vs sk-lem-nagata-sketch-graph: that theorem modifies a compactification of a quasi-compact open by a blow-up to extend it over an ambient scheme. It does not state compactification of a proper correspondence diagram with four dense opens and Cartesian restrictions.
lem-trf-proper-diagram-compactification vs lem-weil-pbc-compatible-compactification-triangle: that statement compactifies a composable pair and factors the source through the preimage of a target open, without requiring that factor to be an isomorphism or preserving the two correspondence equations.
lem-trf-proper-diagram-compactification vs def-trf-cohomological-comparison: a definition prescribing axiom (VII) does not prove this coefficient-free compactification theorem, and the new theorem does not assert axiom (VII)'s functorial coherence.

## Review by Q42

I checked delivery-errors B–E with the two JSON files, Varshavsky's text, and every cited node statement open. I did not infer theorem content from a node's proof. In particular the formal Verdier-exchange isomorphism alone does not identify the evaluation-defined map, and an arbitrary compactification alone does not make the open restriction square Cartesian. Those were the two places requiring explicit attention.

Step 1 uses coefficient-conventions and coefficient-pushforward for the finite coefficient domain and both commuting leg equations. I read fixed-map-proper: it actually states properness of the induced fixed map and p×p. Admissibility supplies the specified constructible adjunctions; package (3) gives proper coincidence. The comparison definition supplies the types and the two mate recipes. Thus no Cartesian assumption on the original leg squares was introduced.

Step 2 uses the multiplication formula in kernel-pushforward-maps and the signed tensor and ordinary adjunction conventions. Transposing the two associative parenthesizations gives the three ordinary counits; transposing the symmetric variants gives their signed permutation. At s the map is the identity counit. These are the actual tensor maps, not chosen isomorphisms between their endpoints.

Step 3 uses package (3), the composite-adjunction statement of fix-prop-adjunctions (3), admissibility, and the comparison's ordinary mate recipe. Ordinary composition gives (III); the tensor square has the same two counits after transposition, giving (IV). These operations are defined on the finite-Tor constructible inputs already fixed in step 1.

Step 4 checks the trace counit, using the explicit exceptional composite-counit formula from fix-prop-adjunctions (3) and conjugate exceptional composition from admissibility. Kernel-pushforward-maps defines tau and chi by exactly the resulting composite, so delta=tau and d=chi. This is an equality of maps established by their transposes.

Step 5 uses fix-lem-tensor-adjunction's internal adjunction for one exceptionally admissible proper p and N=omega. Package (5) is applicable because M and the test objects are finite-Tor constructible. I read both formulas in dual-pushforward-evaluation-counit: one is the defining evaluation identity, the other identifies mu with the counit-defined projection map. The displayed Hom calculation uses those formulas and naturality to show that the internal-adjunction isomorphism is exactly chi, including the signed symmetry. It makes no unrestricted pro-etale adjoint assumption and does not merely use the existence of an unspecified duality isomorphism.

Step 6 uses the comparison definition for the ordinary and exceptional mates and fix-prop-adjunctions (3) for their counits. Compact-support composition is thm-sf-comp-composition on etale-origin inputs; constructible finite coefficients carry that domain, as in the conventions. I checked proper-square-normalization (1): it explicitly identifies compact-support composition with the specified ordinary composition on a proper square. Applied with t=p_V and t_W=p_U, it makes the two mates inverse; mere independence of compactification would not by itself be a sufficient citation for that equality.

Step 7 uses the new geometric node only for its explicitly listed compactifications, extended equations and the two Cartesian squares. Substitution in the two fixed-scheme fibre products proves the remaining fixed square, even though neither original leg square is Cartesian. The fixed products and induced fixed map are defined in coefficient-pushforward and cohomological-comparison. Steps 1–6 can be applied to the extended proper maps without using (VII), so there is no induction or circular application of the item.

Step 8 uses package (4) for invertible proper base change on the now-Cartesian open squares. Fix-prop-adjunctions (4) supplies its actual counit mate; fix-lem-exchanges (1),(2),(4) supply whiskering, pasting and compact-support composition compatibility on these same finite-stage witnessed inputs. Proper-square-normalization (2) identifies the open compact-support map with the adjoint of inverse open base change. I checked that both horizontal maps there are open and both vertical maps proper, as required. Transposing separately the tensor, ordinary and exceptional comparisons gives the restricted counits and composite counits, yielding the rho compatibilities of the comparison definition. The open exceptional identification is the one specified by that definition, not an arbitrary isomorphism.

For the new node I read Varshavsky §4.1.4(a)'s final paragraph and Remark 1.1.3. The geometric argument preserved below checks why graph closure gives dense opens, why the equations extend scheme-theoretically, and why properness forces the inverse-image open identities. All schemes remain separated finite type over a field; no initial proper-over-k hypothesis is needed. I tested empty schemes, identity p and q, schemes already proper, nonreduced graph closures, and non-Cartesian leg squares. Density plus a closed equalizer is used scheme-theoretically for equations, not just equality on a dense set of points. A proper open immersion with dense image is surjective and hence an isomorphism. These checks exclude the two common compactification gaps.

I examined every old long step for independent claims. The graph-closure existence result is extracted as one unsplit geometric node. The remaining duality argument is a single adjunction-transpose calculation using two existing identity nodes; it is now written as trace normalization followed by its Hom computation. No new node merely restates an axiom of the item; no new proof or proof sketch is stored in the new node. All eight current non-elementary steps are below 2000 characters. No Lean or compiler/build operation was run.

## Geometric construction retained for the next worker

The following is report material only; the new node is deliberately statement-only. It records the original construction that should prove it. Choose dense compactifications Y→Y* and B→B* over Y*×Y* by Nagata. Choose X→X′ and take the schematic image of its graph in X′×Y* to get X*. Choose C→C′ and take the schematic image of (j′,u_Bq,(u_X×u_X)c) in C′×B*×X*×X*. Both maps from the original schemes are quasi-compact immersions, so their maps to their schematic images are dense open immersions. Closed subschemes of products of proper schemes are proper. The equalizers b_i*q*=p*c_i* are closed and contain the schematically dense copy of C, hence are the whole schematic image. Every extended map from a proper scheme to a separated k-scheme is proper. Finally X→p*^{-1}(Y) is an open immersion proper over Y; its image is both closed and dense, hence all of p*^{-1}(Y), and similarly for C and B. This proves the two Cartesian squares. The existing nodes det-nagata-theorem-dense, lemma-nagata-immersion-open-in-scheme-image, lemma-nagata-scheme-image-universal, lem-weil-pbc-closed-immersion-from-composite, lem-weil-pbc-proper-fp-permanence and lemma-nagata-proper-to-separated-target are ingredients to cite when that geometric node is split. Their statements were opened and read during this audit.

## Unfinished work

No required item work remains. The new geometric node is intentionally unsplit, as required by a one-level stage-1 delivery. There are 1 new node and 0 new Mathlib leaves. The dry run and direct push are the remaining delivery operations.
