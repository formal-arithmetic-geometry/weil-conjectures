# Stage-1 delivery: lem-sfb-affine-open-derived-qcoh-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-open-derived-qcoh-criterion.json: item split into seven proof steps, with its statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-derived-coherator-adjunction.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-derived-coherator.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-derived-coherator-interchange.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statements for every step/node pair.

Three new nodes, zero Mathlib leaves. Everything was written in the assigned sandbox. No Lean, compiler, Lake or build command was run.

## Attachments

None. Searched WeilConjectures for the item blueprint tag and for coherator, affine derived comparisons, and quasi-coherent derived equivalences. The existing affineQCohDerivedAdjunction_unit_counit and exists_affineQCohDerivedEquivalence_core concern D(A) and D_QCoh(Spec A), not the termwise inclusion from D(QCoh(O_X)) for arbitrary qcqs X. Their transport through the abelian affine equivalence is additional mathematical work, so they are not exact attachments to this item or to the newly stated coherator nodes. DQCoheratorAdjunction concerns a right adjoint to D_QCoh -> D(Mod), also a different domain from the derived coherator in this delivery.

## Wanted

None. All sources used are present in literature/stacks-project.

## Problems found and corrected

The live item was unsplit, with no previous sandbox node or report. Its statement already contains the crucial normalization of the derived comparison, and has been preserved verbatim. The proof of 09T6 writes functor equalities but does not display the identities needed to identify the actual adjunction maps. I made those identities explicit in the flat-interchange prerequisite: they come from the four adjunction Hom identifications in 08D8 and the unit-compatible comparison. This avoids treating mere object isomorphisms as a proof about the unit and counit.

There is no source statement dispute and no replacement of the unit route. The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). The inherited item is a deep lower prerequisite on that route, and its own proof follows Stacks 09T6. The unusual null blueprint ancestor is inherited: tools/blueprint_refs.py ancestor reports None. I preserved it and extended its via chain and precise place on each new node.

## Not duplicates

lem-sfb-scheme-derived-coherator-adjunction vs lem-sfb-qcoh-grothendieck-generators: the existing 077P node states Grothendieckness and exact colimit-preserving inclusion, but not existence of the underived right adjoint or the derived adjunction; the new node states the latter and cites the former for its abelian structure.

lem-sfb-scheme-derived-coherator-adjunction vs lem-sfb-levelwise-quasicoherent-brown: the existing 077P node gives Brown representability for D_QCoh and semisimplicial systems. Its domain is the full cohomologically quasi-coherent subcategory of the ambient derived category; the new node instead constructs Rq into D(QCoh) and is adjoint to termwise inclusion.

lem-sfb-affine-derived-coherator vs new-affine-qcoh-derived-adjunction-unit-counit: the existing node has source D(A) and requires the derived tilde/global-sections models. The new statement is about the coherator adjunction with source D(QCoh(O_T)); identifying the abelian module category with QCoh and transporting its derived functor is needed before the existing result can be applied. It is therefore useful input to a later split of the new node, not an identical statement.

lem-sfb-flat-derived-coherator-interchange vs lem-kun-derived-adjoint-square-comparison: the existing abstract square lemma assumes existence of derived adjunctions and a postcomposed derived-functor property, and concludes compatibility of a comparison without invertibility. The new geometric lemma supplies derived QCoh pushforward for flat qcqs maps and the invertible interchange C_Y Rf_* = Phi_f C_Z; the abstract square can serve in its later proof, but does not state it.

lem-sfb-flat-derived-coherator-interchange vs lem-sfb-affine-open-derived-qcoh-criterion: flat coherator interchange is a comparison of two right adjoints, valid without the conclusion that termwise inclusion is an equivalence. The item's seven-step induction proves that equivalence using this comparison and the affine case; the new node contains no global equivalence conclusion.

lem-sfb-affine-derived-coherator vs lem-sfb-affine-open-derived-qcoh-criterion: the affine case has no affine-open comparison hypothesis and supplies the base calculation used at the middle vertices of the induction. It is a strict special geometric input, not a reformulation of the qcqs criterion.

## Review by N0

I read perfect.tex Tag 09T6 (lemma-argument-proves) from the statement through its entire support induction. For the scheme coherator node I read the opening paragraphs of section-coherator (08D6), properties.tex proposition-coherator (077P), including its representability construction, and derived.tex lemma-derived-adjoint-functors (09T5). For the affine node I read perfect.tex lemma-affine-coherator (08D9), all three clauses and its proof, and the statement and adjunction discussion of lemma-affine-compare-bounded (06Z0). For the flat-interchange node I read all of lemma-flat-pushforward-coherator (08D8), especially the four Hom identifications: the two composites are right adjoint to I_Z P_f, and the normalized comparison identifies their adjunction maps. Its displayed identities have been type-checked on paper: the first starts at Phi_f B and ends at Phi_f C_Z I_Z B; the second starts at I_Y C_Y R_f E and ends at R_f E; the third starts at I_Y H and ends at R_f I_Z P_f H.

Step 1 uses the exact inclusion explicitly stated by lem-sfb-qcoh-grothendieck-generators and the triangulated termwise factorization explicitly stated by lem-weil-pbc-exact-functor-derived-factorization. The new coherator node supplies the adjunction and shift-compatible unit/counit, not merely the existence of a right adjoint with no normalization. The equality of cohomology follows by using the same ambient kernels and cokernels. The inclusion reflects zero cohomology because it is a full inclusion.

Step 2 writes the simultaneous inductive assertion, including closedness of T and the number of affine opens, and proves the zero case. No non-elementary auxiliary fact is used there beyond the usual definition of the derived category: an acyclic complex is zero. The empty scheme is included.

Step 3 uses the last clause of the flat-interchange node for the affine-open inclusion, so flatness, quasi-compactness and quasi-separatedness are not silently assumed for a general open. Its last displayed identity says that c carries I_X of the QCoh-derived unit to the ambient open unit. The triangulated cone axiom supplies both triangles and the exact-factorization node makes I_X of the first distinguished. Only the total derived functor from the item's hypothesis is used; its unit-compatible identification with the derived functor of the new node is allowed by the universal property.

Step 4 uses lem-pc-supported-open-unit-cone-properties, whose statement explicitly assumes qcqs X, closed T and quasi-compact open U, and concludes quasi-coherence, vanishing off T and vanishing on U. I checked all three hypotheses. The over-site to actual-scheme restriction is supplied by def-pc-derived-open-restriction-maps, which explicitly uses Scheme.Modules.overEquiv. Thus both cones have support in the closed subset T minus U, covered by n minus 1 affine opens. I did not use lem-pc-derived-open-unit-cone, which assumes affine X and would be insufficient here. No separatedness of X or affineness of intersections is used.

Step 5 uses exactly the affine unit and counit clauses of the affine coherator node, and exactly the first two displayed identities of the flat-interchange node. I verified the direction of lambda and c in both composites; all intervening maps are isomorphisms, hence the actual middle adjunction components are isomorphisms. These new prerequisites are statement-only, not proof sketches or replacements of the item's conclusion.

Step 6 uses the coherator node for the exact endofunctors and shift compatibility, so naturality really gives triangle morphisms, including their final squares. I read lem-sf-triangle-morphism-iso: it applies to any two isomorphic components, so the middle and third vertices suffice for the first vertex in both triangles.

Step 7 uses lem-weil-pbc-qcqs-finite-affine-open-cover, which states finite affine covers for every quasi-compact scheme and needs no extra separation. T=X is closed. The two natural isomorphisms then give inverse equivalences by the definition of equivalence; no Brown representability is invoked to conclude essential surjectivity.

For delivery-errors B--E I checked complete introduction of objects, definition dependencies, single-escaped TeX, source tags and labels, existing-node reuse, and exact citation strength. Searches of the whole DAG, blueprint_refs search (coherator, 077P, 08D8, 08D9, 09T6, affine coherator, flat pushforward, quasi-coherent derived), latest blueprint text and project Lean found no exact replacement. Each new node has actual msearch LeanFinder, LeanSearch, Loogle and grep queries; the natural-language tools give different phrasings. I read all returned hits. In particular Mathlib's Adjunction.derived needs derived-functor hypotheses and does not construct the geometric coherator; rightAdjointUniq and its unit/counit formulas presuppose the adjunctions. I also read Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean and the quasi-coherent pushforward declarations in Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean. They do not establish any new node in one line.

I tested the new assertions on the empty scheme, the identity flat map, affine schemes over the zero ring and over an arbitrary non-Noetherian ring, zero objects, and complexes unbounded in both directions. For f=id the interchange reduces to coherator naturality and the triangle identities. Affine U=X makes the cones zero, as required. A closed support need not be quasi-compact; the proof only requires its containment in finitely many affine opens, and this follows at the end by T=X. All proof steps are below 2000 characters; none hides a long inline comparison proof. Off-unit support, triangulated and finite-cover nodes are declared as generic tool uses in split_report. All quoted citations are verbatim copies of the cited statements, with one record per step/node pair.

## Unfinished work

None in this one-level stage-1 split. The three new statement-only prerequisites are intentionally left for later workers.
