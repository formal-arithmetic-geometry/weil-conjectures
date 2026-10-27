# Q11 stage-1 report

1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-coherent-exterior-base-change.json: item, statement, split into eight steps; no matching Mathlib theorem.
- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-bialgebra-top-degree-exterior.json: new statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-derived-bialgebra-exterior-rigidity.json: new statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-space-derived-external-cup.json: new statement-only lemma, unsplit; no Mathlib match.
- citations.json: verbatim statements for all step/node citations. Search outputs and searches.jsonl are retained in the sandbox.

2. Attachments

None. I searched the project WeilConjectures source for the item blueprint tag and coherent/exterior/base-change notions. No finished declaration gives every clause, and a sorry declaration is not an attachment. The upstream audit has no finished implementation of this item. No Lean was written or compiled.

3. Literature wanted

WANTED: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 6, relative coherent cohomology of abelian schemes, for lem-sfb-abelian-coherent-exterior-base-change. The relative theorem is not claimed to follow as a citation from Milne's field theorem; the assembly here is agent-written.

WANTED: Borel 1953, the graded Hopf algebra structure theorem invoked in Milne I Lemma 12.2, for lem-sfb-bounded-bialgebra-top-degree-exterior. I read the actual Milne proof; the new node isolates exactly its algebraic equality criterion with explicit counit and algebra-map hypotheses.

4. Corrections and route audit

The item statement is retained, including arbitrary nonflat, nonreduced and non-Noetherian base changes. There is no STATEMENT-DISPUTED correction. The inherited empty proof did not establish the relative assertion. Milne I 12.1 concerns constant-coefficient cohomology and cannot be substituted for coherent cohomology. I use I 8.7(e) only for the dimension of coherent H1, and I 12.2 for the abstract field algebra argument. Constant fibre dimensions alone do not imply local freeness over a nonreduced base. The local bialgebra rigidity input supplies the missing nilpotent-base argument, without assuming smoothness of a relative Picard functor. The external comparison is in the derived category, not merely degreewise, and its multiplicativity is explicit.

During self-review I replaced an unnecessarily narrow Noetherian perfect-pushforward citation by the existing proper-flat-space derived base-change statement, which explicitly gives the Zariski perfect complex and small-etale counit. I also replaced an informal spreading assertion by the existing perfect-Hom filtered-colimit theorem. The source list is honest about the two agent-stated combined lemmas: neither minimal models nor a definition of cup product alone proves them.

The chapter and unit were read. This is a prerequisite for the relative coherent reduced-coproduct calculation on the existing alteration/stable-curve route; no unit step is bypassed. Definitions and the listed off-unit generic tools do not replace that route. Latest-blueprint searches for bialgebra, exterior, Kunneth, Hopf and base-change exterior statements, and whole-DAG/Lean searches by source tags and notions, found no identical blueprint statement. Inherited blueprint ancestry is preserved and each new node specifies the precise role it serves; same_as is empty. I checked existing dependency closures for an occurrence of this item to avoid circular use of the field H1 input.

5. Unfinished work

The stage-1 assembly is complete. The three new general lemmas are intentionally statement-only and unsplit for subsequent workers; they are not claims of finished Lean proofs. There are zero Mathlib leaves. No target statements, library files, launcher tools or repository files were edited.

## Review by Q11

I read Milne AV I 8.7(e), printed page 37, and the entire proof of I Lemma 12.2, printed page 55. For the new field criterion the perfect-field and signed anticommutativity hypotheses match that lemma; degree-one square-zero in characteristic two is part of the conclusion, not an assumption silently inferred from graded commutativity. Connected degree zero, finite-dimensionality, top-degree bound and the actual multiplicative coproduct are stated explicitly. Existing primitive-product and coherent-group-bialgebra nodes do not already state the exterior equality criterion.

For the new rigidity statement I read Stacks more-algebra Tag 0BCC for the minimal finite-free residue model and algebra Tag 00IP for the separated maximal-ideal filtration. The additional argument is genuinely a new algebraic lemma, not either tag's conclusion: start with the minimal differential in the maximal ideal. If it lies in m^n, its next-order term is a derivation and a coderivation of the residue exterior bialgebra, since multiplication and coproduct are chain maps. It kills degree zero by the unit, and sends degree one to a degree-two primitive element by the counit. The reduced coproduct on exterior degree two is the injective alternating map into degree one tensor degree one, also in characteristic two. Thus the next-order differential vanishes on degree one and hence on the whole exterior algebra. Induction puts it in every power of m; Krull intersection kills it. This needs Noetherian locality, not completeness. Once the differential vanishes, the unit and counit identify degree zero and make degree one primitive. The reduced coproduct on degree two has a unit minor because its residue alternating map is injective. A square of a primitive degree-one element is primitive (the two signed cross terms cancel even in characteristic two), so that square vanishes. The wedge map is then defined; its residue map is an isomorphism, and its source and target are finite free with the same binomial ranks, so its determinant is a unit. The case g=0 is just R in degree zero. These are the proof obligations intentionally assigned to the new statement-only rigidity node, rather than hidden in the item's application.

For the new external-cup statement I read spaces-perfect Tags 08IN and 08IR, the small-etale/Zariski comparison Tag 071Q, and sites-cohomology Tags 0FPL, 0FPM and 0H9A. For flat qcqs X and Y the projection square is Tor-independent. Base change identifies the pushforward along the first projection with the pullback of the pushforward from Y; projection formula and affine scalar sections then give the derived tensor comparison. The comparison must be the external cup map defined by the adjunctions; the associativity, multiplicativity, symmetry, unit and arbitrary scalar-extension compatibilities are explicit requirements of the new lemma. No cohomology projectivity is assumed, which is essential before the item's local-freeness argument. Existing projective-cohomology Kunneth has that extra hypothesis and cannot be used at this point. I checked that the new node says kappa is multiplicative; otherwise step 3 would have been an invalid C4 citation.

For step 1 I opened smooth-flat, space-flat-proper-fp-locality and space-geometric-h0. They provide respectively chart flatness, preservation under every base change, and the universal structural H0 isomorphism for geometrically reduced connected nonempty fibres. Smooth fibres supply reducedness; the identity section supplies nonemptiness. These hypotheses are not inferred from connectedness alone.

For step 2 I opened proper-flat-space-derived-base-change, perfect-affine-bounded-projective and affine-qcoh-derived-equivalence. The first explicitly supplies a Zariski perfect derived image with its etale comparison under properness, flatness, finite presentation and relative-flat finite-presentation coefficients. O is free of rank one over itself and relatively flat by step 1. The other two statements give the bounded finite-projective R-complex and its scalar derived-sections interpretation. No perfection assertion is extracted from a mere base-change definition.

For step 3 the new external-cup statement supplies exactly the derived isomorphism, its product compatibility and the pullback/naturality/unit comparisons. The group equalities give the bialgebra diagrams by functoriality. The counit is the identity section, and Delta is the inverse external cup composed with group pullback, not an arbitrary per-degree identification. These constructions commute with scalar extension by that same node.

For step 4 I opened the abelian-variety definition, characterization, coherent H1 dimension, proper coherent finite-dimensionality, dimension-vanishing, and coherent-group-bialgebra statements. The fibre is a scheme by the item's assumption, is proper smooth and geometrically connected, and its field is algebraically closed. These are exactly the field hypotheses needed. Characterization supplies geometric integrality. Finiteness in every degree together with dimension vanishing supplies finite total dimension. The H1 node gives dimension g; the bialgebra node gives H0, counit and multiplicative signed coproduct. The new field criterion then gives exterior multiplication; the new external-cup node identifies the etale product with this Zariski product. Nothing about relative Picard smoothness is cited.

For step 5 I checked the new rigidity statement against the application: R_s is Noetherian local, K_s is perfect, its bialgebra structure is the derived one just constructed, and its residue exterior property descends from the algebraic closure by faithful scalar extension. Squares and kernels/cokernels of the explicit exterior maps descend, not merely dimensions. The lemma's conclusion gives a zero-differential finite-free model and the actual cup exterior map.

For step 6 I opened affine-perfect-hom-colimit: it gives continuity of Hom between bounded finite-projective complexes over a filtered ring colimit. The localization system R_f with f outside the point prime has colimit R_s. Both inverse maps and their two equations descend by this bijection. This proves a finite-free cohomology chart; stalkwise square-zero and wedge-isomorphism claims then glue. The stalk and finite-cover arguments are elementary consequences of the explicitly obtained models and maps, not new hidden general lemmas.

For step 7 I opened flat-space-derived-pushforward-base-change and checked that no flatness of the new base map is required: flatness is that of A over the original base. Pullback of the local zero-differential finite-free model is ordinary tensor even for a nonflat map. This gives the canonical higher-image comparison in each degree. External cup explicitly gives compatibility of these canonical maps with products, identity and composition. The statement does not trade an arbitrary comparison for the canonical one.

For step 8 I opened affine-base-higher-image-sections, the scheme Zariski-etale quasi-coherent equivalence and finite-flat-affine-sections-projective. They respectively identify scalar Hi with sections of Ri, give the appropriate associated module sheaf, and turn finite locally free sheaves on an affine into finite projective modules. The wedge comparison is checked on a finite principal trivializing cover, so the scalar map is the stated cup map. Quasi-compactness bounds the finitely many local ranks and proves eventual vanishing without a uniform-dimension assumption on all of S.

I checked delivery-errors B--E against these files: no omitted non-elementary input is replaced by a definition; every cited node was opened and its statement is quoted verbatim in citations.json; no new node is an elementary step or a geometric clause copied from the item; there is no Picard-smoothness assumption, coefficient-category swap, SGA route, or fibre-dimension-only flatness inference. Each new statement introduces its own objects and all statement dependencies. The degree-one primitive and exterior-square tests include characteristic two, rank zero, nonreduced local rings, varying-rank bases and the zero affine ring. No step exceeds 2000 characters. All actual Mathlib queries and outputs are retained, including second phrasings and the targeted algebra grep; none is represented as unavailable when it succeeded.

## Not duplicates

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sbc-regular-principal-prime-localization-dvr: The existing conclusion is a DVR localization of a domain, whereas the new statement kills differentials of a perfect derived bialgebra over any Noetherian local ring.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sbc-complete-local-subideal: The existing result is completeness for subideals under completeness assumptions; the new result neither assumes completeness nor asserts it, and concerns exterior derived bialgebras.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-trf-formal-coefficient-operator-base-change: The existing theorem concerns formal-series coefficient operators, not perfect complexes or coproduct rigidity.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-trf-flat-graded-fibre-regular-lift: The existing theorem lifts a regular initial form using a flat associated graded ring; it does not kill a minimal complex differential from exterior bialgebra data.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-trf-normal-cone-directrix-minimal-primes: The existing theorem concerns characteristic-zero reduced normal-cone fibres and minimal primes, not arbitrary-characteristic local derived bialgebras.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs def-trf-finite-coefficient-expression: The existing node defines formal coefficient expressions; it states no rigidity theorem about perfect complexes.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sc-principal-ideal-dvr: The existing statement characterizes DVRs among local domains with principal maximal ideal; no such domain or principal-ideal hypothesis appears in the new bialgebra statement.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sfb-bounded-pseudocoherent-residue-model: The existing theorem supplies a finite-free minimal model with residue cohomology ranks, but does not make its differentials zero; the new coproduct argument is the additional conclusion.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sfb-pseudocoherent-point-fibre-line: The existing theorem recognizes a single shifted line from one-dimensional fibres; exterior fibres generally occupy many degrees and require the new bialgebra argument.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sc-connective-universal-h0-zero-differential: The existing conclusion cancels the degree-zero complement using universal H0, not all differentials using an exterior residue bialgebra.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sc-residue-cohomology-zero-complex: The existing splitting is over a field; the new theorem is over a Noetherian local ring including nonreduced rings.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sc-minimal-free-comparison-residue: The existing conclusion compares minimal models after residue reduction; it does not force their differentials to vanish over the ring.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-sc-perfect-local-pseudocoherent-free-model: The existing statement gives a minimal free model with potentially nonzero differential; the new bialgebra hypotheses force zero differential and exterior multiplication.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-weil-pbc-finite-module-complete-over-complete-noetherian: The existing result is completeness of finite modules over a complete ring, not a derived bialgebra rigidity theorem and not applicable without completeness.

lem-sfb-perfect-derived-bialgebra-exterior-rigidity vs lem-weil-pbc-krull-intersection-localization: The existing result makes an ideal-adic intersection vanish near V(I); it does not supply the derivation/coderivation calculation that puts a differential in that intersection.

lem-sfb-flat-space-derived-external-cup vs lem-wf-curve-trace-cup-naturality: The existing result is finite-coefficient curve trace compatibility; the new theorem is a structure-sheaf derived external-cup isomorphism for flat spaces.

lem-sfb-flat-space-derived-external-cup vs lem-wf-etale-cup-functoriality: The existing theorem gives ordinary etale cohomology pullback functoriality for abelian sheaves, not derived coherent Kunneth invertibility.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-projective-cohomology-coefficient-kunneth: The existing statement assumes bounded finite-projective cohomology and gives cohomological coefficient formulas; the new derived comparison assumes no cohomology projectivity and is used to prove it.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-affine-etale-derived-module-realization: The existing statement realizes the derived module category on an affine etale site; it does not compare global sections on two arbitrary flat spaces and their product.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-ringed-site-acyclic-basis-cohomology: The existing result compares derived sections and cohomology on an acyclic basis; it does not assert external tensor comparison or its multiplicativity.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-space-proper-support-derived-projection-formula: The existing result is a proper-support projection formula for one morphism; the new theorem gives a normalized external cup, two-factor scalar comparison and product/base-change coherence.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-flat-space-derived-pushforward-base-change: The existing result is the derived exchange isomorphism; it supplies no external cup isomorphism or its multiplicativity and permutation coherence.

lem-sfb-flat-space-derived-external-cup vs def-sfb-space-affine-global-hom-cohomology: The existing definition normalizes global internal Hom cohomology; it is neither an external tensor isomorphism nor a theorem of invertibility.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-derived-etale-zariski-equivalence: The existing theorem is a derived site equivalence and pullback comparison; it does not state external cup invertibility and its coherent algebra compatibilities.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-proper-flat-space-derived-base-change: The existing theorem gives perfection and base change under proper finite-presentation hypotheses; the new theorem gives external cup for arbitrary flat qcqs spaces and does not assume properness.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-space-qcqs-derived-projection-formula: The existing theorem is the projection formula for one qcqs map, not the normalized external product comparison with pullback, symmetry and scalar-extension coherence.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-scheme-derived-etale-qcoh-comparison: The existing theorem gives scheme site/global-sections comparison; the new statement includes arbitrary algebraic spaces and a two-space multiplicative external isomorphism.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-space-affine-global-trace-adjunction: The existing theorem is a global RHom trace adjunction with a right adjoint; it does not state any external coherent Kunneth isomorphism.

lem-sfb-flat-space-derived-external-cup vs def-sfb-affine-scalar-projection-data: The existing node defines scalar adjunction data and a projection arrow without asserting invertibility; the new node asserts the external cup isomorphism and its compatibilities.

lem-sfb-flat-space-derived-external-cup vs lem-sfb-space-affine-derived-projection-formula: The existing projection formula has affine scalar module coefficients; the new statement compares two derived global-section objects and includes full external product coherence.

lem-sfb-flat-space-derived-external-cup vs def-sfb-space-affine-global-sections: The existing node defines normalized scalar sections and cup, but does not prove the external cup is invertible, multiplicative or compatible with all scalar extensions.

lem-sfb-flat-space-derived-external-cup vs def-sfb-space-affine-sections-compositors: The existing definition provides section compositors and the affine O identification; it does not assert external product invertibility or multiplicativity.

lem-sfb-flat-space-derived-external-cup vs lem-pur-shifted-tensor-morphism-calculus: The existing result is signed calculus for tensor shifts of morphisms, not a global-sections Kunneth theorem.

lem-sfb-flat-space-derived-external-cup vs lem-pur-supported-source-system-cup-calculus: The existing result concerns cup products on supplied supported source systems; it does not compare structure-sheaf derived sections of flat algebraic spaces.

lem-sfb-flat-space-derived-external-cup vs lem-pur-support-site-comparison: The existing result is supported finite-coefficient etale/proetale comparison and explicitly not Kunneth; the new statement has coherent O coefficients and proves external invertibility.

lem-sfb-flat-space-derived-external-cup vs lem-pur-supported-cup-functoriality: The existing theorem concerns supported finite Kummer-coefficient products, not coherent derived external products of spaces.

lem-sfb-flat-space-derived-external-cup vs lem-pod-cup-product-graded-commutativity: The existing theorem is the sign rule for rational l-adic cup products, not a coherent structure-sheaf external tensor isomorphism.

