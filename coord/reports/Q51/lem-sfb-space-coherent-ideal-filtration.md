# Q51: lem-sfb-space-coherent-ideal-filtration

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-ideal-filtration.json: item split into seven proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-support-union-sequence.json: statement-only, unsplit; Mathlib searches find no algebraic-space support-separation theorem.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-support-ideal-power.json: statement-only, unsplit; no Mathlib match for the algebraic-space support/ideal-power equivalence with coherent products.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-reduced-support-generic-ideal-inclusion.json: statement-only, unsplit; no Mathlib match for the ideal-sum inclusion on an algebraic space.
- citations.json: one verbatim statement quotation for each node used in each numbered proof step.

## Attachments

None. The project-source searches for the exact blueprint tag and coherent/ideal filtrations found scheme declarations, not this theorem for arbitrary Noetherian algebraic spaces. In particular the CoherentIntegralFiltration and CoherentGenericPointIdealInclusion files concern schemes. No Mathlib declaration is claimed as an attachment.

## WANTED

None. All mathematical sources needed for this split are present in literature/stacks-project/.

## Corrections and route

The item statement is retained, including nonzero factors, full support of each ideal, support containment, and the empty-support assertion. The original unsplit item named Tag 07UR without a proof; the split now carries its actual closed-support induction. The three new statements are independent inputs of that proof, not clauses asserting that a filtration already exists. Concatenation, coordinate-sum filtration and ideal-power refinement remain explicit proof steps rather than new nodes.

I read the current blueprint through literature/blueprint/latest/, especially the six-functor stability unit and direct-images proof (3). This is a lower-level prerequisite on the inherited alteration/devissage chain, not a replacement of that unit's direct-image route. The blueprint ancestor command returns None for the inherited chain. I retain the inherited null from.node and explicit from.place/via, extending them for the new nodes; I do not invent a blueprint id. Searches by coherent, support, and Tags 07UP/07UQ/07UK/07UR find no blueprint statement that replaces a proposed node. The chapter and unit records were read and are unchanged; this item is not their key statement.

## Unfinished work

No part of this one-level split remains unfinished. The three new lemmas are intentionally statement-only queue items. No Lean files were written and no compiler, Lake or build command was run.

## Review by Q51

I read spaces-cohomology.tex, lemma-coherent-filter (07UR), including every induction paragraph, against the seven steps. I also read lemma-prepare-filter-support (07UP), lemma-power-ideal-kills-sheaf (07UK), and lemma-prepare-filter-irreducible (07UQ), statements and proofs, for the three new nodes. The ideal-power node adds coherence of products and quotients from lemma-coherent-Noetherian-quasi-coherent-sub-quotient (07UD), checked on affine etale charts. For the generic inclusion's annihilation formulation I read lemma-i-star-equivalence (08AM): a module annihilated by the defining ideal descends coherently to Z. Full support and reduced irreducibility then give precisely the setting of 07UQ. Its proof chooses a power of an ideal equal to the unit ideal on a dense open. Thus this ideal is nonzero, coherent by 07UD, and has full support: its support is closed by spaces-morphisms.tex lemma-support-finite-type (07TZ) and contains that dense open. Coherence of the direct image and cokernel is consistent with 07UH and 07UC. The new statement contains no proof sketch; those source checks are recorded here.

For Step 1 I opened lem-sfb-space-coherent-abelian: it states coherence of ambient kernels and cokernels, so the inverse images used in concatenation are coherent. The quotient identification is written out using local lifts and its kernel; it uses no extra filtration theorem.

For Step 2 I opened every cited statement. lem-weil-pbc-site-restriction-exact gives exactness on chart slices for abelian sheaves; def-weil-sheaf-of-modules-category gives the underlying sectionwise kernels and sheafified cokernels, making the same assertion for module sheaves. lem-weil-pbc-coherent-kernel-cokernel-locnoeth gives coherent ambient Zariski kernels and cokernels, and lem-sfb-scheme-etale-module-exact-finiteness-comparison says explicitly that association to the etale site is exact in ambient modules. Together with lem-trf-scheme-zariski-etale-quasi-coherent-equivalence this justifies the comparison used, rather than assuming an equivalence of quasi-coherent categories alone preserves ambient cokernels. lem-weil-pbc-module-stalk-exact then gives support containment for coherent subquotients. lem-sfb-space-etale-chart-support equates chart supports with inverse images of geometric support; lem-weil-pbc-module-iso-on-stalks detects zero on each chart. Covering descent of a zero sheaf is the sheaf axiom. Finally lem-sfb-space-noetherian-coherent-support states closed support of N when N is a quasi-coherent submodule of F, so N=F gives the closedness asserted here. These tools have the necessary locally Noetherian chart hypotheses because X is Noetherian by assumption.

For Step 3 I opened lem-sfb-noetherian-space-topology: it supplies a minimal member of any nonempty collection of closed subsets, exactly the well-founded induction required. The new support-union statement supplies the coherent short exact sequence with the correct order of supports. The induction quantifies over every coherent module with that support, so it applies to both new modules, and to every proper-support factor later, without circularity. Empty support is handled before the reducible/nonempty distinction.

For Step 4 I opened lem-sfb-space-reduced-closed-support and lem-sfb-space-closed-immersion-quasi-coherent-modules. They supply respectively the reduced closed structure and its quasi-coherent defining ideal. The new ideal-power node supplies a finite annihilating exponent and coherent terms. lem-sfb-space-coherent-abelian then supplies coherent successive quotients. The equality J(J^k M)=J^{k+1}M directly proves annihilation of each quotient; no false assertion that a set-theoretic support containment itself implies J M=0 is used. The n=0 case means M=0 and was checked separately.

For Step 5 I read the new generic-inclusion statement against all its uses: X is Noetherian, Z is reduced, nonempty and irreducible, J P=0 was proved in Step 4, and the branch under consideration has full support T. It gives an actual monomorphism from a positive finite ideal sum and a coherent cokernel of strictly smaller support. The induction applies to that cokernel; it is never applied to P with the same support.

For Step 6 I reopened lem-sfb-space-closed-immersion-quasi-coherent-modules, lem-sfb-space-coherent-abelian and lem-sfb-space-closed-coherent-modules. They state exactness of closed direct image, coherence of finite sums, Noetherianity of the closed subspace, preservation of coherence, and equality of direct-image support. Thus all the coordinate-sum terms are coherent and their factors are i_*K with support T. The finite coordinate sequences are split by the displayed inclusions/projections; no non-elementary additivity assertion is left implicit.

Step 7 invokes only the earlier steps: concatenate the finitely many refinements of the descending ideal-power filtration and remove zero quotients. The factors remain the supplied ideal direct images, with support inside the original module by Step 2. None of the proof steps exceeds 2000 characters or contains a separately quantified hidden comparison lemma.

I tested the new statements on the zero module, empty space, empty support pieces, a field, a disjoint union of closed components, and a nilpotent thickening such as k[e]/(e^2). In the power statement the exponent can be 0 precisely when F=0; for Z=X its zero defining ideal permits exponent 1, and for Z empty its unit ideal forces F=0. The generic statement excludes empty support and permits K=O_Z and rank equal to the vector-space dimension over a field. Over a nilpotent thickening it requires the explicit J-annihilation hypothesis, so it does not assert that arbitrary modules descend to the reduced space. The union statement permits one or both pieces to be empty. These cases agree with the claimed assertions.

I read the saved searches.jsonl results rather than rerunning their queries. The three new nodes each record the queries actually run through msearch.py, including a second semantic phrasing, Loogle and grep. Nearby hits such as Scheme.IdealSheafData.support_sup concern zero loci on schemes, and Module.support_quotient and Module.mem_support_iff_exists_annihilator concern modules over a ring. I read these source statements: none gives the proposed algebraic-space result in one specialization. No failed service is recorded as a negative mathematical result. Existing item searches were retained unchanged from its live node.

I checked delivery-errors B through E against the files: self-contained statements and definition dependencies, single-escaped TeX, exact tag/label references, no new proof sketches or fabricated searches, no duplicate statement or item-clause node, exact citation statements, proper induction hypotheses, no added hypotheses in applications, and the correct module/support objects. Each citations.json entry copies a verbatim part of the cited node's statement. The first dry run detected a concurrent update adding a direct-image definition reference to the closed-immersion statement; I reopened it and replaced its two whole-statement quotes by the unchanged precise theorem sentences used in Steps 4 and 6. The underlying cited mathematical claims are unchanged. The server review_split check passed; the final delivery dry run remains the next gate.

## Not duplicates

lem-sfb-space-coherent-support-union-sequence vs lem-weil-pbc-coherent-support-union-exact-sequence: the existing theorem is for schemes with Zariski module stalks; the new theorem is for arbitrary Noetherian algebraic spaces on their small etale site.
lem-sfb-space-coherent-support-ideal-power vs lem-weil-pbc-coherent-support-power-ideal-kills: the existing statement is for schemes; the new statement treats algebraic spaces and explicitly includes coherence of all ideal-power submodules and quotients.
lem-sfb-space-coherent-support-ideal-power vs lem-weil-pbc-ideal-power-product-restriction-zero: the existing theorem only commutes scheme ideal products with restriction to an open, and does not assert an annihilating exponent.
lem-sfb-space-reduced-support-generic-ideal-inclusion vs lem-weil-pbc-coherent-generic-point-ideal-inclusion: the existing theorem assumes schemes and an ordinary generic point; the new theorem supplies the algebraic-space ideal-sum inclusion under annihilation and full reduced irreducible support.
lem-sfb-space-reduced-support-generic-ideal-inclusion vs lem-sfb-space-generic-multiple-embedding: the existing theorem embeds an ideal multiple of a given full-support module into a positive direct power of another module; it does not give an ideal sum embedded into the single given module F.
lem-sfb-space-coherent-support-ideal-power vs lem-sfb-space-generic-multiple-embedding: the existing generic comparison does not assert the equivalence between support containment and annihilation by a defining-ideal power.
lem-sfb-space-reduced-support-generic-ideal-inclusion vs lem-sfb-space-closed-coherent-modules: closed direct image preserves coherence and support, but that statement constructs no ideal inclusion.
lem-sfb-space-reduced-support-generic-ideal-inclusion vs lem-sfb-space-coherent-abelian: closure of coherent modules under kernels/cokernels/extensions constructs no ideal-sum inclusion with smaller-support cokernel.
lem-sfb-space-reduced-support-generic-ideal-inclusion vs lem-sfb-space-coherent-ideal-filtration: the item asserts an entire finite filtration of any coherent module; the new node asserts a single generic inclusion for an annihilated full-support module and does not give a filtration.
lem-sfb-space-reduced-support-generic-ideal-inclusion vs lem-sfb-space-noetherian-coherent-support: the existing statement asserts coherence and closed support of quasi-coherent subquotients, and does not construct a generic ideal-sum inclusion.
lem-sfb-space-reduced-support-generic-ideal-inclusion vs lem-sfb-space-coherent-kernel-cokernel-extension: the existing closure properties of coherent modules do not construct an ideal-sum inclusion.
lem-sfb-space-coherent-support-ideal-power vs lem-sfb-space-noetherian-coherent-support: coherence and closedness of subquotients do not produce a uniform ideal power annihilating a module with specified support.
