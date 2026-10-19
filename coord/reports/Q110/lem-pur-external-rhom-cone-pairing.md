## Files written

- dag/nodes/sec-smooth-purity/lem-pur-external-rhom-cone-pairing.json: corrected the disputed normalization; ten proof steps; current repository metadata and prior item searches retained.
- dag/nodes/sec-smooth-purity/lem-pur-kflat-map-factorization.json: one new statement-only node, Stacks Tag 0G7D; not found in Mathlib. Zero new Mathlib leaves.
- citations.json: verbatim quotations for every step dependency.
- report.md: this repair report.

The never-merged duplicate lem-pur-constant-global-sections-adjunction is withdrawn. Its JSON and the previous report and citations are preserved under repair/ in the sandbox. All prior logged searches remain in searches.jsonl. The adjunction is now cited from def-constructible-constant. No live project, launcher or Lean file was edited.

## Attachments

None. I searched the read-only slopmaster2 project for the item tag, external RHom and cone-pairing concepts, and searched the DAG and project for the factorization lemma. The externalHom field at WeilConjectures/SixFunctors/Etale/Derived/Kunneth/Comparisons.lean:130 is an interface under constructibility and finite-type hypotheses, not this global-Hom cone transformation. Upstream master was searched as reference material, not evidence of finished proofs.

## WANTED

None. The actual new source, sites-cohomology.tex, label lemma-factor-through-K-flat, Tag 0G7D, is present. The extra external pairing argument is agent-written, expanding the blueprint support comparison and Stacks constructions.

## Source error

STATEMENT-DISPUTED: the retained normalization through Hom(G,a^-1 I_K tensor b^-1 I_L) was false. Take A=Z, X=Y=P=Spec C, a=b=id, K=L=Q/Z, E=H=Z. The injective complexes I_K=I_L=Q/Z have ordinary tensor zero. However F=(Q/Z) tensor^L (Q/Z)=(Q/Z)[1], and lambda is the identity of F. The flat resolution [Z -> Q], in degrees -1,0, computes its nonzero Tor group. No claimed comparison out of the zero intermediate Hom complex can give that map.

The correction retains every geometric, coefficient and boundedness hypothesis, and every naturality, cone-component and boundary assertion. It replaces the false raw normalization by an honest resolved formula. Resolve the two global Hom complexes by flat-term K-flat A-complexes U,V. Their evaluations into I_K,I_L have K-flat flat-term sources. Tag 0G7D factors each, up to homotopy, through K-flat flat-term N_K,N_L. Now a^-1 N_K tensor b^-1 N_L represents F; a K-injective resolution J of that tensor gives the actual target Hom(G,J). The Koszul formula uses these lifted evaluations u,v. This is an existence construction for all original inputs, not an extra hypothesis on them. The notation H_T(G,M) now explicitly allows arbitrary G and any K-injective model I.

The sole current citer is lem-pur-supported-product-localization. Its step 6 needs the specified evaluation transformation and both boundary squares, which remain true. Its raw degreewise f(e) tensor g(d) sentence must use the corrected lifted-evaluation representatives; interpreting f,g as arbitrary maps into non-flat I_K,I_L is invalid. I did not edit that parent. Paragraphs 1 and 3 of the ancestor lem-pur-kunneth-supported proof require the evaluation-defined support comparison, not an ordinary tensor of injectives. This repair restores that route without changing a unit-level purity argument.

## Repair of the return

1. E2/E3 and G1: removed the missing intermediate comparison. Steps 3-4 construct the lifted evaluations and an actual model of F. The new node is the full source statement 0G7D, including its flat-terms clause.
2. E5: removed the old transport sentence and sign computations. Steps 7-9 keep the same K-flat N_K,N_L and the same J under coefficient shifts, by explicitly defining the shifted lifts. Step 10 uses naturality at the boundary arrow and the proved shift identities; it does not complete two squares by a noncanonical cone map.
3. C5: read def-constructible-constant, whose statement includes modules and their constant/sections adjunction, and withdrew the duplicate leaf. I also read Mathlib GlobalSections.lean:55-110, confirming the generic adjunction identification.
4. C8/route: split_report.tool_uses now declares all three returned tools (lem-sfb-ringed-derived-monoidal-comparisons, lem-sfb-geometric-inverse-image-constant-module, lem-sf-ringed-derived-closed-symmetric-monoidal), together with the other generic off-unit infrastructure used. No maintainer-owned tool_uses or unit/chapter field was changed. No SGA source is used.
5. Minor C1: Step 1 explicitly cites lem-weil-pbc-ringed-topoi-derived-tensor-pullback for preservation of K-flat flat-term complexes; Step 4 uses it for N_K,N_L. Exact module inverse image has its own citation.

## Not duplicates

lem-pur-constant-global-sections-adjunction vs def-constructible-constant: the former duplicates the needed module-valued adjunction and is withdrawn. The derived adjunction and normalized constant tensor comparison are already in def-kun-constant-projection-morphism.

Before creating lem-pur-kflat-map-factorization I searched the entire DAG for 0G7D, its label, K-flat factorization and the homotopy condition, and searched the Lean project. Blueprint searches for 'factor through K-flat' and '0G7D' each returned zero nodes. The ancestor command gives lem-pur-kunneth-supported; the new blueprint ancestry and exact proof paragraph are filled. Nodes mentioning the same tag in proofs/sources are distinguished below.

- lem-pur-kflat-map-factorization vs lem-pd-module-ringed-topos-derived-comparison: the existing statement compares internal module-object and sheaf-module derived operations for condensed coefficients, not factorizations of arbitrary chain maps.
- lem-pur-kflat-map-factorization vs lem-weil-pbc-scalar-extension-unit-triangles: the existing statement constructs the scalar-extension unit and its triangle/shift compatibilities.
- lem-pur-kflat-map-factorization vs lem-sfb-successive-derived-quotient-normalization: the existing statement normalizes successive scalar extensions and their units.
- lem-pur-kflat-map-factorization vs lem-sfb-open-closed-internal-hom-formulas: the existing statement gives open/closed internal-Hom adjunction identities.
- lem-pur-kflat-map-factorization vs lem-asd-etale-sum-extension-tensor: the existing statement gives etale sum-extension tensor and counit comparisons.
- lem-pur-kflat-map-factorization vs det-formal-closed-support-ii-limits: the existing statement gives exactness and limit preservation of support and restriction functors.
- lem-pur-kflat-map-factorization vs lem-trf-external-comparison-triangles: the existing statement treats a particular Kunneth exchange/projection transformation on triangles, not the existence of lifted evaluation maps.
- lem-pur-kflat-map-factorization vs det-sp-scalar-extension-functor: the existing statement gives scalar extension, finite Tor, twist and composition properties.
- lem-pur-kflat-map-factorization vs lem-kun-kunneth-map-agrees: the existing statement identifies a specific inverse Kunneth composite with the evaluation-defined map.
- lem-pur-kflat-map-factorization vs lem-kun-derived-pullback-composition-monoidal: the existing statement gives coherence equations for pullback tensor constraints.
- lem-pur-kflat-map-factorization vs lem-weil-integral-twist-derived-scalar: the existing statement compares completed scalar extension with Tate twists.
- lem-pur-kflat-map-factorization vs det-sp-reduction-tower-normalized: the existing statement normalizes integral reduction towers and their constructibility/Tor bounds.
- lem-pur-kflat-map-factorization vs lem-weil-point-completed-scalar-shift: the existing statement checks a specified completion comparison on a Roos-cone model.
- lem-pur-kflat-map-factorization vs lem-sf-cbc-completed-pullback-unit-tower: the existing statement compares completed pullback reduction towers and their units.
- lem-pur-kflat-map-factorization vs lem-pur-finite-clopen-derived-decomposition: the existing statement decomposes module/derived categories along a finite clopen partition.
- lem-pur-kflat-map-factorization vs lem-sf-ringed-derived-closed-symmetric-monoidal: the existing statement supplies the closed symmetric monoidal structure and evaluation adjunction, not fixed-source chain-map factorization or its flat-terms clause.
- lem-pur-kflat-map-factorization vs lem-weil-pbc-site-derived-tensor-descent: the existing statement identifies a localization of K-flat complexes with the derived category and its tensor; it does not assert the actual fixed-source chain-map homotopy factorization with flat terms.

## Review by Q110

I read the retained split against the current repository item, which remains unsplit. The geometric, coefficient and boundedness hypotheses, ancestry, chapter and unit agree. I retained the current metadata and all earlier item search entries. As required, I first ran the dry run on the retained split: it returned OK at 075f545ae5. That mechanical result did not establish the false normalization; the present changes are substantive mathematical repairs.

I read the chapter and sk-prop-a1-kummer unit records, and current blueprint lem-pur-kunneth-supported.proof.md paragraphs 1 and 3. In Stacks sites-cohomology.tex I read section-hom-complexes (0A8X), lemma-compose (0A90), section-internal-hom (08J7), lemma-internal-hom (08J9), lemma-section-RHom-over-U (08JA), lemma-restriction-RHom-to-U (08JB), lemma-RHom-triangulated (08JC), and the complete lemma-factor-through-K-flat (0G7D), including its proof and final assertion. I checked tag/label pairs against tags/tags, correcting inherited mismatches. The only new node states precisely 0G7D, is self-contained on a small ringed site, and has a statement only: no proof, sketch, or proof dependencies.

Step 1 cites the site version of bounded-above flat implies K-flat, not the ringed-space version. The sections model computes the two global Hom objects while retaining their termwise A-linear structure; projectivity of E,H is not needed. The K-flat resolution theorem applies to A-modules by the one-object site. I checked the underived module adjunction in def-constructible-constant, exactness and the derived adjunction in def-kun-constant-projection-morphism, exact module inverse image in prop-weil-pbc-inverse-image-modules-exact, and K-flat flat-term pullback in lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

Step 2 uses the actual closed adjunction and its natural evaluation counit in lem-sf-ringed-derived-closed-symmetric-monoidal. Its composite with the derived constant/sections adjunction gives the global-Hom transposition bijection written in the step. The constant-module inverse-image statement applies degreewise, and the monoidal-comparisons statement supplies the coherent interchange. None assumes a finite coefficient ring, finite-type scheme, or constructibility. These are infrastructure tools and do not replace the unit's route.

In Step 3 I checked the unsigned evaluation differential: the two f d_E terms cancel. The tensor-Hom isomorphism and the adjunction identify this chain evaluation with the derived counit after resolving the global Hom source by U. The domain is K-flat by two applications of the definition and associativity. Its terms are finite sums of tensors of flat modules because E is bounded; tensoring with such a term is a finite sum of compositions of exact functors. This verifies the flat-terms hypothesis of 0G7D. That lemma supplies N_K,u,c_K with t_X homotopic to c_K u; it does not lift through an arbitrary preselected resolution. The same check applies to H.

Step 4 uses the K-flat pullback theorem and tensor-descent statement to make the ordinary tensor T an actual representative of F. The Kinjective existence node supplies J. The ordinary tensor-Hom isomorphism gives the displayed chain pairing, and the sections-model statement identifies Hom(G,J) with the target. The derived tensor of the two homotopy identities identifies this pairing with Step 2's transpose. No step tensors I_K and I_L as models of F. Naturality and independence follow by injectivity of the adjunction bijection, rather than an unsupported resolution transport.

Step 5 uses evaluation naturality, the stated monoidal comparisons and the internal-Hom restriction theorem. The global-Hom restriction arrow is restriction of actual morphisms, not asserted to be an isomorphism. No functorial choice of lifted u,v is needed. Step 6 cites Hom exactness, right-derived global-sections exactness, exact inverse-image triangulatedness, and tensor exactness separately; exactness of the two functors alone is not used to infer exactness of their natural transformation.

Step 7 calculates the actual Hom shift theta and the evaluation-domain cancellation eta from their differentials. The shifted source is U[-1], and the chosen shifted lift is u eta into the same N_K. Similarly V[-1] and v eta use the same N_L. Thus Steps 8 and 9 compute inside the same valid T and J. For the E shift, the first composite has exponent sq+r+(r+s)=sq+s; the second has s(q+1)=sq+s. For H, they are sq+s+q+(r+s)=sq+q+r and r+(s-1)q=sq+q+r modulo 2. These are equalities on every total tensor summand and local pure tensor, hence actual chain-map equalities by the sheafified tensor construction. The right-tensor shift is the identity and the left-tensor shift is (-1)^r. Step 10 explicitly combines this shift square with naturality at d:E_0 -> E_2[1], producing the connecting square with the same contravariant rotation convention on both sides. This proves the specified cone term, not an unspecified completion.

Small cases: in the reviewer's Q/Z example take U=V=[Z -> Q], N_K=U,N_L=V and u=v=identity for E=H=Z. Step 4 is the resolution of the identity of U tensor V and retains H^{-1}=Q/Z. Zero objects, empty sites, zero/split triangles, shifted one-term complexes and negative cochain degrees satisfy the formulas without extra assumptions. For 0G7D, t=0 works with u=0 and a K-flat resolution of I; if I is already K-flat take N=I,c=id,u=t. The lemma does not falsely assert strict equality or lifting through every chosen resolution.

Before creating the new node I ran and read five msearch queries: LeanFinder with two formulations, Loogle, grep and LeanSearch. The returned candidates concern projective/injective resolution homotopies, derived fractions and equality after localization of homotopic maps. None states this K-flat-target factorization with a fixed source and flat-terms clause. The services were available for these queries; every record is copied from an executed query and its result. Earlier searches remain recorded and were reused for the unchanged external derived pairing question. Every dependency in each step has a verbatim statement quotation in citations.json; proof_deps is their exact union. No step exceeds 2000 characters. The new node is generic resolution infrastructure, strictly smaller than the external pairing, and not a clause of the item.

## Unfinished work

No unresolved part of the stage-1 split. The new 0G7D node intentionally remains statement-only for later splitting, as required. No Lean or compiler work was performed.
