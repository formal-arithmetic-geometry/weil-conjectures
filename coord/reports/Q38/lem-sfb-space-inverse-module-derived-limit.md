# Q38: lem-sfb-space-inverse-module-derived-limit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-inverse-module-derived-limit.json: split, statement unchanged; seven assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-coherator-adjunction.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-coherator-bound.json: statement, unsplit; no Mathlib match.
- citations.json: a verbatim statement quote for every step/node citation.

Two new nodes, zero Mathlib leaves. The new nodes contain no proofs or proof dependencies.

## Attachments

None. I searched lean/WeilConjectures by the item's blueprint tag and by derived/inverse limit, coherator, quasi-coherent and homotopy-limit terminology. No declaration states this algebraic-space D_QCoh result. Existing scheme and pro-etale limit results do not have its objects or coefficient ringed site. No Lean was written or compiled.

## WANTED

None. The source and its references are available locally.

## Corrections and scope

The imported item is correct: no STATEMENT-DISPUTED correction is needed, and its statement is byte-identical to the live statement. Its empty proof is now replaced by the actual argument of spaces-perfect.tex Example 0CST, the reference used by spaces-flat.tex Lemma 0CX5. Flatness, finite presentation of the modules, infinitesimal compatibility and proper support are not needed for this boundedness lemma; they remain hypotheses, as in 0CX5 and the caller. In particular I did not silently replace a D_QCoh limit by an ordinary sheaf limit.

I read the chapter/unit records, the three-level rules, and the latest blueprint's sk-thm-sf-ctf-stability/_section.md. This is a generic infrastructure lemma under the inherited coherent-family/Quot prerequisite. It changes no chapter or unit statement, no realization record and no route. `blueprint_refs.py ancestor` reports null for this existing ancestry chain; I preserve its inherited null ancestor, fill precise places, and give the new nodes the corresponding extended via chain. Searches of the entire blueprint for coherator, 0CR4, 0CSS, boundedness coherator, inverse quasi coherent and derived limit found no blueprint statement to substitute for either new node. Searches of the live DAG by tags, titles and statement concepts found only the narrower scheme coherator results and the generic shift results distinguished below.

Every search recorded in the new nodes was actually run through batch2/msearch.py; searches.jsonl and the saved *-*.txt outputs contain the results. I read all hits, including ordinary Scheme.Modules limits, module pushforward and sheafification adjunctions, Adjunction.derived, and DerivedCategory t-structure bounds. None constructs the algebraic-space D_QCoh coreflector or its uniform bound. Two semantic phrasings were run for each new node, plus LeanSearch, Loogle and grep. Existing item searches and their results are retained; current searches are appended. No service was unavailable.

## Not duplicates

lem-sfb-space-derived-coherator-adjunction vs lem-pc-dq-coherator-adjunction: the existing result assumes a qcqs scheme and its scheme module site; the new theorem constructs the coreflector on the small etale ringed site of a qcqs algebraic space, which need not be a scheme.
lem-sfb-space-derived-coherator-adjunction vs lem-sfb-scheme-derived-coherator-adjunction: the existing adjoint has domain D(QCoh) on a scheme's Zariski site; the new adjoint coreflects the full D_QCoh subcategory on a space's etale site. These are different functors and neither statement identifies them.
lem-sfb-space-derived-coherator-bound vs lem-sfb-space-affine-chart-uniform-qcoh-vanishing: the existing result bounds higher direct-image evaluation of a quasi-coherent module along a fixed morphism; the new result bounds cohomology sheaves of DQ applied to an arbitrary ambient derived object, given bounds for all affine etale evaluations.
lem-sfb-space-derived-coherator-bound vs lem-sfb-space-derived-coherator-adjunction: existence of a right adjoint supplies no uniform cohomological amplitude; the second node supplies that bound for arbitrary ambient objects and intervals.
lem-sfb-space-derived-coherator-adjunction vs def-coef-reduction-limit-shift-data: the existing definition specifies reduction/limit shift data for an adic coefficient sequence; it does not assert the space D_QCoh coreflector exists.
lem-sfb-space-derived-coherator-adjunction vs lem-trf-finite-structural-maps-commshift: the existing result concerns shift equations for finite-coefficient six-functor structural maps; it does not construct a quasi-coherent coreflector.
lem-sfb-space-derived-coherator-adjunction vs lem-sfb-derived-adjoint-ses-mates: the existing result starts with exact functors and adjoints and compares short-exact-sequence boundary mates; it does not establish coreflector existence for spaces.
lem-sfb-space-derived-coherator-adjunction vs lem-sfb-ringed-projection-first-shift: the existing result is shift compatibility of an already defined projection transformation; it does not construct DQ.
lem-sfb-space-derived-coherator-adjunction vs lem-weil-pbc-adjunction-square-shift-mate: the existing result assumes adjunctions and proves shift compatibility of their mates; it supplies no space coreflector.
lem-sfb-space-derived-coherator-adjunction vs lem-weil-pbc-derived-exchange-triangulated: the existing result concerns a specified bounded-below scheme exchange transformation; the new node asserts existence of an unbounded space coreflector.
lem-sfb-space-derived-coherator-adjunction vs lem-weil-pbc-formal-exact-projection-mate: the existing result starts with supplied exact tensor and adjunction data and constructs a projection transformation; the new node establishes the geometric DQ adjunction.
lem-sfb-space-derived-coherator-adjunction vs lem-weil-pbc-adjunction-shift-compatibility-unique: the existing result equips an already existing adjunction with compatible shifts; it does not establish DQ exists.
lem-sfb-space-derived-coherator-adjunction vs lem-weil-pbc-derived-adjunction-commshift: the existing result is a scheme inverse-image/direct-image shift equation; it does not concern the D_QCoh inclusion.
lem-sfb-space-derived-coherator-adjunction vs lem-weil-pbc-derived-adjunction-shift: the existing result concerns K-flat/K-injective pullback/direct-image adjunctions of ringed topoi; the space inclusion/coreflector adjunction is not such a supplied geometric morphism adjunction.
lem-sfb-space-derived-coherator-adjunction vs lem-sf-triangulated-right-adjoint: the existing theorem assumes an adjunction and compatible shifts, then proves exactness. It cannot construct the geometric right adjoint required here. The shared 0A8D citation gives the new coreflector's triangulated structure, not its existence.
lem-sfb-space-derived-coherator-adjunction vs lem-sp-canonical-right-derived-adjunction-shift: the existing result assumes an exact adjunction of abelian categories and derives it; the new theorem constructs a right adjoint to the full quasi-coherent-cohomology derived inclusion.
lem-sfb-space-derived-coherator-adjunction vs lem-sp-finite-free-scalar-shift: the existing result is a finite-free coefficient scalar shift equation, without any D_QCoh coreflector existence assertion.

Neither new node restates a clause of the item. The adjunction concerns arbitrary ambient complexes and the bound concerns every interval [a,b], with no tower. The proof of the item's [0,1] affine bound and its projection identity stays in the item. Conversely, I did not create elementary nodes for projection compatibility, product transport across an adjunction, or the vanishing of the outside terms of the Milnor sequence.

## Review by Q38

I read spaces-flat.tex Situation existence and Lemma compute-what-it-should-be (0CX5), and spaces-perfect.tex Example inverse-limit-quasi-coherent (0CST). For the first new node I read Lemma better-coherator (0CR4), both proofs, and derived.tex Lemma adjoint-is-exact (0A8D). For the second I read Lemma boundedness-better-coherator (0CSS), including the affine case and distinguished-square induction: the bound applies to affine hypercohomology of an arbitrary E, not only to quasi-coherent or bounded E. Its lower endpoint is a, not a-N. Taking N nonnegative only enlarges the upper interval. I checked injectives.tex Lemma derived-products (07D9), derived.tex product-K-injective (0BK6), and sites-cohomology.tex RGamma-commutes-with-Rlim (0D6K) against the assembly.

Step 1 reads the statements of lem-trf-space-qc-separated-quasi-coherent-pushforward and lem-trf-space-chart-limit-enlarged-sections. The former really asserts module quasi-coherence on spaces, not only a scheme theorem. The latter identifies the actual chart-limit direct image with the ringed-topos direct image used by the former. Surjectivity A to A_n follows by recursive compatible lifts. On affine scheme tests the immersion is a quotient spectrum, hence qc and separated. X is qcqs since its structure map is finitely presented over an affine base. No finite-type condition on kernels or Noetherian base is used.

Step 2 reads def-sfb-space-small-ringed-model, prop-pur-kinjective-resolutions-exist, lem-weil-pbc-module-sheaves-limits-sectionwise, lem-pc-ringed-space-product-kinjective and lem-weil-derived-limit-existence. The product-K-injective node, despite its title, explicitly quantifies over any abelian category, so it applies to the small-site module category. The sectionwise-limit node is also for any site. These provide ambient products through resolved complexes. I specifically did not apply the exact-products clause of derived-limit-existence to etale module sheaves.

Step 3 uses the new adjunction and the first clause of derived-limit-existence. I checked the Hom product identity including the projections, the inverse unit DQ(IM_n) to M_n, and naturality at each transition. This supplies the D_QCoh product and identifies the shift map, so exactness of DQ sends the ambient Roos triangle to the required one. Uniqueness up to isomorphism suffices for the cohomology conclusion, without claiming a canonical limit or identifying arbitrary maps from their projections.

Step 4 reads lem-sfb-space-module-pullback-quasicoherent, lem-trf-space-enlarged-etale-ringed-site-model, lem-pe-ringed-site-derived-evaluation-slice, lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, lem-sc-etale-affine-qcoherent and lem-kun-site-rgamma-derived-limit. The enlarged-site lemma identifies the etale chart site with the slice, including the structure sheaf. The scheme equivalence really identifies the restricted module with an associated etale quasi-coherent module, as required by affine acyclicity. During self-review I corrected a missing module/abelian comparison: affine acyclicity is stated for associated abelian sheaves, whereas our evaluation is derived in module sheaves. The now-cited derived-evaluation/slice theorem states precisely their cohomological agreement on the slice; its enough-injectives hypothesis was established in step 2. This avoids claiming that forgetting preserves injectives. The derived-limit comparison node applies to arbitrary ringed sites and to the actual product triangle, preserving its projections.

Step 5 reads lem-pc-derived-limit-milnor-sequence, whose objects are complexes of abelian groups, precisely the outputs of derived evaluation. Both H^(i-1) and H^i vanish when i is outside [0,1]; hence both outer terms vanish. No surjectivity on sections or Mittag-Leffler condition is assumed. Step 6 applies the new uniform bound with a=0,b=1, giving [0,N+1] for cohomology sheaves. Step 7 reads lem-weil-pbc-hom-into-triangle-exact: its clause (i) is exactly the zero-composite assertion used. Taking the (n-1)st component gives q_(n-1)=t_n q_n, with the item's indexing and signs.

I tested the new statements on an empty space, on an affine scheme (DQ is affine derived sections followed by associated sheaves, with bound N=0), and with E=0. The item includes the zero module tower, constant towers, and the one-point affine test, where inverse limits of groups have cohomology only in [0,1]; surjective module towers can have degree-one vanishing without any need to assert this on general etale sheaves. I also checked the base qcqs condition intrinsically, using qc pairwise fibre products of affine etale charts, rather than incorrectly testing only the diagonal relative to a possibly non-quasi-separated S. Both new nodes are strictly general infrastructure, not the source's tower claim relabelled. All proof steps are below 2000 characters, with no hidden sub-lemma in a long step.

I checked delivery-errors B--E: statements introduce objects and notions; new nodes are statement-only with correct Stacks tags, actual searches and blueprint metadata; each cited statement contains the fact used (quotes supplied); no unquoted source lemma or scheme-only theorem is applied to a nonscheme; elementary assembly arguments stay in the proof; coefficients, site, degree bounds, transition indexing and product category are fixed throughout. Off-unit citations are explicitly declared as generic tools in split_report.tool_uses, for the maintainer to accept. I left no unresolved mathematical issue.

## Unfinished work

The two new statement-only lemmas remain for subsequent stage-1 workers, as required. No other work is claimed complete by this split. Required delivery validation follows below.
