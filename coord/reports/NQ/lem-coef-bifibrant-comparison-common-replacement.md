## Files written

- `dag/nodes/sec-six-functors/lem-coef-bifibrant-comparison-common-replacement.json`: statement node, now split in six steps; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- `searches.jsonl`: actual NQ search records. The item's preexisting Q49 searches are retained unchanged.

No new nodes and no Mathlib leaves. The item statement, source, creation metadata and blueprint ancestry are retained. No Lean, compiler, Lake or build command was used.

## Attachments

None. Searches for the exact blueprint id and for `bifibrant`, `Bifibrant`, and `commonReplacement` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` returned no project declaration. The item has no attached Lean declaration to inspect.

## Sources wanted

WANTED: Jacob Lurie, Higher Algebra, Definition 1.3.4.1, Remark 1.3.4.16, Construction 1.3.4.18 and Theorem 1.3.4.20, for lem-coef-bifibrant-comparison-common-replacement; archival copy. Read online at https://www.math.harvard.edu/~lurie/papers/HA.pdf (printed pp.108,116–117).

WANTED: Jacob Lurie, Higher Topos Theory, Remark 4.2.4.5 and Proposition A.3.3.2, for the originating diagram-model comparison; archival copy. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf.

WANTED: Kerodon, Theorem 4.4.4.4, Tag 01DK, for the pointwise-equivalence input to lem-coef-bifibrant-comparison-common-replacement; archival copy. Read online at https://kerodon.net/tag/01DK. This is a Kerodon tag, not a Stacks tag. No Stacks tag states this homotopical result. No SGA source is used.

## Audit of the imported item and route

The statement is valid as written. Its ordinary functor R need not have an enriched lift, so applying a coherent-nerve functor directly to R would be unjustified. The split instead constructs r after localization, and keeps the two uses of c distinct: localization of its ordinary nerve in D identifies r with Phi; postcomposition of its ordinary nerve in E with e compares evaluation functors. E is not assumed locally Kan, and the proof never treats its coherent nerve as a quasicategory.

HTT Remark 4.2.4.5 says that the diagram comparison is independent of choosing the projective or injective model structure; Proposition A.3.3.2 supplies these model structures. Neither is literally the general supporting lemma here. The more general common-localization proof is therefore correctly recorded with proof_origin.by = agent, using the existing Dwyer–Kan and pointwise-equivalence nodes.

I read the chapter record and sk-prop-sf-biduality-general unit record. This is not its key node and no unit realization field changes. I also read the current main-20261015 integral-exceptional-adjoint statement and proof: the second paragraph's derived coefficient adjunction is the inherited ancestor place. This split stays below that supporting diagram/model-category foundation. No geometry or coefficient route is replaced. The item's blueprint.from place is already explicit, and is retained. Whole-blueprint searches for `bifibrant` and `natural equivalence` return no imported blueprint node with this statement; the broader localization search was read and does not identify another statement of this comparison.

Mathlib: the five new NQ queries in searches.jsonl were run with msearch.py and their full terminal hits were read. Two LeanFinder phrasings returned truncated-nerve and ordinary-localizer declarations. LeanSearch returned ordinary cofibrant replacements, ordinary IsLocalization.of_equivalence_target, isoUniqFunctor and functorEquivalence. Loogle returned functorEquivalence. Grep supplied the localization source files. I read Predicate.lean at functorEquivalence (236), of_equivalence_target (405) and isoUniqFunctor (466), and Equivalence.lean (45–63). These quantify over ordinary categories and natural isomorphisms, not coherent nerves or entire infinity functor categories. SimplicialNerve.lean (14–34) defines the nerve and lists the quasicategory theorem as future work. None supplies this item as a one-line specialization; no Mathlib leaf is claimed. No new node was needed, so no duplicate/tag-pair comparison is required.

## Review by NQ

I reviewed the item against the sources above and opened the full statements of every cited node. HA Remark 1.3.4.16 needs functorial model factorizations; the model-category convention explicitly supplied by lem-coef-simplicial-model-nerve-localization includes them. HA Theorem 1.3.4.20 does not require combinatoriality, and none is added here. Both model structures have exactly the same W, as needed for the single target localization. The input supplies R and c, so there is no unjustified construction of a replacement functor with extra properties.

Step 1 uses the actual statement of lem-coef-simplicial-model-nerve-localization: its equivalence with the bifibrant nerve, agreement with inclusion, entire-functor-category universal property, and equivalence of the ordinary bifibrant subcategory localization with D's localization. These are all explicit clauses, rather than arguments taken from that node's proof. Together they make the canonical a_P and a_Q localization maps; I wrote the quasi-inverse precomposition calculation instead of assuming equality of presentations. The canonical ordinary-to-coherent nerve map is explicitly constructed by constant composite arrows on the mapping-poset nerves. def-cbc-enhanced-diagrams-cones supplies nerves, functor categories and the quasi-inverse convention.

Step 2 uses only the stated model axiom two-out-of-three, naturality of c, and definitions. The displayed equation has the correct source RG and target H, and gives preservation of W by R without assuming R preserves fibrations or cofibrations. The ordinary product functor representing c and its mixed arrows are written out. Ordinary naturality suffices for its nerve; no unprovided enriched naturality is used. This is elementary from the cited definitions/axioms.

Step 3 uses the entire-functor-category essential-image clause of the same localization node with target A. The W-inversion needed for descent was proved in Step 2. The cited definition def-coef-coherent-localization-interface explicitly retains higher simplices and transformations; it is cited for that meaning only, not as an existence theorem. Existence is the theorem applied in Step 1. Thus r and eta are legitimate localized data, not an enriched lift chosen from an unsupported existence claim.

Step 4 applies lem-coef-infinity-pointwise-equivalences precisely to the nerve of c followed by q in the quasicategory L: every component is q(c_G), hence an equivalence. Its statement allows any small simplicial index, including N(Q_0). Agreement of psi_p and psi_q on the ordinary nerves is a hypothesis of this item, so it identifies the endpoints before descent. The localization node's full functor-category clause then reflects equivalence of these functors; applying a quasi-inverse of its restriction equivalence proves this directly, retaining all coherences. Whiskering with psi_p's inverse gives r equivalent to Phi with the specified order of composition.

Step 5 applies the same pointwise-equivalence statement with target T and the explicitly constructed transformation a_E N(c). Here the assumption on e, rather than an unsupported equivalence in the nerve of E, ensures every component e(c_G) is invertible. The endpoints are restrictions of the same map e; this uses the common enrichment and inclusions. Again the full localization property of a_Q, with target T, descends the equivalence, and eta supplies exactly the other endpoint. Step 6 is the elementary quasi-inverse calculation stated there, using the convention of def-cbc-enhanced-diagrams-cones. No theorem about ordinary homotopy categories is substituted for a coherent assertion.

For edge cases I checked equal model structures with R the identity and c the identity (r may be the identity and the comparison reduces to the given compatible presentations), and a terminal target T (all evaluation transformations are uniquely equivalent). The formulas also make sense when E has non-Kan mixed mapping spaces: only A, B, L and T need be quasicategories. All categories and product indices fit in the stipulated enlarged universes. A hypothetical empty bifibrant subcategory would contradict the supplied model-nerve equivalence, not require adding a nonemptiness hypothesis. Every occurrence of W is the common underlying class; no weak-equivalence detection or properness assumption is hidden.

Against delivery-errors B–E: no new unsplit statements, unintroduced objects, hollow definitions, duplicate lemmas, new clauses relabelled as lemmas, circular dependencies, or unsupported transport claims were introduced. Every cited fact was matched against the cited statement; citations.json contains exact excerpts. The six proof steps have lengths 1270, 919, 571, 938, 799 and 530 characters, so none exceeds the 2000-character review threshold. The only unproved inputs are already existing DAG nodes. The principal correction to a possible faulty proof was to descend the ordinary R, never apply the enriched nerve to it. The statement itself required no repair.

## Unfinished work

No mathematical clause remains unfinished. Required server dry run and delivery results are recorded below once they complete. No independent reader or sub-agent was started, following the direct-delivery brief.
