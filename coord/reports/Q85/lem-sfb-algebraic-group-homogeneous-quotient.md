# Q85: lem-sfb-algebraic-group-homogeneous-quotient

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-group-homogeneous-quotient.json: statement, split into twelve proof steps; no exact Mathlib or project attachment.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-immersion-fppf-descent.json: statement only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-extension-open-exhaustion.json: statement only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-scheme-finite-set-affine.json: statement only, unsplit; no Mathlib match.
- citations.json: one complete verbatim cited statement for each step/node pair. Full statements preserve their hypotheses and qualifiers.
- report.md and searches.jsonl: report and actual launcher search records. The scratch assembly script is not part of the DAG delivery.

## Attachments

No attachment for the item. Searches of the live project library for the exact blueprint tag and homogeneous quotient notions do not find a declaration stating all clauses. The available free-action algebraic-space quotient is an input, not scheme representability. Mathlib Scheme.LocalRepresentability.isRepresentable proves the open-cover representability criterion, not existence of a homogeneous quotient. The existing node lem-pc-schemes-criterion already states that criterion and records the declaration; it is reused instead of creating the initially considered Mathlib leaf.

## WANTED

None. All sources used are available in literature/.

## Problems found and corrections

The imported item is true as stated; its statement and statement dependencies are retained. Its earlier Q43 searches are retained and augmented with the actual Q85 searches. A naive proof by taking rational cosets is insufficient over imperfect fields and for torsors without sections. The split uses the fppf sheaf quotient and only obtains a scheme after finite extension and effective descent.

Milne B.37 initially assumes quasi-projectivity to obtain the generic quotient through B.35. I do not import that assumption or invoke its outside references: Stacks 06PH gives the algebraic-space quotient, and the existing quasi-separated-space dense-scheme-open theorem supplies the required initial open. The rest follows Milne B.36 and B.37 Steps 1–3. The affine-neighbourhood lemma applies to a scheme already constructed, and does not package scheme existence or a clause of the item into a new node. The closed diagonal uses actual closed-immersion descent: the existing quasi-compact-immersion locality statement alone would not suffice.

The chapter and inherited unit remain fixed. I read the latest blueprint direct-images proof, paragraph (3), and its section; the lower-level algebraic-group prerequisite realizes the inherited parent factorization argument. No direct-image unit step is rerouted. The inherited blueprint ancestor is null; its detailed place and full via chain are retained, and each new node extends that chain through this item. The latest blueprint and DAG search found no equivalent blueprint statement for any of the three new facts.

## Not duplicates

lem-sfb-space-closed-immersion-fppf-descent vs lem-trf-space-closed-immersion-cover-descent: the existing statement descends along etale scheme covers; the new statement allows arbitrary fppf coverings of algebraic spaces, as required for q times q.

lem-sfb-space-closed-immersion-fppf-descent vs lem-sfb-space-quasi-compact-immersion-locality: the existing conclusion is a quasi-compact immersion, which need not be closed; the new statement descends closedness as well.

lem-sfb-space-closed-immersion-fppf-descent vs lem-sfb-invariant-closed-substack-descent: the existing statement descends invariant closed subschemes along a smooth atlas of a stack; the new statement tests an arbitrary algebraic-space morphism along a flat lfp cover, with no smoothness assumption.

lem-sfb-space-closed-immersion-fppf-descent vs lem-sfb-singleton-stack-finite-field-homeomorphism: the latter constructs a finite residue field for a reduced one-point stack, not closed-immersion locality.

lem-sfb-finite-extension-open-exhaustion vs lem-kun-closed-point-field: finite residue fields at closed points do not state exhaustion of a compatible family of varying opens after a finite extension; B.36 requires an additional dimension argument.

lem-sfb-homogeneous-scheme-finite-set-affine vs lem-pd-projective-finite-affine-neighbourhood: the existing statement assumes an affine morphism into projective space; the new statement assumes a flat surjective homogeneous orbit map and no projective presentation.

lem-sfb-homogeneous-scheme-finite-set-affine vs lem-sfb-algebraic-group-homogeneous-quotient: the new lemma assumes that Y is already a scheme with a homogeneous action and concludes its finite-subset affine property. The item constructs that scheme and does not state this property. Thus this is an independent conditional descent tool, not a restatement of the item.

No new open-cover gluing node was created: lem-pc-schemes-criterion is reused exactly.

## Review by Q85

I read Milne Theorem 5.28, Definition 5.20, Proposition 5.25, Appendix B.36 and B.37 (printed pp.104–105 and 604–606). For closed-immersion descent I read spaces-descent.tex, lemma-descending-property-closed-immersion, and checked its tag 0420 in the tag table. For the new exhaustion statement I used precisely B.36, including a fixed algebraic closure and compatibility for every inclusion of finite intermediate fields. In particular, the extensions need not be separable. For the new affine-neighbourhood statement I read B.37 Step 2: the translation argument starts with an existing homogeneous scheme, passes to finite fields to obtain simultaneous rational lifts and a rational translating element, and descends an invariant affine neighbourhood by the finite locally free relation. The printed version treats closed points; a finite set of arbitrary points is contained in an affine open once one chooses a closed specialization for each, since opens are stable under generalization and finite-type field schemes are Jacobson. This property is deliberately left as the new node's mathematical task, rather than hidden in an assembly step. The hypotheses of the new conditional version give the same fppf quotient by the stabilizer of o: on test schemes the equality of two orbit values is exactly that their difference stabilizes o, and the given fppf orbit map provides local lifts. No normality of the stabilizer is used.

For Step 1 I checked the closed subgroup really is finite type by its affine quotient rings. Field flatness is written as the vector-space-basis argument, and pqf-lem-lft-fp-locnoeth actually concludes lfp over the locally Noetherian field base. The inverse in l acting on g is essential for a left action; I checked the order of both products. The scheme-to-space node retains the Yoneda sheaf, so no change of objects is implicit.

For Step 2 I opened lem-sfb-free-flat-group-space-quotient: it gives the algebraic space, flat surjective lfp map and full sheaf kernel-pair isomorphism, without an affineness or smoothness assumption. Inverting its group coordinate gives the displayed right-coset relation. The sheafification definition gives the universal factorization used to descend left translations; identity, associativity and equivariance already hold on the orbit presheaf. This step does not assume normality or a group structure on the quotient.

For Step 3 I checked the same kernel-pair statement identifies the base-changed diagonal with the closed inverse image of L under difference. I opened the covering-calculus node: its base-change and composition clauses make q times q an fppf cover. The new descent statement really concludes closed immersion, not merely monomorphism or immersion. Closed immersions on affine tests are affine quotient maps, hence quasi-compact, so the dense-open theorem's diagonal hypothesis follows.

For Step 4 I opened the representable lft source-descent statement and verified both morphisms are representable by algebraic spaces; it imposes neither quasi-compactness of the source cover nor Noetherianity. The topology theorem supplies continuity; its surjectivity is supplied by the quotient theorem. Continuous image gives quasi-compactness of F. The qcqs permanence node applies first to F over the affine field base and then to G over F. Separatedness gives quasi-separatedness; the absolute diagonal factorization through the field base justifies the absolute convention in the permanence statement. Thus the use is not an illicit conversion of finite type into finite presentation on an arbitrary base.

For Step 5 I read the existing representability criterion in full, including its current blueprint update on smallness and set-indexing. A union of scheme open subspaces has those scheme opens as relatively representable open subfunctors. Their index family is a set of opens, and the algebraic-space fpqc-sheaf theorem supplies the Zariski sheaf hypothesis. The criterion supplies representability of the union; translation invariance follows by applying an automorphism and its inverse. Extension compatibility is inclusion, not an unjustified claim that the whole scheme locus commutes with base change.

For Step 6 I checked the dense-open theorem accepts a quasi-compact diagonal and supplies an open dense scheme. Nonemptiness follows from the identity of G and surjectivity. A principal affine inside its inverse image is still finite type, so the closed-point-field lemma applies to its maximal ideal. For Step 7 I checked all hypotheses of B.36 for the fixed scheme G over k1, including every further finite extension and monotonicity. The covering-calculus node supplies surjectivity after extension. The four-property descent node explicitly includes arbitrary base change of finite type and separatedness, so the resulting Y satisfies the hypotheses of the next step.

For Step 8 I checked the new affine-neighbourhood statement has a given rational origin, the genuine left action and a flat surjective lfp orbit morphism. These are available on Y=F_K; no scheme existence is taken from that node. For Step 9 I opened the descent-datum definition and both invariant-affine descent nodes. Spec K to Spec k is finite flat lfp surjective, even when K/k is inseparable. The first node's finite-subset condition is exactly Step 8; its invariant affine conclusion is precisely the second node's hypothesis. Thus their combination really gives an effective scheme descent, rather than the false assertion that arbitrary schemes descend effectively for all fpqc covers.

For Step 10 I checked the fpqc-sheaf node applies to both the algebraic space and the representable scheme sheaf. The canonical descent datum makes the two equalizer diagrams agree, on all test schemes. It identifies the scheme and quotient naturally, so the geometry already proved transports along an isomorphism. For Step 11 I evaluated the actual kernel-pair isomorphism on T; the formula yields an L(T)-element, not just an element after a field extension. For Step 12 I opened the quasi-compact base-change statement and the precise fpqc-covering definition. Over each affine of T the inverse image has a finite affine cover; together with flatness and surjectivity this verifies that very definition and supplies the lift by the second projection.

I tested L=1 (X=G), L=G (X=Spec k), a nonnormal subgroup, finite nonreduced alpha_p in G_a, a non-affine abelian group, finite fields, and purely inseparable field extensions. Nothing uses reduction, etale local sections, an infinite ground field, or normality. Empty test schemes cause no exception. The new B.36 lemma permits an empty Z; the homogeneous AF lemma has a given origin and consequently a nonempty Y. All twelve assembly steps are shorter than 2000 characters. The substantial open-exhaustion and AF arguments are explicit new nodes, not hidden long steps. The citations file copies verbatim statements rather than bending a quote to the desired inference. I checked delivery-errors B through E against these choices, including existence versus chosen objects, smallness, generic tools, complete arbitrary-test-scheme clauses and noncircularity.

## Unfinished work

The three new statement-only lemmas are intentionally unsplit stage-1 dependencies. No Lean writing or compilation was performed. Delivery validation follows with the required launcher dry run.
