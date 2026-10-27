# Stage-1 delivery: lem-trf-integral-birational-normal-isomorphism

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-integral-birational-normal-isomorphism.json`: existing statement node, now split into four proof steps; not a Mathlib leaf.
- `citations.json`: a verbatim statement quotation for every node used in every proof step.
- `searches.jsonl`: actual msearch log for this worker; inherited searches in the item were retained.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. No unit record, Lean file, repository file or launcher script was changed. The item statement and its statement dependencies are unchanged, as are its inherited source, provenance and blueprint fields (apart from confirming the empty same_as result).

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id and for integral/birational/normal/isomorphism terminology. The normalization and dense-open extension declarations found impose different hypotheses or concern a different morphism. In particular the locally Noetherian dense-open extension theorem does not cover this arbitrary integral morphism. No exact project attachment was found.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## What needed correction

The imported item had a correct statement and no proof. Its source, Stacks Tag 0AB1 (`morphisms-lemma-finite-birational-over-normal`), explicitly says “finite (or even integral)”; no statement dispute is necessary. The existing `lem-trf-finite-birational-normal-iso` proves only the finite case, so citing it would silently add a finite-module hypothesis. I retained the integral case and supplied the complete affine argument directly. The existing finite proof also indicates the reusable affine field and local-normality nodes; those statements, rather than that proof as a black box, are cited here.

The Mathlib search results are not a leaf for this item: `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom` (Normalization.lean:287) says that the source-to-relative-normalization arrow is an isomorphism. It says nothing by itself about the given arrow to a normal target. Read its proof through line 305. Two different semantic phrasings, Loogle, LeanSearch and source grep were run with msearch and their results read. The grep call scoped to the single Normalization.lean file prints malformed file/line columns because rg omits a filename for a single file; its hits were read as line numbers and checked against the source, not used as a declaration match. The other grep searched the AlgebraicGeometry directory. All newly recorded queries agree verbatim with searches.jsonl.

## Not duplicates

No new nodes were created. The item vs `lem-trf-finite-birational-normal-iso`: this item permits integral morphisms without finiteness, whereas that existing node assumes a finite morphism. Neither its statement nor its hypotheses were altered. Searches of the whole DAG for Tag 0AB1, normality, affine rings and function fields, and blueprint_refs searches for birational, integrally closed, fraction field, 033L, 0358 and isomorphisms are local, were used to find existing material. The current latest blueprint ancestor proof, trace-formula chapter and Frobenius local-vanishing unit were read. This is a generic geometric auxiliary input along the existing Temkin/connectedness branch, not a replacement of a unit step.

## Review by Q155

I read the complete statement and proof of Stacks Tag 0AB1 in morphisms.tex:14630ff, including the words “or even integral”. Its affine proof makes no Noetherian, finite-presentation or module-finiteness assumption. I also read Properties Tag 033L (`lemma-integral-normal`), the local-to-global normality proof of Algebra Tag 030B (`lemma-normality-is-local`), Schemes Tag 01HV (`lemma-spec-sheaves`, especially parts (1) and (6)), and the rational-function identification of Morphisms Tag 01RV (`lemma-integral-scheme-rational-functions`). For the affine isomorphism and final gluing, I read Mathlib Morphisms/IsIso.lean:48ff and Gluing.lean:448-475, and the gluing of the local g_i in the proof of Schemes Tag 01JJ (`lemma-glue-functors`), with Sheaves Tag 00AN (`lemma-mapping-property-glue`). No new node needs a separate source review.

Step 1 uses precisely the integral part of `def-weil-finite-integral-morphism` and `lem-sc-integral-function-field-affine-fraction`. I opened both complete statements. The former supplies affineness and the monic-equation condition, and the latter supplies membership of the generic point, both domain assertions, injective germ maps and the fraction-field identification. I checked nonemptiness of the inverse image using the explicitly assumed generic-point image. The displayed equation beta u = phi alpha is the germ naturality identity, written out on a section, so the embedding of B into k(T) uses the inverse of the supplied field isomorphism and gives exactly the original ring map u on A. No unrelated abstract field isomorphism is substituted.

Step 2 uses `lem-weil-pbc-affine-open-stalk-localization` clause (c), `def-weil-pbc-normal-ring`, and `lem-weil-pbc-normal-domain-of-local-normal`. I read each full statement. Clause (c) identifies the localization at each maximal ideal with the actual target stalk; the hypothesis on all stalks therefore gives the premise of the normal-domain criterion. The domain premise was established in Step 1. Ring-isomorphism invariance is the direct transport of a monic equation and its root, stated explicitly. Normality is taken in the fraction field of A, already identified with K; no excellence or Noetherian condition enters.

Step 3 uses the same integral definition, the elementwise definition of normal domain, and `lem-sc-affine-global-sections-iso`. Their statements really give, respectively, a monic equation for each b, membership in A for its root in K, and an isomorphism of affine schemes from the ring isomorphism. I wrote the equation and used injectivity of B into K to turn membership into surjectivity of u. Both the source and target of the affine restriction are affine by Step 1. This step is marked non-elementary because its last inference applies the cited affine equivalence result; it hides no additional algebra lemma.

Step 4 uses `lem-weil-pbc-scheme-morphism-gluing`, whose statement supplies existence of the glued morphism and equality of maps detected on a cover. I opened its statement and checked both clauses. I wrote out why local inverses land in the preimage of the overlap, why their restrictions are both inverses of the same restricted isomorphism, and why both global inverse identities hold. Intersections need only be open, never affine. This spells out local-to-global isomorphism detection without introducing a new node for a few lines from the gluing statement. All cited supporting statements are already Mathlib leaves, so there is no off-route unsplit lemma requiring a tool-use exception. The step lengths are all below 1000 characters, hence none crosses the 2000-character long-step threshold.

I checked delivery-errors B–E against the actual files. B: no new nodes or proof sketches masquerading as statements; all TeX has single literal backslashes after JSON decoding, sources have their correct tags and labels, inherited metadata is retained, and no unrun search is recorded. C: each non-elementary input is one of the cited statements just discussed; citations.json copies those statements verbatim, including localization clause (c); proof_deps is exactly the union of uses. The reused leaves do not depend on this item. D: the steps carry the common-field, integral-closure and inverse-gluing arguments themselves, with no restatement node or relocation of the item. E: no finite-type assumption, no affine-overlap assumption, and no claim that an integral morphism is finite.

Edge cases: the schemes are integral and therefore nonempty. Empty affine opens can be omitted from a cover; they are not passed to a domain/fraction-field lemma. The inverse image of every nonempty target affine contains eta_Z. A zero-dimensional normal target such as Spec k gives K = k and the argument forces B = k. For arbitrary non-Noetherian domains the maximal-localization normality criterion still applies (its statement has no Noetherian premise), and no finite subcover is needed. Dropping normality permits the finite birational cusp normalization Spec k[t] -> Spec k[t^2,t^3], which is not an isomorphism. Dropping the field-isomorphism hypothesis permits nontrivial finite extensions Spec L -> Spec k. Dropping integrality permits dense principal-open immersions such as Spec Z[1/2] -> Spec Z. These checks isolate exactly the hypotheses used, and no statement repair was required.

## Unfinished work

None within stage 1. The item is a split, not a Lean proof; its already-existing dependencies retain their own states. Required remote dry run and direct delivery are recorded by the delivery command's output.
