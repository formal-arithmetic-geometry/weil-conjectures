# Worker report: lem-sfb-projective-bundle-picard-classification

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-bundle-picard-classification.json: nine-step split, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-space-invertible-trivial.json: statement-only lemma; no exact Mathlib scheme-level match.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-flat-fibre-section-lifting.json: statement-only lemma; no Mathlib match.
- citations.json: verbatim statement evidence for every use in every step.

## Attachments

None. Searched WeilConjectures for the blueprint id and projective/Picard/invertible terminology. ProjectiveSpaceOverField, CoordinateSectionChart, Serre and Picard modules do not provide the requested relative Picard classification. No compiler was run.

## WANTED

None. All sources used are present locally. No SGA source is used.

## Problems and corrections

The item had no proof, with an EGA II Remark 4.2.7 reference that only announces the locally Noetherian connected-base result. I retain its arbitrary-base statement and supply the extension through existing finite-presentation descent. Its blueprint ancestor is null, as blueprint_refs.py ancestor reports; the explicit detailed ancestor-place chain and via list are retained and extended for the two inputs. The current latest blueprint unit and direct-image proof were read: this is supporting algebraic geometry beneath the stable-moduli/alteration refinement of direct images, not a replacement of the unit route.

I checked Stacks 0BXJ against its source: it omits n>=1, and is false for projective dimension zero. The item has r>=2, so n=r-1>=1 throughout the uniqueness argument. The affine-space input explicitly permits n=0 because a line on Spec k is trivial. I have not changed 0BXJ or imported its false zero-dimensional reading.

The generic Stacks 0EX7 fibrewise-trivial vector-bundle assertion assumes a reduced base. I do not apply it: local triviality is proved through H1 vanishing and proper closed-image shrinking, before descent. In particular no reducedness or global qcqs hypothesis has been added to S.

The general section-lifting node was narrowed to relatively flat invertible sheaves, which is all this proof needs. The source is canonical cohomology base change in 07VK, not the weaker noncanonical finite-free cohomology model already in the DAG. Its future proof must identify the canonical degree-zero comparison. An outline for that future worker: on an affine Noetherian base take a bounded nonnegative finite-free cohomology complex from 07VK. At s split off a unit minor of the map out of degree one; H1 of the fibre being zero forces the residual degree-zero differential to be zero at the local ring (the remaining degree-one map is injective modulo the maximal ideal). The resulting H0 base-change map is surjective. A generator or any desired fibre section lifts after localization and shrinking. This is a report hint only; the new node itself has no proof or proof dependencies.

## Not duplicates

lem-sfb-affine-space-invertible-trivial vs lem-pur-affine-punctured-line-algebra: the existing statement gives affine and punctured lines only; the new input covers affine space in every finite dimension and is needed on every projective standard chart.
lem-sfb-proper-flat-fibre-section-lifting vs lem-trf-infinitesimal-vanishing-section-lifting: the existing node assumes vanishing for every ideal-power graded piece on the localized total space and has no relative-flatness hypothesis; the new node assumes relative flatness and only H1 vanishing on a single fibre. The hypothesis conversion itself requires flatness and coherent base change and is not an instance of the existing statement.
lem-sfb-proper-flat-fibre-section-lifting vs lem-sfb-point-exceptional-isomorphism-neighbourhood: the latter uses 07VK for exceptional curves of birational maps between regular surfaces; it asserts an isomorphism near those curves, not section lifting for an arbitrary proper family.
lem-sfb-affine-space-invertible-trivial vs lem-sfb-projective-line-invertible-classification: projective line classification does not assert triviality on affine spaces of dimension at least two.
lem-sfb-affine-space-invertible-trivial vs lem-sfb-projective-bundle-picard-classification: affine-space triviality is a chart input; it does not assert any classification on a projective scheme or local decomposition over a base.
lem-sfb-proper-flat-fibre-section-lifting vs lem-sfb-projective-bundle-picard-classification: lifting an individual section for an arbitrary proper family supplies neither projective fibre classification nor coefficient-line gluing, degree uniqueness, or base-change compatibility.

## Review by Q26

I read EGA II Remark 4.2.7 on printed page 75, Stacks divisors.tex 0BXJ and 0BDA including their proofs, coherent.tex 07VK and its canonical base-change statement, limits.tex 0B8W including the invertible-module descent proof, and sheaves.tex 00AL/00AM/04TN. For the first new node I checked 0BDA(2) with R=k and the whole affine space, including n=0. For the second I checked that properness and Noetherianity are exactly the hypotheses of 07VK, and relative flatness is explicitly imposed; an invertible sheaf on this locally Noetherian total space is coherent. The zero sheaf on an empty fibre, an empty source, arbitrary residue fields, and nilpotent elements in the base do not invalidate the section-lifting conclusion. The source's derived comparison, rather than arbitrary isomorphisms of cohomology objects, is essential.

For steps 1 and 2 I opened the affine-space input, the integer-twist definition, the existing projective-line classification, and the complete module gluing statement. The chart lemma asserts exactly the triviality used; it is not misused for projective triviality. The units computation is written explicitly in the item using polynomial degrees and Laurent extreme exponents. The triple-overlap computation uses three distinct indices only when n>=2. For n=1 the cited existing classification gives existence and integer uniqueness, and coefficient extension preserves its integer twist. Rescaling by c_i0 inverse is compatible with the convention e_i=g_ij e_j. This checks both sign and the small projective-dimension case.

For step 3 I opened the projective-space properness node, polynomial-projection flatness, invertibility, projective-space cohomology, the new section-lifting statement, and properness's definition. They respectively provide properness, relative flatness on charts, line bases, H1(O)=0, an actual section with the specified fibre restriction, and closed images of closed sets. I wrote the local-ring coefficient argument showing that the lift generates on the fibre; I did not merely infer that its support or point set determines an isomorphism. The complement of the generator locus is a closed subset and properness permits shrinking the base away from its image. This applies over nonreduced Noetherian bases.

For step 4 I opened the finite-locally-free definition and quotient-geometry theorem to verify the local free bundle comparison preserves the tautological line. I opened affine Noetherian approximation and finite-type-over-Noetherian to verify that each integer-subalgebra stage is Noetherian. I opened limit-fibre-products and invertible-affine-limit-descent: the former states an actual scheme limit and affineness of transitions, and the latter requires qcqs stages and such transitions. Projective spaces are proper and separated, hence qcqs, and are base changes of a fixed projective space over Z; these are precisely the hypotheses supplied. Pullback of twists uses their written transition formula. There is no global approximation of a possibly non-qcqs S.

For steps 5 through 8 I reread quotient geometry, the full integer-zero cohomology formula (including the constant monomial), invertibility, pullback's definition, and both clauses of module gluing. Field integer uniqueness makes the degree locally constant. The degree-zero formula identifies the canonical map on functions, not merely an abstract module of the same rank. This remains true on all opens by sheaf gluing; in particular I never assume an intersection of affine opens is affine. The transition units descend uniquely, obey the cocycle equation by injectivity, and give the coefficient line. The same scalar calculation descends an isomorphism of two coefficient lines, establishing uniqueness of their isomorphism classes. For S empty the degree function and coefficient class are unique. For disconnected bases different integers on different open pieces are allowed.

For step 9 I opened representable-unique and checked it actually states uniqueness of representing schemes, in addition to opening quotient geometry's natural bijection. These give the universal quotient after arbitrary base change, including its tautological line. I opened tensor-pullback and pullback-composition statements: these are the actual tensor and composition isomorphisms used. Negative twists commute with pullback because evaluation of a line and its dual is locally the evaluation of a rank-one free module; this argument is spelled out, with no exactness of nonflat pullback assumed. Multiplying explicit transition functions proves tensor additivity, and uniqueness identifies the pulled-back invariants. No arbitrary base-change theorem for a different coefficient category enters.

I checked delivery-errors B--E against each node. Both new statements introduce their own objects and cite the definitions they need, have no proof sketch, and are strictly smaller inputs. All mathematical assertions not written out as the chart, local-ring, sheaf, or scalar calculations cite statement nodes. No step exceeds 2000 characters. The natural-language proof is agent-written because EGA only announces the result and the arbitrary-base assembly is expanded here. Searches of the whole DAG, blueprint_refs, and WeilConjectures were completed before creating either node. The semantic searches mostly returned ring Picard facts or generic base-change facts; I also read Mathlib's UFD Picard instance at RingTheory/PicardGroup.lean:886. It concerns algebraic invertible modules, so is not an exact scheme-level leaf without the affine sheaf/module bridge. The current new nodes have real, logged leanfinder, loogle, leansearch and grep queries, with a second phrasing; searches are preserved in searches.jsonl. The cited off-unit tools are declared in split_report.tool_uses and supply generic interfaces only.

## Unfinished

Neither new input is split, as required for a one-level stage-1 delivery. No Lean files were written, no git command was run in the shared repository, and no compiler or build tool was used.
