## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-curve-etale-scheme-cover.json: statement unchanged; three-step split following Stacks 0E6F.
- dag/nodes/sec-six-functors-basics/lem-sfb-curve-smooth-polarization-cover.json: statement, unsplit; no Mathlib match. This is the smooth polarization input of 0DQ0, not another copy of the etale scheme-cover conclusion.
- citations.json: a verbatim statement excerpt for each of the five step citations.
- searches.jsonl: actual search-command log, retained unchanged.

Attachments: none. Searches of lean/WeilConjectures by the blueprint tag, algebraic-space terminology, polarization and curve/etale scheme-cover terminology found no declaration stating the item. The Picard scheme results concern smooth projective curves and do not cover these arbitrary proper flat algebraic-space families.

WANTED: none. All the required sources are present.

The item was unsplit and the sandbox contained no earlier node or report. I read moduli-curves.tex section-stack-curves, the description of PolarizedCurves immediately before lemma-polarized-curves-in-polarized, lemma-polarized-curves-over-curves (0DQ0), and lemma-etale-locally-scheme (0E6F). The latter explicitly unwinds 0DQ0 into the smooth cover with a relative polarization. I also read more-morphisms.tex lemma-etale-dominates-smooth (055V) and spaces-topologies.tex lemma-etale-dominates-smooth (0CFV). The existing node lem-sfb-smooth-space-cover-etale-sections gives the needed factorization maps; no new refinement lemma is needed. Relatively ample on an algebraic space includes representability by spaces-divisors.tex definition-relatively-ample (0D31), and its scheme-base sanity check; the source's PolarizedCurves objects already have scheme total spaces.

The searches for the new node used its own polarization-cover statement in three semantic phrasings, plus LeanSearch, Loogle and grep through the mandated msearch.py command. Their actual results are recorded in its mathlib_searches. I read the returned types: scheme smoothness, flatness, universally open morphisms, scheme base-change stability and affine local presentations do not produce a polarization. The quoted-name Loogle query and the polarization grep had zero hits. Further item searches are appended without removing its inherited Q74 searches. No search was fabricated and no unavailable service was treated as a negative answer.

The whole-DAG searches included 0DQ0, polarized-curves-over-curves, polarized/polarised curves, relative ampleness, Picard smoothness, 055V and 0CFV. The whole imported blueprint was searched with blueprint_refs.py for polarized, polarized curve, 0DQ0, etale locally scheme, ample smooth and curve scheme. The broad results were inspected: none states the new polarization-cover input. The existing relative Picard-space smoothness result requires universal H0=O and cannot replace the Picard-stack input for a general family; I did not add that hypothesis.

The inherited blueprint ancestry is broken at created.item = Sheaf.SixFunctors.CtfStabilityDirectImages, a module name without a DAG node. blueprint_refs.py ancestor returns None. I retained the inherited null from.node and exact place/via chain; the child prepends this item to via. I read the current latest blueprint's sk-thm-sf-ctf-stability direct-images proof (3), not the old snapshot named by inherited metadata. This source represents the higher-level purpose; the actual local proof follows 0E6F without changing the unit route.

Nothing mathematical remains unfinished in the item's split. The new node deliberately remains statement-only for the next stage-1 split.

## Not duplicates

There are no existing DAG nodes with Tag 0DQ0. The tag 0E6F also occurs in the existing parent lem-sfb-proper-space-curve-qcoh-bound and in this item; neither states the smooth polarization input. The new node cites 0E6F only to locate where its 0DQ0 consequence is explicitly unwound.

lem-sfb-curve-smooth-polarization-cover vs lem-sfb-curve-etale-scheme-cover: the former supplies a smooth surjective scheme morphism and a relative polarization on the pulled-back curve, whereas the item constructs an etale covering; passing from smooth to etale requires the independently existing refinement statement and the explicit pullback argument.

lem-sfb-curve-smooth-polarization-cover vs lem-sfb-proper-space-curve-qcoh-bound: the latter proves vanishing of quasi-coherent cohomology in degrees greater than one and has no polarization-cover assertion.

lem-sfb-curve-smooth-polarization-cover vs lem-sfb-space-relative-ample-locus: the latter starts with a globally supplied line module and detects where it is ample; the new node constructs a line module after a smooth cover, without a supplied line module.

lem-sfb-curve-smooth-polarization-cover vs lem-sfb-space-relative-ampleness-fpqc-descent: descent starts with a line module and a covering and does not supply the new node's cover or line module.

lem-sfb-curve-smooth-polarization-cover vs lem-sfb-smooth-space-cover-etale-sections: the existing node refines a supplied smooth surjection for arbitrary spaces, without constructing the surjection or a relative polarization. It is reused in step 2.

## Review by Q18

I checked B through E with the sources and the exact cited statements open. For the item, 0E6F and section-stack-curves assume precisely properness, flatness, finite presentation and relative dimension at most one, and allow empty fibres. I left every hypothesis and the conclusion untouched. The new statement is the smooth-cover consequence which the first paragraph of the 0E6F proof expressly derives from 0DQ0. I checked the preceding definition of PolarizedCurves: its total space is a scheme, and its line module is relatively ample, meaning ample over every affine base open. Thus step 1 does not silently infer that an arbitrary algebraic space with an arbitrary line module is a scheme. The new statement defines the morphism properties and the dimension convention inline and cites the existing definitions for schemes, spaces, smoothness, invertible modules and ampleness. It contains no proof, no hidden genus restriction, and no source tag used as a substitute for meaning.

For step 1 I compared every family hypothesis with the new node's statement, including geometric fields and empty fibres. It supplies exactly U, p and Y that the step retains. Step 2 cites the existing smooth-space-cover-etale-sections statement, whose conclusion explicitly includes e_i, v_i and p v_i=e_i. I checked its hypotheses: taking S=T, the source U is a scheme and hence an algebraic space over T, and p is both smooth and surjective by step 1. No individual etale map is assumed surjective. The existing theorem includes set indexing, the chosen universes and the empty target. Both statements belong to this item's unit, so no off-unit proof tool is substituted for the route.

In step 3 the cited scheme fibre-product definition gives existence of Y times_U T_i as a scheme. The algebraic-space fibre-product statement says it is the sheaf fibre product, and the algebraic-space definition explicitly identifies maps with natural transformations. I wrote both inverse maps on A-points; the equality p v_i=e_i is exactly what makes the second pair satisfy its fibre-product relation. Substitution commutes with restriction in A. This is an elementary universal-property calculation, rather than an uncited base-change theorem. It also avoids an unnecessary theorem about preservation of ampleness under arbitrary base change: only the scheme conclusion is requested. The five citations in citations.json were checked as exact substrings of the statements, not of their proofs.

I tested the new statement on an empty base (the empty scheme is a smooth surjective cover of it), empty total space over a nonempty base (the empty scheme has its unique invertible ample module), zero-dimensional fibres, disconnected and nonreduced curves, and a non-Noetherian base. None needs positive genus, purity of fibre dimension, connectedness or a fixed Hilbert polynomial. The smooth polarization input is genuinely a moduli lemma, not a two-line elementary fact, while the final fibre-product comparison needs no new node. All proof steps are shorter than 2000 characters. There was no disputed statement and no SGA route. The corrections during preparation were to reuse the existing refinement lemma and to use its explicit factorization maps rather than recreate a duplicate or cite an ampleness-descent statement for a line module not yet constructed.
