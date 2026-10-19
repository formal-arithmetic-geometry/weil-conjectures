## Worker report

Group Q59; item lem-trf-coherent-log-ideal-chart-construction; stage 1 only; 2026-10-18. This is direct delivery with self-review followed by the maintainer's independent review. There was no earlier item copy, report or search log in this sandbox. The repository and both Lean source checkouts were read only; no git command, Lean write, compiler or Lake invocation was made there. All authored files are in this item's sandbox.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-coherent-log-ideal-chart-construction.json: the item, split into ten steps. Mathematical conclusion and hypotheses retained; fine and strict are defined inline at the end to remove implicit terminology.
- dag/nodes/sec-trace-formula/lem-trf-fine-monoid-finite-saturation.json: new statement-only generic algebra input, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-polarized-fine-log-etale-descent.json: new statement-only generic descent input, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for every proof-step citation.
- report.md: this report. searches.jsonl and search-*.txt preserve the real Mathlib searches and their returned types. ilo.txt is a local extraction of the source, not a delivery file.

Two new nodes, zero Mathlib leaves. Both new nodes have empty proof and proof_deps. They are not new names for the blowup clauses: finite monoid saturation makes no mention of log schemes or blowups, and polarized log descent makes no mention of monoidal ideals, blowups, fractions or principalization. The local chart argument, overlaps, principalization and both universal properties remain in the item.

## Attachments

None. I searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint id and for LogStructure, LogScheme, LogBlow/logBlow, logarithmic blowups, monoidal ideals and saturation/localization combinations. There is no project declaration stating the item. The upstream master snapshot is only reference material, never evidence of a finished proof.

## WANTED

None. The ILO PDF and the Stacks TeX files used below are available locally. No literature download was needed.

## Source and blueprint audit

I read the item, chapter sec-trace-formula, unit sk-i-curve-zero, its nearest blueprint ancestor lem-trf-local-term-locality and that ancestor's current main-20261015 text/update. This item is a generic chart-construction input in the existing nearby-duality / alteration / log-regular-resolution ancestry. It supplies the existing log-blowup-normalization route, rather than replacing the unit or chapter route. No chapter, unit, ancestor or other worker's node is changed.

For the item I read ILO, Expose VIII, 3.1.17--3.1.21 (printed p. 101), 3.3.3--3.3.9 (printed pp. 106--108), and 3.4.2 (printed p. 110). The finite-saturation input is the finite-morphism sentence in the proof of VIII 3.2.9 (printed p. 104), together with localization compatibility in 3.1.17. In particular, I do not use 3.2.9's normalization identification or its normal-base hypothesis: finite saturation of the monoid algebra is the independent algebra assertion needed here. The new monoid node does not assert that arbitrary monoid algebras of saturated monoids are normal in the presence of torsion.

The new descent input makes precise the scheme-effectivity point in the last sentence of VIII 3.3.8. I read Stacks spaces.tex, theorem-presentation (02WW), spaces-descent.tex, proposition-fpqc-descent-quasi-coherent (04W8) and lemma-descending-property-ample (0D3C), including the latter's proof through relative Proj. The quotient of the etale descent relation is initially an algebraic space; the compatible invertible sheaves descend, and relative ampleness descends by 0D3C, which makes that space a scheme. Fine log structures and their maps then descend as monoid sheaves with structure maps on the small etale site; being fine or fs is etale local. This is a generic descent theorem; it does not import a principalization theorem into a new node.

Whole-DAG searches looked at statements, tags and keywords, not only file names in this chapter. The whole imported-blueprint searches included: log blow, logarithmic, log structure, monoid, saturated monoid, finite saturation, saturation commutes, finite union translates, fine log descent, polarized, relatively ample, ample invertible, descent, and glue schemes. No blueprint node states either new result. Searches with broad descent and monoid words returned unrelated category-theoretic monoidal material and the existing Picard descent nodes; these were opened where relevant. blueprint.from.node is lem-trf-local-term-locality, with the complete inherited via chain and the item prepended for each child. The from.place and split_report.blueprint identify the alteration/log-resolution use rather than claiming that the current ancestor's trace statement itself is a logarithmic chart theorem.

## Mathlib searches

All new searches ran through the required msearch.py command and are in searches.jsonl. The item and each child have LeanFinder, LeanSearch, Loogle and grep records; the two semantic phrasings were different questions about the same claim. I read every returned type. No unavailable response is recorded as absence.

For finite monoid saturation, LeanFinder returned FG of the Grothendieck group, monoid localization, and semilinear sets. I also inspected Mathlib/GroupTheory/Finiteness.lean lines 619--630: fg_eqLocusM is a Gordan lemma for equalizers in a canonically ordered, well-quasi-ordered monoid. It is not a one-line specialization giving finite root closure as a module. GroupTheory/Subgroup/Saturated.lean lines 25--43 defines NSMulSaturated but gives no finite-saturation construction. The other Loogle saturation is factor closure, not the root closure used here. A second root-closure phrasing returned semilinear-set descriptions only. The new node is unsplit, not a Mathlib leaf.

For polarized fine-log descent, both semantic queries returned etale categories and descent of properties of already existing morphisms. The grep over AlgebraicGeometry found such morphism-property descent, and the refined LogStructure/LogScheme/IsAmple/RelativelyAmple search returned no hit. Those results do not construct a scheme or a log structure from a polarized descent datum. The item queries returned ordinary ideal-sheaf gluing, Proj and perfectoid examples, none with the log universal properties.

## What needed correction or expansion

The imported item had no proof. Its mathematical assertion agrees with the cited source, so there is no STATEMENT-DISPUTED correction. I added explicit meanings of fine and strict, not a new hypothesis. I did not identify a log principal generator with a nonzero function and did not identify the log blowup with the ordinary blowup of K. That identification requires additional hypotheses and is particularly wrong for the logarithmic point example below.

The source's short phrase about descent was expanded: arbitrary scheme descent along etale covers is not automatically effective. The generator torsor of the principal log ideal supplies a compatible relatively ample line bundle, and its affine nonvanishing loci are computed explicitly. This permits the new generic polarized-descent theorem to apply. The overlap identity is written inside the common group completion and is preserved by saturation and base tensor products. Fine test objects and fs test objects are treated separately; saturation is used only in the fs extension step.

## Not duplicates

lem-trf-fine-monoid-finite-saturation vs lem-trf-fs-face-sharpening: the existing node starts with a saturated monoid and localizes and sharpens a face; it does not construct the saturation of an unsaturated monoid, prove it finitely generated, or prove module finiteness of the monoid-algebra extension.
lem-trf-fine-monoid-finite-saturation vs lem-trf-fg-commutative-monoid-finite-presentation: the existing node gives finite relations for a generating tuple, not saturation, finite translates or localization compatibility of saturation.
lem-trf-fine-monoid-finite-saturation vs lem-trf-coherent-log-ideal-chart-construction: the new generic input applies to every fine monoid, with no ideal, chart base ring or log scheme; the item's Q_e are derived in its own Step 2, and the finite map is derived by tensoring in Step 10.
lem-trf-polarized-fine-log-etale-descent vs lem-pc-fpqc-descent: the existing node descends modules on a fixed scheme; the new node constructs the underlying scheme from a polarized descent datum and descends its log structure.
lem-trf-polarized-fine-log-etale-descent vs lem-weil-pbc-fpqc-representable-descent: the existing node descends morphisms into a fixed scheme; it does not provide effectivity for a polarized family of schemes and log structures.
lem-trf-polarized-fine-log-etale-descent vs thm-pd-effective-descent: the existing node assumes a surjective finite locally free cover and projectivity, without requiring a linearized polarization; the new node handles arbitrary jointly surjective etale chart covers with a specified compatible relatively ample line bundle, and includes the logarithmic structures.
lem-trf-polarized-fine-log-etale-descent vs lem-weil-pbc-glue-schemes: ordinary gluing along open immersions is effective without a polarization; the new statement addresses etale descent and the scheme-effectivity obstruction.
lem-trf-polarized-fine-log-etale-descent vs lem-trf-coherent-log-ideal-chart-construction: the new node is a generic descent input for any polarized fine log schemes, has no ideal or principalization conclusion, and is used only after the item has constructed its charts, universal properties, line bundle and cocycle.

## Review by Q59

I reopened every cited node and compared its statement with each use, rather than reading only its source label. citations.json contains the actual statement text in each case. The two new inputs are statement-only, self-contained, introduce every object, and have search records that came from real command outputs. TeX has single mathematical backslashes after JSON decoding. Neither node contains a proof sketch in its statement. I checked the B--E return checklist against the files and the sources named above.

Step 1 uses the definition of coherent monoidal ideal to identify the local ordinary ideal with (alpha(e)), etale-to-fpqc to supply the covering hypothesis, the actual equivalence of module descent data in lem-pc-fpqc-descent to descend the ideals and inclusions, and finite-module descent to obtain finite type. A finite affine refinement gives a faithfully flat product algebra, so the latter node's faithful-flat hypothesis is present. The image ideal calculation is just multiplication by chart elements and units; no log-regularity or nonzero-divisor assumption is used. pqf-def-coherent supplies the definitions of the two conclusions. I explicitly read that the module node gives effective descent of objects and maps, not merely a statement about flatness.

Step 2 obtains integrality and equality of group completions from P contained in Q_e contained in P^gp; these are direct subgroup-generation checks. The new finite-saturation node applies because the displayed finite generators really generate Q_e, and supplies exactly finite generation and finite translates. It assumes no torsion-freeness; none is silently supplied. This is an algebra tool, not the chart-universal-property clause under a new name.

Step 3 uses the actual associated-log pushout in def-trf-fs-log-blowup and the ordinary balanced tensor product definition. The structure map and the extension of charts are specified, not assumed. The equality h=e+(h-e) proves principalization in the monoid. This remains valid if every alpha(e) is zero. It is an elementary construction from the cited definitions and the monoids from Step 2.

Step 4 proves both inclusions in the common-localization identity and the triple-overlap identity explicitly. The finite-saturation node's localization clause, not a claimed flatness or normalization fact, is what permits the saturated overlap. lem-weil-pbc-glue-schemes explicitly supplies existence and the prescribed chart intersections, precisely the data used here. Log sheaves and their structure maps glue by the given isomorphisms; this last part is the sheaf construction. No etale intersection is called an affine localization: these are the specific principal opens of the chart schemes.

Step 5 uses the log-ideal definition, integrality of fine log structures, and the monoid/ring presentations. The stalk equation m=g(e)+b and cancellation show that an original generator e, rather than a newly chosen element, generates locally. The resulting group homomorphism sends every h-e to its unique quotient in the integral monoid. I added the existing lem-weil-pbc-morphism-into-affine-scheme, whose statement really is the bijection of scheme maps with maps into global sections (and the principal-open inverse-image formula); it justifies the scheme map from the balanced ring map. The new descent input's morphism clause glues etale-local lifts. It is not being used for effectivity at this step. Both existence and uniqueness are given, with no saturation assumed for this fine test object.

Step 6 checks why fs chart structures have saturated stalk monoids using lem-trf-fs-face-sharpening: its statement really gives a saturated face localization and saturated sharp quotient. Passing back from the characteristic quotient uses only that units form a group. The prescribed map on group completions, rather than an arbitrary choice of roots, then extends to Q_e^sat. This meets the fs, not merely fine, hypothesis. Stalkwise membership and the sheaf property provide the local sections; the same morphism-descent clause finishes gluing.

Step 7 is the tensor presentation under a strict restriction and uniqueness of universal objects. It does not claim that an arbitrary log base change has an underlying scheme base change. Only strict etale restrictions are required, and on those the chart is unchanged. Chart-independent comparisons and their cocycles follow from uniqueness, so they are elementary consequences of the preceding steps.

Step 8 computes a line bundle, not an invertible ordinary ideal. Its frames have transition v_f=alpha(f-e)v_e. Its section associated to h has coefficient alpha(h-e) on the e-chart. Consequently its nonvanishing locus is exactly the h-chart, on both the fine and fs versions. The finite affine cover checks both conditions in the actual def-weil-pbc-ample-invertible-module, without applying the proper-over-a-field version of the ample criterion. The invertible-module definition is met by the locally free rank-one gluing. The generator torsor of the principal log ideal, whose action is free by cancellation, explains why the line bundle is independent of all chart choices. This is the elementary gluing calculation, not an unproved assertion of scheme descent.

Step 9 applies the new polarized-descent statement only after furnishing the log isomorphisms, their cocycle and the compatible relatively ample line bundles. Their effectivity gives actual schemes. Fineness/fs is etale local by its definition. For the universal property on Y, the test object is pulled back along the cover, and the local maps descend by the morphism clause. Thus the existence and universal properties are not simply restated as new children.

Step 10 gets the comparison s from the fine universal property and identifies its full preimage of an e-chart by the generator/unit criterion, not merely by containment of images. The algebra extension is finite because the finitely many monomials z^f span; the balanced-tensor relations prove that the same spanning set works after tensoring with A, without any flatness assumption. The cited etale/fpqc comparison and finite-descent theorem give exactly the global finiteness conclusion. I checked that lem-weil-pbc-fpqc-descend-finite applies to families, not only to a quasi-compact singleton, which matters for an arbitrary locally Noetherian Y.

Small cases: P=0 and a singleton generating set give the identity. A principal ideal E={e} likewise has Q_e=P, so both objects are Y. If 0 belongs to E, the 0-chart is all of Y and the other charts are its ordinary unit opens. For P=N^2 and E={(2,0),(0,2)}, Q_(2,0) is generated by P and (-2,2); its saturation contains (-1,1), so the finite-saturation step is substantive. The algebra is spanned after adjoining the square-root monomial, as claimed. For the standard N^2 logarithmic point over a field (both standard generators map to zero) and E={(1,0),(0,1)}, the local algebras are k[t] and k[t^{-1}], giving P^1, while K=0. This tests both the zero-generator trap and the difference from the ordinary blowup. The helper monoid statement also allows P=N direct-sum a finite abelian group; this checks the lack of a torsion-free assumption. The empty underlying scheme causes no exception; the relevant charts and descended schemes are empty. A nonempty E is required exactly where a chart generator is selected.

No proof step exceeds 2000 characters. I checked the longer universal-property and polarization arguments for hidden comparison lemmas: the arguments are written out; the non-elementary saturation, scheme gluing, affine-map representability and descent results are cited as nodes. The off-unit citations are generic tools declared in split_report.tool_uses; definitions and Mathlib/Lean-closed leaves are used as such. There is no alternative proof-unit route and no SGA citation.

## Unfinished work

The two generic children remain unsplit deliberately, as the one-level split requires. No clause of this item is left without a proof. Server validation and delivery are recorded below once the commands finish.

## Validation

The first required deliver.py --no-push exited successfully: preflight passed, receipt 3aa12fdca1. Before the final dry run I clarified the generic descent node to state explicitly the source-local form of morphism descent used in Step 5; quotations were regenerated from that exact statement. No mathematical hypothesis or conclusion of the item changed.
