# Q111 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-square-zero-picard-obstruction.json`: item, statement retained, split into six proof steps. The explicit square-zero unit calculation is a step, not a node.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-line-modules-h1.json`: one new statement-only lemma, unsplit, no Mathlib match. General ringed-site line-module classification and its change-of-ring formula. Its statement does not assert any obstruction sequence or thickening result.
- `citations.json`: one verbatim statement extract for each of the twelve proof-step citations.
- `searches.jsonl`: actual Q111 search log, retained. The item keeps its Q57 searches and records the new searches as well. The new node records precisely six Q111 queries that ran. No Lean file was written and no compiler/build tool was invoked.

## Attachments

None. Searched `lean/WeilConjectures` for the exact blueprint id and for Picard obstruction, square-zero Picard, and the Picard/cohomology notions. No project declaration states the algebraic-space obstruction lemma. The scheme Hilbert-90 and GmPicard results do not cover arbitrary algebraic spaces, and the scheme-only obstruction node is not an attachment for this item.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## What needed correction

The imported statement is faithful to Tag 0DNM and was retained verbatim. Its proof had not yet been split. The ordinary scheme version `lem-sfb-square-zero-picard-obstruction`, `thm-sc-hilbert-90`, the curve-only `lem-sc-h1-gm-pic`, and their restriction formulas cannot be applied to an arbitrary algebraic-space total space. The appropriate general line-module classification is the one new node.

I also avoided treating the small scheme-object etale site of a non-scheme algebraic space as though its final object were the space itself. For comparison of module-derived and underlying-abelian cohomology I use the already existing enlarged etale site, whose objects include the algebraic space and which has final object Z. This lets the existing general ringed-site evaluation-comparison statement apply literally. I did not introduce a new comparison lemma or silently identify cohomology with constant coefficients with structure-ring cohomology.

The inherited `blueprint.from.node` is null. `tools/blueprint_refs.py ancestor lem-sfb-space-square-zero-picard-obstruction` itself returns `None`. I kept that value, retained the long, precise `from.place` and `via` chain, and gave the new node that exact returned ancestor with this item prepended to `via`. Read the latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md` (3). This split supplies the existing Picard-stack prerequisite inside that recorded chain; it changes no chapter or unit route.

## Unfinished work

The one new general ringed-site line-module lemma is deliberately statement-only, to be split later. The item itself has a complete assembly proof. No mathematical obstruction remains for this delivery.

## Review by Q111

I read `spaces-more-morphisms.tex`, Tag 0DNM, label `lemma-picard-group-first-order-thickening`, including its displayed exact sequence and entire proof. It explicitly uses the common etale site, the map f to 1+f, the long exact sequence and the Picard/H1 identification. I also read Tag 05ZS, `lemma-thickening-equivalence`, and the surrounding first-order ring-sheaf discussion. For the new node I read `sites-cohomology.tex`, Tag 040E, `lemma-h1-invertible`, its entire frame-torsor proof, and Tag 03AJ, `lemma-torsors-h1`. I checked the difference between invertible modules and locally free rank-one modules against `sites-modules.tex`, Tag 0B8Q, `lemma-invertible-is-locally-free-rank-1`. The published 040E statement assumes a locally ringed site; the new node explicitly concerns locally free rank-one modules, for which its frame-torsor construction works on any ringed site. This avoids claiming that every tensor-invertible module is locally free on an arbitrary ringed site.

For clarity, the argument intended for the new statement-only node is as follows (this is report material, not proof text hidden in its statement). Frames of a line module form a locally trivial A-units torsor. Conversely, for such a torsor P, sheafify the associated module (P times A)/A-units; on a trivializing cover it is A, and a change of torsor frame multiplies its module frame by the same unit. These constructions are inverse up to canonical isomorphism. Tensoring local frames multiplies the transition units, so the classification is a group isomorphism. Changing A to B sends every transition unit a to phi(a). Equivalently the frame torsor is extended along A-units to B-units; the associated module is B tensor_A L. Functoriality of the torsor/H1 classification gives precisely the coefficient-change formula stated. This is a generic prerequisite, with no square-zero hypothesis and no H2 conclusion, rather than a renamed clause of the item.

I opened the statements of every node cited by the six proof steps and compared what is actually used:

1. `lem-sfb-space-first-order-ringed-description` explicitly states both the common etale-site equivalence for a first-order thickening and the exact structural quotient with square-zero quasi-coherent kernel. It supplies exactly these assertions. `lem-trf-space-enlarged-etale-ringed-site-model` supplies the canonical ringed-topos model, its module equivalences and tensor pullback, as required for the restriction convention. I do not use only a definition node as evidence of the equivalence.
2. The calculation (1+x)(1+y)=1+x+y, inverse 1-x, and the explicit lift of a unit establish the entire units short exact sequence. The only nondefinitional conversion is local surjectivity to an epimorphism, which is exactly `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`. Local lifts of both b and b-inverse are taken on a common refinement. I do not assume a quotient map is surjective on global sections or need affine intersections.
3. `lem-weil-pbc-site-sheaves-enough-injectives` is for any small site, not only schemes; it supplies the abelian category and injectives. The global-section functor is additive and preserves kernels by its compatible-family definition. `lem-weil-pbc-right-derived-universal-delta-functor` explicitly states canonical connecting maps and exactness for every short exact sequence; I read `derived.tex`, Tag 015B, `lemma-higher-derived-functors` (4), as well. Its hypotheses are therefore satisfied for the units sequence. No H1 torsor comparison has been used yet.
4. The new node states the group isomorphisms and, separately and explicitly, their compatibility with a ring-sheaf map on the same site. Applying it to A to B is legitimate after step 1. The two existing site-model nodes identify the ordinary restriction with B tensor_A L on that site. Thus the map in the long exact sequence corresponds to the actual tensor pullback j-star, with the same coefficients and the same line-module convention as the item's statement. It is not sufficient merely to know an abstract isomorphism between the two Picard groups and H1; this is why the change-of-ring clause is explicit in the new node.
5. I read `sites-cohomology.tex`, Tag 03FD, `lemma-cohomology-modules-abelian-agree`, including its statement and proof, and the definition of global sections on a site without a final object in Tag 01FT. `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` requires an object U and enough injective module sheaves. I apply it on the enlarged site at its actual terminal object Z. `lem-trf-space-enlarged-etale-ringed-site-model` states the equivalences of both sheaf topoi and module categories; their section-preserving nature follows by evaluating the terminal sheaf. `lem-pur-ringed-site-grothendieck-abelian` and `lem-sp-grothendieck-enough-injectives` establish the missing module-injective hypothesis on this small ringed site. An additive equivalence preserves exact sequences and injectivity (the lifting property transports by its inverse), so applying it to the resolution preserves the section complex. Hence the existing evaluation comparison says exactly what is needed for H2 on the original site, not merely for constant-ring sheaves on a scheme.
6. The final step defines delta as the composite of the three canonical homomorphisms already constructed. Exactness transports across the two isomorphisms. If H2 is zero, equality of Picard classes is precisely existence of a restriction isomorphism; this can be included as part of the lifting datum. The elementary step makes no claim of unique extension or unique restriction isomorphism.

I checked small cases. If J=0, A to B is an isomorphism and the obstruction is zero, agreeing with Picard restriction being an isomorphism. For the empty algebraic space all the groups are trivial. Over k[epsilon]/epsilon-squared to k, units lift by c(1-x) and the elementary kernel is the additive epsilon-ideal in every characteristic, including characteristic 2. For the new node, on the one-object site a line module means actually free rank one, so its Pic-line group and H1 of units are both zero; it does not falsely identify the ordinary ring Picard group with this group. On general sites a local frame remains a local frame after arbitrary extension of scalars, without flatness. The zero ring sheaf also gives trivial frame/line classification. I checked that no proof step invokes Noetherianity, properness, finite-dimensionality or representability of Z by a scheme.

I checked delivery-errors B through E explicitly: all objects and coefficient conventions are introduced, the new node is statement-only, source places use Stacks tags and TeX labels, actual search queries are logged, the unit calculation stays a step, the new node is neither an obstruction-sequence clause nor a duplicate, and every non-elementary assertion has a node whose statement supplies it. The longest proof step is under 900 characters, so none reaches the 2000-character hidden-lemma review threshold. Dependency traversal found no path from any cited substantive site/cohomology node back to the item. `citations.json` copies literal statement text and was checked against each node. The generic off-unit tools are declared in `split_report.tool_uses`; no unit or chapter file was changed.

The Q111 searches ran with leanfinder, Loogle, grep and LeanSearch, with a second semantic phrasing for both the item and the new node. I read the hits rather than treating the names as matches. Loogle's `Submodule.mulExact_unitsToPic_mapAlgebra` is a statement about Picard groups of rings and an algebra extension, not the H2 obstruction for a thickening or the line-module classification on a site. LeanFinder's H1Cotangent hits concern cotangent modules, not sheaf cohomology. I opened `Mathlib/RingTheory/PicardGroup.lean` (the TODO explicitly leaves the sheaf-cohomology comparison), `Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean` (fixed-family cocycles, sheaf H1 and the required comparison still TODO), and `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` (defines abelian cohomology, not the line classification). Free-sheaf/unit-Hom equivalences do not state the classification either. No new Mathlib leaf is justified by these results.

## Not duplicates

`lem-sfb-square-zero-picard-obstruction` is the scheme/Zariski theorem, not the algebraic-space/etale statement of the item. `thm-sc-hilbert-90` applies to schemes, and `lem-sc-h1-gm-pic` to curves; neither gives the general ringed-site prerequisite for a non-schematic algebraic space. General module/abelian comparison is already present and is cited instead of being created again.

The following comparisons include every existing node sharing either source tag 040E or 03AJ with the new node. Sharing a source's torsor discussion does not make a statement about relative extensions, a curve, or a generator-coordinate formula a classification of all line modules on a ringed site.

lem-sfb-ringed-site-line-modules-h1 vs def-amb-relative-etale-cohomology: the existing node defines Resolution model of relative etale cohomology and its cone maps; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-amb-torsor-with-section: the existing node defines Torsors with a specified section and their isomorphism classes; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-abelian-realization: the existing node defines Exact abelian realization from the supported integral generator; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-etale-hom: the existing node defines Canonical finite supported Ext to derived Hom realization; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-forget-support: the existing node defines Canonical forget-support maps for normalized finite realizations; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-integral-extension: the existing node defines Normalized integral extension of a framed line bundle; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-pro-predicate: the existing node defines Normalized supported-Hom predicate for the pro-etale realization; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-pro-realization: the existing node defines Normalized supported pro-etale realization of an integral extension; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-realization-additive: the existing node defines Additivity predicate for integral supported realizations; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-realization-enlarge: the existing node defines Support enlargement predicate for framed supported realizations; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-realization-iso: the existing node defines Invariance predicate for framed supported realizations; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-realization-property: the existing node defines Integral realization and positive forget-support predicate; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-realization-pullback: the existing node defines Etale pullback predicate for framed supported realizations; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-scalar-maps: the existing node defines Roots coefficient Yoneda splice of an integral supported class; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-scalar-realization: the existing node defines Unique finite scalar realization of an integral framed extension; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-framed-transport: the existing node defines Canonical transport of complementary frames and positive ordinary Kummer image; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-pur-principal-torsor-sign-types: the existing node defines Principal torsor localization comparison interfaces; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs def-sc-torsor-extension-presentation: the existing node defines Canonical extension presentation of an etale torsor; it does not assert an isomorphism between arbitrary ringed-site line modules and derived H1 of units. The new node asserts that isomorphism and its coefficient-change formula.

lem-sfb-ringed-site-line-modules-h1 vs lem-amb-framed-lifts-classification: the existing statement classifies pointed lifting torsors for a given short exact sequence with terminal object T; the new statement classifies all line modules by absolute H1 of units, with no final object required.

lem-sfb-ringed-site-line-modules-h1 vs lem-amb-relative-cocycle-coordinates: the existing result concerns Concrete first homology coordinates for the relative restriction cone; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-amb-relative-torsor-class-naturality: the existing result concerns Equivariant naturality of framed relative torsor classes; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-amb-relative-torsor-cohomology: the existing result concerns Relative first cohomology and torsors with a specified open section; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-amb-relative-torsor-forget-normalization: the existing result concerns Ordinary normalization of the framed relative cocycle; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-pur-cartier-pair-tensor-addition: the existing result concerns Tensor addition of framed Cartier pairs before applying Kummer; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-pur-divisor-torsor-boundary-signs: the existing result concerns Relative torsor representatives and the two boundary signs; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-pur-principal-torsor-connecting-comparison: the existing result concerns Supported-Hom comparison and coefficient Yoneda connecting; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-pur-principal-torsor-framed-comparison: the existing result concerns Framed extension pushout and signed relative cocycle; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-pur-principal-torsor-normalized-comparison: the existing result concerns Normalized open and supported-Hom comparisons; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-pur-principal-torsor-normalized-natural: the existing result concerns Naturality of normalized supported-Hom comparisons; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-pur-principal-torsor-yoneda-sign: the existing result concerns A globally framed relative torsor gives the inverse-section pushout; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-pur-relative-extension-cohomology-normalization: the existing result concerns Relative torsor extension and Ext-normalized supported cohomology; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-contracted-product-exists: the existing result concerns Existence of the contracted product of an etale torsor; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-contracted-product-exists-data: the existing result concerns Translation torsor structure on the explicit sheafified orbit quotient; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-contracted-product-exists-universal: the existing result concerns Universal property of the explicit sheafified orbit quotient; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-generators-pullback-equivariant: the existing statement gives a particular scheme-module generator/pullback compatibility formula; the new statement is the full classification by derived H1 on any small ringed site, with change of its structural ring sheaf.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-generators-pullback-map-unit-formula: the existing statement gives a particular scheme-module generator/pullback compatibility formula; the new statement is the full classification by derived H1 on any small ringed site, with change of its structural ring sheaf.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-generators-pullback-section: the existing statement gives a particular scheme-module generator/pullback compatibility formula; the new statement is the full classification by derived H1 on any small ringed site, with change of its structural ring sheaf.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-generators-pullback-sections-natural: the existing statement gives a particular scheme-module generator/pullback compatibility formula; the new statement is the full classification by derived H1 on any small ringed site, with change of its structural ring sheaf.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-generators-pullback-source-comparison: the existing statement gives a particular scheme-module generator/pullback compatibility formula; the new statement is the full classification by derived H1 on any small ringed site, with change of its structural ring sheaf.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-generators-pullback-target-comparison: the existing statement gives a particular scheme-module generator/pullback compatibility formula; the new statement is the full classification by derived H1 on any small ringed site, with change of its structural ring sheaf.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-generators-pullback-unit-map: the existing statement gives a particular scheme-module generator/pullback compatibility formula; the new statement is the full classification by derived H1 on any small ringed site, with change of its structural ring sheaf.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-inverse-image-lifting-torsor: the existing result concerns Inverse image of a lifting torsor; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-inverse-image-lifts-fibre: the existing result concerns Underlying lifting-fibre comparison for etale inverse image; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-torsor-h1-functoriality: the existing result concerns Functoriality of the etale torsor classification of H1; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-torsor-inverse-image-extension: the existing result concerns Inverse image of the torsor extension; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-etale-torsor-pushout-extension: the existing result concerns Pushout of the etale torsor extension; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-extension-presentation-generator-fibre: the existing result concerns Generators identify the fibre; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-extension-presentation-short-exact: the existing result concerns Short exactness of extension presentation; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-h1-gm-pic: the existing statement is restricted to curves and their scheme morphisms; the new statement classifies line modules over an arbitrary commutative ring sheaf on any small site and gives coefficient change on that site.

lem-sfb-ringed-site-line-modules-h1 vs lem-sc-h1-gm-pic-pullback: the existing statement is restricted to curves and their scheme morphisms; the new statement classifies line modules over an arbitrary commutative ring sheaf on any small site and gives coefficient change on that site.

lem-sfb-ringed-site-line-modules-h1 vs lem-sp-etale-torsor-extension-presentation-exists: the existing result concerns Existence of the free extension presentation of an etale torsor; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-sp-relative-torsor-extension: the existing result concerns Relative extension class of a torsor with a specified section; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-weil-pbc-finite-etale-equivalence-h1: the existing result concerns Finite etale pullback equivalence implies finite constant H1 comparison; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs lem-weil-pbc-gabber-h1-absolutely-algebraically-closed: the existing result concerns First constant cohomology vanishes on closed subschemes of the spectrum of a normal domain with separably closed fraction field (Stacks 09ZB); its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs new-etale-torsor-inverse-image-extension-core: the existing result concerns Extension core after inverse-image torsor transport; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

lem-sfb-ringed-site-line-modules-h1 vs new-etale-torsor-inverse-image-torsor: the existing result concerns Inverse-image torsor and equivariance; its torsor/extension/cohomology assertion does not classify line modules over arbitrary ring sheaves. The new node gives that absolute classification with coefficient change and without a scheme hypothesis.

