## Worker report

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-top-intersection-pullback.json`: item, split, no Mathlib match.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-invertible-coherent-euler-projection.json`: statement-only, unsplit, no Mathlib match.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-equal-dimension-generic-structure-image.json`: statement-only, unsplit, no Mathlib match.
   - `citations.json`: one verbatim statement quotation for each use in each proof step.
2. Attachments: none. Searched `lean/WeilConjectures/` for the blueprint tag, intersectionNumber/intersection_number/topSelfIntersection, Euler-characteristic and projection/generic-image terminology. No declaration supplies the item or either new supporting statement. Curve-specific finite-pushforward results do not treat arbitrary dimensions or nonfinite maps.
3. WANTED: none. All mathematics used is in the local Stacks sources.
4. No mathematical statement correction. The source's proof contains a typographical `$R^if_*\mathcal O_X$` in its generic-vanishing sentence, although its morphism is named $f:Y\to X$; the argument and the surrounding equations concern $\mathcal O_Z$. Here $Z$ is the whole source, so it is written unambiguously as $R^if_*\mathcal O_X$ with OUR convention $f:X\to Y$.
5. Nothing unfinished in this one-level split. The two new nodes are intentionally unsplit, with empty proof and proof_deps, for subsequent stage-1 work. No Mathlib leaves. No Lean written, no compiler or build invoked.

Read the existing Q58 searches.jsonl before reusing its actual results. Added searches only where the new generic-image and twisted-Euler questions needed refinement. The Mathlib function-field hits at FunctionField.lean:81–82 and :164 identify stalk-to-field algebras and fraction fields; their types do not identify the direct-image stalk, prove finite generic degree, or give higher-image vanishing. Pushforward, pushforwardComp and pullbackPushforwardAdjunction hits only give underived functors and adjunctions. Neither is an exact match or one-line specialization. The two alternative semantic phrasings for each new lemma likewise give no match. All recorded tool/query pairs are in searches.jsonl.

Blueprint/DAG searches: ran blueprint_refs.py ancestor for the item (reports inherited from.node=None), and whole-blueprint searches for intersection, euler-characteristic-morphism, generic direct image, projection-formula, generically-finite, higher direct image, function-field degree, euler projection, generic structure, Euler–Leray. Grepped all dag/nodes for 0BET, 0BEK, 01E8, 02NW, 01Y6, 0A21 and the numerical-polynomial labels, as well as statements about generic rank, proper closed subsets and Euler–Leray. The existing numerical-polynomial and Euler-additive nodes were read and reused where applicable. No blueprint node states the two new facts. The original blueprint.from.node=None is inherited through the long created-item chain; it is not invented or replaced by a different ancestor. The precise added from.place identifies the corresponding paragraph of 0BET. Read the current latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md; this is the existing auxiliary Milne degree-polynomial branch, not a replacement of the unit's route. The item is not a unit key statement; no unit record was changed.

## Review by Q58

I read varieties.tex, Tag 0BET, label lemma-intersection-number-and-pullback, including the coefficient argument, both dimension branches, and the last leading-term congruence. The item is exactly its Z=source, equal-line-bundle specialization, with both source and target nonempty proper integral varieties of dimension g>=1. The source allows arbitrary morphisms of proper schemes, rather than only finite maps. The imported statement already records this distinction correctly, and I kept it. I also read the chapter and unit records, the three blueprint levels in SETUP.md, and delivery-errors B–E in full.

For the first new node I read varieties.tex 0BEK, lemma-euler-characteristic-morphism, whose proof explicitly justifies coherence and the finite sum via proper coherent direct image, as well as cohomology.tex 01E8, lemma-projection-formula. In 01E8 an invertible module is finite locally free of rank one; the isomorphism commutes tensor by that module through every higher direct image. Substituting this in 0BEK gives exactly the displayed twisted Euler identity. Finite type over the field and properness ensure the Noetherian/coherent finiteness hypotheses. This node is a cohomological input for arbitrary coherent F and arbitrary invertible M, with neither intersections nor a dominance alternative in its conclusion. It therefore does not move a clause of the item into a renamed lemma.

For the second new node I read varieties.tex 0A21, lemma-dimension-locally-algebraic (in particular dimension equals transcendence degree and the dimension formula), morphisms.tex 02NW, lemma-generically-finite (1)<->(4), and coherent.tex 01Y6, lemma-finite-pushforward-coherent. Equal dimension forces transcendence degree zero in the actual generic field extension; finite type makes the algebraic extension finite. Over the generic point, any source point must have residue transcendence degree at least g, so the dimension formula forces it to be the generic point of the integral source. The fibre is thus a singleton, and the qcqs proper morphism meets 02NW's hypotheses, giving finiteness on an open containing eta_Y. On that open the generic section algebra is k(X); its k(Y) action is the pullback-of-germs action, not an arbitrary embedding. 01Y6 gives vanishing of positive higher images there; restriction identifies them with the restrictions of the original higher images. The node states this generic calculation, not any equality of intersection numbers. Its g=0 case is included and valid, although the item itself assumes g>=1.

Step 1 uses the statement of lemma-nagata-proper-to-separated-target to obtain properness from the given triangle (the target is separated because it is proper). It then uses exactly the coherence, finite-sum and twisted-Euler conclusion of the first new node with F=O_X. def-sc-invertible-module gives the local rank-one trivializations and inverses; def-pc-module-pullback supplies the ordinary tensor pullback. The canonical comparison between pullback of products and products of pullbacks is checked on each trivialization, where it is the identity; these canonical maps glue. This local argument also checks coherence and invertibility of all powers, including zero and negative exponents. No finite-morphism hypothesis is silently introduced.

Step 2 uses properness only for closedness of the image (in the universally-closed definition), and lem-pc-higher-direct-image-open-restriction really asserts restriction for every p and every module, with no affine or quasi-coherence hypothesis. Restricting to the complement of the image means an empty source, so every higher image is zero there. For any proper closed subset of the integral dimension-g target, appending Y to a chain increases its length by one; the inequality is directly the cited definition of Krull dimension, not a hidden dimension-theory lemma. lem-sc-snapper-numerical-polynomial explicitly bounds total degree by the support dimension for arbitrary coherent modules and arbitrary invertible entries. The finitely many zero summands are discarded. Coefficient extraction is precisely def-sc-intersection-number. This gives the zero case without a projectivity or ampleness assumption.

Step 3 uses every part of the second new node it needs: finite generic extension, nonempty open on which positive higher images vanish, and the scalar-compatible generic stalk. The original proper map satisfies its hypotheses by step 1. The same chain argument bounds the support of each positive higher image by g-1; Snapper then removes their degree-g coefficients. There is no assumption that the whole morphism is finite. All uses refer to statements, rather than arguments hidden in cited proofs.

Step 4 uses lem-sc-numerical-polynomial-leading-term with F=f_*O_X on the proper target Y. Its sole support component is Y because the generic stalk is nonzero and coherent support is closed; the local finite-generation argument for that closedness is written explicitly. The integral generic local ring is k(Y) by def-sc-function-field. A basis filtration shows directly that length over this field is its vector-space dimension e, avoiding an extra length theorem. The cited leading-term statement gives exactly the difference of Euler polynomials of degree <g, with this generic multiplicity. The two intersection coefficients are precisely the definition's identity closed-immersion cases. No comparison between unrelated cohomology or coefficient categories is used.

I tested identity maps (e=1), finite maps of P^1 of degree n (including Frobenius in characteristic p, so the full inseparable degree is required), a constant map to a rational point (g>0 gives total degree zero), a birational blowup of a proper surface (e=1 although the map need not be finite), a trivial invertible module (all top coefficients zero), and g=1 where the lower-degree terms are constants. For the new Euler node, the zero sheaf and identity map give the expected equality; a positive-dimensional proper structure morphism shows why the higher direct images cannot simply be discarded. For the generic-image node, g=0 reduces to finite field extensions; a birational nonfinite map confirms that only an open-finiteness conclusion is asserted. Non-algebraically-closed fields and inseparability cause no change in either source argument.

Against B–E: new statements introduce all objects and cite their actual definition nodes, use ordinary single-escaped TeX in parsed JSON, and carry sources by Stacks tag and label. New nodes have no proof sketch in the statement or proof fields. Existing generalizations were reused; the distinct same-tag statements are compared below. No new node duplicates an item clause, no cycle is intentionally introduced, and proof_deps equals the union of uses. All four non-elementary steps are under 2000 characters and their cohomological/polynomial inputs are explicit cited statements. I corrected my initial plan after finding lem-pc-euler-additive: its untwisted Euler–Leray clause is already present, while the new input is the line-bundle-twisted identity using the not-yet-present higher projection formula.

Off-unit tools are declared in split_report.tool_uses: Snapper's polynomial degree bound, the generic-multiplicity leading-term formula, and open restriction of module higher direct images. These are generic coherent-cohomology tools used on this inherited supporting branch; none replaces a step of the six-functor stability unit. The proper-to-separated node is already a Mathlib leaf and the definitions merely give notions.

## Not duplicates

- lem-sfb-invertible-coherent-euler-projection vs lem-pc-euler-additive: the existing statement gives untwisted Euler–Leray and short-exact additivity; the new input requires the higher projection formula for an arbitrary invertible twist.

- lem-sfb-invertible-coherent-euler-projection vs lem-sc-finite-locally-free-tensor-unit: the existing statement concerns Finite locally free tensor-pullback unit; it does not assert the twisted Euler–Leray identity for an arbitrary morphism of proper schemes and coherent source module.

- lem-sfb-invertible-coherent-euler-projection vs lem-sc-picard-pullback-base-change: the existing statement concerns Canonical base change for a pullback presentation; it does not assert the twisted Euler–Leray identity for an arbitrary morphism of proper schemes and coherent source module.

- lem-sfb-invertible-coherent-euler-projection vs lem-sc-picard-pullback-evaluation: the existing statement concerns Universal ranks and evaluation for a module pulled back from the base; it does not assert the twisted Euler–Leray identity for an arbitrary morphism of proper schemes and coherent source module.

- lem-sfb-invertible-coherent-euler-projection vs lem-sc-picard-pullback-local-ranks: the existing statement concerns Common local ranks of a pullback presentation; it does not assert the twisted Euler–Leray identity for an arbitrary morphism of proper schemes and coherent source module.

- lem-sfb-invertible-coherent-euler-projection vs lem-sc-tensor-unit-open-localization: the existing statement concerns Open localization of the tensor-pullback unit; it does not assert the twisted Euler–Leray identity for an arbitrary morphism of proper schemes and coherent source module.

- lem-sfb-invertible-coherent-euler-projection vs lem-sfb-finite-map-locally-free-euler-comparison: the existing theorem assumes a finite morphism and has no positive higher-image terms; the new node allows arbitrary morphisms of proper schemes.

- lem-sfb-invertible-coherent-euler-projection vs lem-trf-finite-ideal-twist-cohomology-comparison: the existing statement concerns Finite ideal products: coherence and twisted cohomology comparison; it does not assert the twisted Euler–Leray identity for an arbitrary morphism of proper schemes and coherent source module.

- lem-sfb-equal-dimension-generic-structure-image vs lem-pc-f3-finite-pushforward-finite-type: the existing statement concerns Finite pushforward preserves quasi-coherence and finite type without Noetherian assumptions; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-pc-m1-projective-affine-finite-cohomology-independent: the existing statement concerns Finite projective cohomology over an arbitrary affine Noetherian base; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-pc-p2-projective-finite-source-cohomology-segment: the existing statement concerns Finite-source exact cohomology segment for a projective embedding; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-per-normal-surface-exceptional-curves: the existing statement concerns Finite exceptional-curve data for a normal excellent surface modification; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sbc-cohen-macaulay-fibre-dimension-decomposition: the existing statement concerns Open dimension partition of a fibre Cohen-Macaulay open; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood: the existing statement concerns Constant local fibre dimension near one Cohen-Macaulay fibre stalk; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sbc-cohen-macaulay-flat-quasi-finite-chart: the existing statement concerns Flat quasi-finite chart near a Cohen-Macaulay fibre point; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sbc-equidimensional-open-local-dimension: the existing statement concerns Local dimension of a pure-dimensional locally algebraic open; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sc-closed-irreducible-dimension-trdeg: the existing statement concerns Dimension of an irreducible closed subset from its generic residue field; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sc-curve-base-change-relative-dimension-one: the existing statement concerns Base changes of a smooth curve are smooth of relative dimension $1$; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sc-dimension-locally-algebraic: the existing statement concerns Dimension of an irreducible locally algebraic scheme over a field; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sc-finite-type-nonclosed-closure-closed-points: the existing statement concerns Nonclosed points in finite-type schemes have infinitely many closed specializations; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sc-integral-locally-algebraic-affine-opens-dimension: the existing statement concerns Nonempty affine opens of an integral locally algebraic scheme have equal dimension; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sc-integral-locally-algebraic-opens-dimension: the existing statement concerns Nonempty opens of an integral locally algebraic scheme have its dimension; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sc-positive-dimensional-locally-algebraic-closed-points: the existing statement concerns Positive-dimensional locally algebraic closed subsets have infinitely many closed points; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sfb-curve-closed-point-affine-local-model: the existing statement concerns Affine local model at a closed point of a curve; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sfb-projective-generic-map-graph-alteration: the existing statement concerns Reduced graph closure extending a projective generic map; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sfb-projective-source-alteration-criterion: the existing statement concerns Projective source and finite function field give an alteration; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sfb-proper-generic-radicial-etale-factorization: the existing theorem assumes a finite function-field extension and supplies a radicial-etale factorization; it does not assert the structure-image generic stalk or higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sfb-separable-curve-geometric-local-data: the existing statement concerns Affine geometric stalks at a separable closed point; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-sfb-syntomic-fixed-dimension-locus: the existing statement concerns Universal syntomic locus of a fixed relative dimension; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-trf-etale-cover-field-curve-nodality: the existing statement concerns Etale covers of locally algebraic schemes: dimension and nodal singularities; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-trf-field-extension-component-local-dimension: the existing statement concerns Component dimensions after a field extension from local dimensions; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-trf-finite-normalization-quotient-local-criterion: the existing statement concerns Finite reduced normalization: coherent quotient and local normality criterion; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-trf-generic-completed-differential-rank: the existing statement concerns Generic ranks of completed differentials over reduced equidimensional algebras; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-trf-geometric-pure-fibre-point-dimension: the existing statement concerns Pure geometric fibres give the ordinary pointwise fibre dimension; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-weil-pbc-affine-line-dense-open-finite-complement: the existing statement concerns Dense affine shrinking makes the boundary of a relative affine line finite; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-weil-pbc-dense-open-dimension-comparison: the existing statement concerns A dense open in a finite type scheme over a field has full dimension; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-weil-pbc-finite-pushforward-coherent: the existing statement concerns The direct image of a coherent module along a finite morphism to a locally Noetherian scheme is coherent; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-weil-pbc-finite-structure-unit-quotient-system: the existing statement concerns Compatible reduced units through a coherent proper supporting quotient; it does not give the equal-dimensional proper-map generic structure-image calculation and higher-image vanishing.

- lem-sfb-equal-dimension-generic-structure-image vs lem-weil-pbc-generic-finite-morphism-open-neighborhood: the existing theorem assumes finite generic fibres and concludes open-finiteness only; the new node derives generic finiteness from equal dimension and identifies the generic structure-image stalk and positive higher-image vanishing.
