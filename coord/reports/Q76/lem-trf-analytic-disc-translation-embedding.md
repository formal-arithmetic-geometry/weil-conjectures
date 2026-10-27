# Stage-1 report: lem-trf-analytic-disc-translation-embedding

## Files written

- dag/nodes/sec-trace-formula/lem-trf-analytic-disc-translation-embedding.json: statement, split; no Mathlib match for the complete translation construction. Its statement and inherited metadata are retained.
- dag/nodes/sec-trace-formula/lem-trf-weighted-disc-banach.json: new statement-only analytic input, unsplit; no Mathlib match for completeness in the weighted Gauss norm at arbitrary positive real radius.
- citations.json: verbatim statements backing every proof-step citation.
- searches.jsonl: actual msearch queries and returned search digests. Queries and results are recorded in the nodes; none is invented.

## Attachments

None. Searches for the item tag and for TateAlgebra, disc algebra, type four, GaussNorm and weighted series in lean/WeilConjectures found no declaration stating this item or the new input. No Lean was written or compiled.

## Wanted literature

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, Section 6.2, printed p.45, the disc description immediately before Lemma 6.2.8, for lem-trf-analytic-disc-translation-embedding and lem-trf-weighted-disc-banach. The named local PDF is absent. I read the primary PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (arXiv:0707.3953v3); I downloaded no file. The split is marked proof_origin.by = agent: it proves the first-factor embedding directly, instead of importing the completed-tensor-product assertion as an unproved black box.

## Findings and scope

The imported item had no proof. Its statement is correct; no STATEMENT-DISPUTED correction is needed. The analytic part does not require a residue-characteristic assumption. The radius is an arbitrary positive real number, and it must not silently be assumed to lie in the value group. We use neither a unit-radius coordinate rescaling nor multiplicativity of the Gauss norm. Submultiplicativity and the constant-coefficient lower bound suffice.

The chapter and unit records and their current latest blueprint texts were read, as were the latest ancestor lem-trf-local-term-locality and its proof. This item is a supporting input already below the inherited nearby-cycle/semistable-modification route. This delivery changes no chapter or unit route and is not the unit's key node, so no unit record is changed. All cited existing statements are either Mathlib leaves or the new input in the same unit.

## Not duplicates

lem-trf-weighted-disc-banach vs lem-trf-restricted-series-gauss-completion: the existing statement covers unweighted restricted coefficient families in finitely many variables, hence radius one; the new statement covers a single variable with the weights s^n for every real s>0, including radii outside the value group. The former does not specialize to the latter by rescaling over F in general.

lem-trf-weighted-disc-banach vs lem-trf-tate-gauss-multiplicative: the existing statement asserts multiplicativity in unit-radius restricted series and does not assert completeness; the new input asserts a complete submultiplicative norm at arbitrary positive radius and does not claim multiplicativity.

lem-trf-weighted-disc-banach vs lem-trf-analytic-disc-translation-embedding: the new lemma is a generic coefficient-space Banach fact for one field and one positive real weight. It constructs no field embedding, mentions no z, and needs neither an algebraically closed subfield nor unattained distances. The item's substantive argument remains in its polynomial, inverse, fraction, density and multiplicativity steps.

lem-trf-weighted-disc-banach vs lem-sfb-weighted-taylor-banach-model: the latter is the complex l1 algebra of convergent analytic germs, whereas the new input uses a nonarchimedean supremum norm and weighted null coefficients. They have different scalar and convergence hypotheses.

The whole DAG was searched by title, statement and analytic keywords; blueprint_refs searches for Gauss, completion, disc algebra, restricted series, weighted, Banach and linear factors gave no blueprint duplicate of the new input. The existing linear-factorization, geometric-inverse and dense-extension leaves are reused. No Stacks tag is claimed for an analytic theorem; the source here is Temkin, not SGA.

## Review by Q76

I checked sections B through E of delivery-errors.md against the actual statements, not merely against dependency names. I read Temkin's printed p.45 disc-algebra paragraphs and the preceding discussion of the unattained-radius field. They describe the scalar-extended algebra with coordinate w = z tensor 1 minus 1 tensor z. For l=K and the identity embedding, its first-factor coordinate is therefore z+W. I expanded that input directly; this avoids needing a separate universal theorem about a completed tensor product. The new node's source is this disc algebra paragraph, but its explicit coefficient-space formulation is my analytic expansion, identified as such in its source.

Step 1 takes precisely completeness, the norm inequalities, constant scalar norms, the W norm and the constant-coefficient contraction from lem-trf-weighted-disc-banach. Its hypotheses apply because K is complete, nonarchimedean and r>0. Restricting the constant K scalar action to k preserves the normed-vector-space property. The new node introduces F, s, the series, operations, norm and metric itself; it contains no proof sketch or hidden existence claim.

Step 2 uses exactly the statement of lem-weil-alg-closed-linear-factorization. I opened that node and checked its existing Mathlib match against IsAlgClosed at FieldTheory/IsAlgClosed/Basic.lean:62 and Polynomial.Splits.eq_prod_roots at Algebra/Polynomial/Splits.lean:299. Algebraic closedness gives every root in k, while z outside k ensures that no evaluated linear factor vanishes. The factorization includes nonzero constants through the empty product. The upper norm bound is a finite product inequality, and the lower bound is the coefficient at W^0. No norm-multiplicativity theorem has been slipped into the argument.

Step 3 uses the actual geometric-series convergence and two-sided inverse clause of lem-trf-complete-normed-ring-geometric-inverse. I read its statement and Mathlib/Analysis/SpecificLimits/Normed.lean:275-351, including the complete-space instance, Units.oneSub and hasSum_geom_series_inverse. The element is h=-W/(z-c), whose norm is strictly less than one by the hypothesis |z-c|>r. The inverse bound is proved in the step by finite ultrametric sums and convergence, rather than attributed to a statement that does not give it. The denominator's factorization and product bound have already been established in step 2 and step 1.

Step 4 cites no extra fact: it writes the fraction construction, checks presentation independence by cross multiplication and injective polynomial evaluation, and proves its isometry with the upper inverse bound and the constant-coefficient map. This is a finite ring calculation from the preceding steps; it does not invoke an unstated localization theorem or assume that the disc ring is a field.

Step 5 uses exactly lem-sfb-dense-subspace-contractive-extension. I read its statement and LinearMap.extendOfNorm, extendOfNorm_eq, norm_extendOfNorm_apply_le and extendOfNorm_unique in Mathlib/Analysis/Normed/Operator/Extend.lean:180-214. The scalar field is k, the ambient space is K, the dense linear subspace is k(z), and the target is the complete normed k-vector space from step 1. Density is an explicit item hypothesis and contraction is proved in step 4; no finite-dimensional hypothesis is used.

Step 6 checks multiplication after extension using explicit approximating sequences and submultiplicative estimates on both sides. It also proves norm preservation by the reverse triangle inequality. This is an elementary continuity calculation from the norms already supplied, with no implicit comparison lemma. I checked that boundedness of the two approximating sequences follows from their convergence, that products converge, and that uniqueness of limits applies to the actual norm metric. All steps are under 2000 characters; none hides a long auxiliary argument.

For the new input I tested zero series, constants, W, s=1, s less than or greater than one, trivially valued fields and positive s outside the value group. Its coefficient statement remains meaningful in each case. An intended future proof is as follows (this is report material only; the new node stays statement-only). A norm-Cauchy sequence has coefficient limits because each coefficient difference is bounded by the Gauss difference divided by s^n. For each fixed epsilon, choose one approximating series at Gauss distance less than epsilon/2; take coefficient limits in that inequality. Its weighted tails then bound the weighted tail of the limit by epsilon, proving restrictedness and uniform Gauss convergence. For products, write A_i=|a_i|s^i and B_j=|b_j|s^j. Each convolution coefficient, weighted by s^n, is bounded by max_{i+j=n} A_i B_j. Boundedness of A and B proves submultiplicativity; outside the sum of their two finite exceptional index sets at threshold epsilon/max(1,||f||,||g||), every term is smaller than epsilon. This proves restrictedness. Scalar norms, the unit, constant coefficient and the variable norm follow immediately from their coefficient formulas. No normalization of s by a scalar of F occurs.

I ran the new input's searches with its id and precise scope fixed, using both semantic phrasings, Loogle and Mathlib grep. The hits PowerSeries.IsRestricted and its subring supply the predicate and algebraic closure under multiplication, but the read Restricted.lean files contain no Gauss-norm completeness. PowerSeries.WithPiTopology.instCompleteSpace at PiTopology.lean:266 concerns product topology and cannot supply this norm completeness. PowerSeries.gaussNorm and its inequalities were read in full; they also do not supply the new node. The item searches returned LaurentSeries adic completions and field-completion embeddings, which have different valuation or target hypotheses. I read the search results and retained the old item's earlier search records.

No unfinished part of the item's proof remains beyond the explicitly stated new analytic input, which is queued unsplit as required for a one-level split. There are no attachments, no Lean changes, and no new Mathlib leaves.
