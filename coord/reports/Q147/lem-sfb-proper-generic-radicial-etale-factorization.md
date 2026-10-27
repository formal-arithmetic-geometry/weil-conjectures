# Stage 1 delivery: lem-sfb-proper-generic-radicial-etale-factorization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-generic-radicial-etale-factorization.json: statement, split into seven steps; Mathlib has ingredients but no matching whole theorem.
- citations.json: one verbatim statement quotation for every citation in every proof step.
- report.md and searches.jsonl: this report and the actual search log.

No new nodes; no new Mathlib leaves. The intermediate polynomial model, primitive element, minimal-polynomial quotient, power basis, finite-open theorem, and radicial spreading already exist. No definition, Lean source, unit, or repository file was written.

## Attachments

None for the item. Searches for its blueprint tag and for generic/radicial/etale factorization in lean/WeilConjectures found no declaration stating all clauses. The existing localized-polynomial declaration AlgebraicGeometry.exists_localized_separable_polynomial_model belongs to lem-weil-pbc-localized-separable-polynomial-model; it is reused through that existing node, not recreated. Its source was read, including the exact conclusion: it supplies the polynomial and Bezout identity, not the embedding of its quotient into B or the desired function field. Those are proved in Step 5.

## WANTED

None. Sources needed for the assembly are locally available.

## Corrections and statement scope

The mathematical assertion is unchanged. The imported reference def-sc-function-field defines a function field for curves, whereas X and S here can have any dimension. The item now cites the existing def-sfb-dominant-function-field-map, which explicitly defines the canonical generic stalk algebra for arbitrary integral schemes. This repairs a reference-scope error, not a hypothesis or a conclusion. No STATEMENT-DISPUTED mathematical claim was found.

The source field initially listed 00GQ, 0BR5 and 01S2 as the historical spreading references. I checked their labels: 0BR5 and 01S2 are sections; the actual spreading input is the existing node, whose assertion includes all necessary hypotheses and the universal-homeomorphism conclusion. The proof-step source now names the specific criterion tags 01S4 and 04DF. No SGA source is used.

## Not duplicates

There are no new nodes. Whole-DAG searches by 02NW, 030K, 030N, 00UB, 00UC, 00GQ, 0BR5, 01S2 and by function-field, polynomial-model, finite-open and inseparable-spreading terminology found the existing inputs now cited. Whole-blueprint searches for generically finite, generic fibre, finite separable, separable polynomial, radicial, monic, and 02NW found no exact replacement for the item. The blueprint ancestor tool reports None, as already recorded in the item: its created.item chain reaches the imported direct-image proof through a created unit realization with no blueprint id. I retained that provenance and its exact det-thm-sf-ctf-stability-direct-images proof-(3) place, and read the current main-20261015 direct-image proof (3), the chapter and unit records. No new provenance chain is introduced.

## Search results

All four required search modes were actually run through batch2/msearch.py. The log records successful responses. LeanFinder returned universally-closed finite global sections, normalization and rational-map results, none of which gives the conclusion. LeanSearch's second phrasing returned definitions and affine consequences of IsFinite. Loogle for IsFinite with IsUniversalHomeomorphism returned no hits. The grep query over AlgebraicGeometry returned no generically-finite or radicial-etale match. The current item's old Q100 searches remain intact, followed by these fresh Q147 searches, exactly matching their queries in searches.jsonl. No unavailable service was represented as a negative search.

## Tool uses

The split_report declares the generic tools from other units: proper closed image/basic properties, the finite-open theorem 02NW, polynomial denominator spreading, finite implies integral, and purely inseparable spreading. These are ordinary scheme and field algebra inputs to the prescribed separable-first route, not replacements for the constructible-direct-image unit route. Mathlib leaves supply the other general algebra facts.

## Review by Q147

I checked the delivery-errors B--E against the finished node and the cited statements, rather than accepting the old parent proof as a proof. The principal sources I read were morphisms.tex lemma-generically-finite (02NW), including the qcqs hypothesis for (4); fields.tex lemma-separable-first (030K) and lemma-primitive-element (030N); algebra.tex definition-standard-etale (00UB), lemma-standard-etale (00UC) and integral-overring-surjective (00GQ); and the full local finite-algebra calculation in the original finite-pushforward blueprint. I also read the statements and proof of the existing purely inseparable-spreading node and the source of its localized-polynomial companion. The published universal-injectivity criterion 01S4 and universal-homeomorphism criterion 04DF explain the conclusion of that existing spreading statement; they are not invoked as unrecorded extra hypotheses in the item.

Step 1 uses exactly the closed-image conclusion, the qc/qs/finite-type consequences of properness, and the finite-type-over-Noetherian theorem. A field is Noetherian directly from its two ideals. No normality or excellence is introduced.

Step 2 uses the affine fraction-field theorem, the actual dominant generic-stalk map, the finite-dimensional-domain field theorem, and the affine-spectrum and pullback universal properties. The fraction-field theorem applies to every nonempty affine chart of integral X and S. Localizing its coordinate domain at nonzero base elements embeds it in L and makes it a K-subspace; elementary finite-dimensional linear algebra bounds its dimension. The cited field theorem makes it a field, and a field containing B contains Frac(B)=L. Thus every affine generic-fibre chart is Spec L and its only point is the same generic point of X. This checks the finite-fibre hypothesis of 02NW explicitly rather than assuming finite function-field extension means finite morphism. The affine fibre identification is verified by its universal property in the step itself.

Step 3 applies the existing 02NW node only after establishing qcqs, finite type, a Noetherian base, and its sole generic fibre finite. Its statement provides a dense open, not necessarily affine; the proof explicitly takes an affine open inside it. The finite-morphism definition then supplies the whole inverse image as an affine finite algebra. Basic-open restriction is proved with the affine universal property; it is not an unsupported invocation of a general permanence theorem.

Step 4 uses the full separable-first theorem (whose statement really includes pure inseparability over the relative separable closure), the finite-separable primitive-element theorem, the definition of separable minimal polynomial, the minimal-polynomial quotient isomorphism and the monic quotient basis. The finite subextension is justified by elementary linear algebra inside L. The last two cited statements together give both positivity and d=[K_s:K].

Step 5 uses the precise localized-polynomial-model statement to obtain a single base denominator and a Bezout identity. It does not take an embedding into B from that statement: it derives alpha=b/a from the generic localization calculation and explicitly inverts a. The existing power basis and minimal-degree property prove injectivity of A[T]/(Q) into B by coefficients, and identify its fraction field. This avoids assuming the initial schemes are normal or that alpha was initially regular on the whole finite inverse image.

Step 6 uses the monic basis for finiteness and rank, the standard-etale-monic-derivative node for etaleness after recognizing that Q' is already invertible, and lying over for surjectivity. During self-review I corrected an initially inadequate citation of the finite-morphism definition for 'finite implies integral': the finished step explicitly cites pqf-lem-finite-integral-lft, whose statement says precisely that. The finite C-module generators for B are the same A-module generators; this is a two-line elementary argument, not a new lemma.

Step 7 checks all five hypotheses of the inseparable-spreading node: A Noetherian domain, C finite etale domain, Frac(C)=K_s, B finite C-domain with Frac(B)=L, and finite pure inseparability of L/K_s. It localizes by an element of A, exactly as the cited statement promises, so no norm descent or arbitrary C-denominator is smuggled in. Reapplying the displayed polynomial and Bezout argument preserves finite etaleness and the power basis; lying over and finite-implies-integral supply surjectivity. The affine domain stalk/function-field theorem is cited for integrality and the precise function-field conclusion. Every step citation has a verbatim statement in citations.json, and proof_deps is exactly the union of uses.

I tested X=S and L=K (choose alpha=0 and Q=T), purely inseparable extensions (K_s=K, d=1 and a universal homeomorphism after shrinking), characteristic zero (K_s=L, the first map becomes an isomorphism after spreading), non-normal integral bases, and a positive-dimensional base with exceptional proper fibres (removed by 02NW). Empty X or S and infinite L/K are excluded by the actual hypotheses. Rank zero is excluded by deg(P)>=1. None of the seven steps exceeds 2000 characters; the largest is the explicit one-point generic-fibre calculation. No new lemma simply restates a clause, no node was added, and the substantial claims are all cited existing statements. Remaining denominator, generator, and universal-property computations are written out.

## Unfinished work

None in this stage-1 split. Server validation and delivery outcomes are recorded below when completed.
