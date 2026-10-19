# Stage-1 delivery: lem-a1-uniformizer-differential-basis

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-uniformizer-differential-basis.json`: existing statement split into six proof steps; no Mathlib match for the whole item. Its statement, statement dependencies, provenance and blueprint ancestry are retained.
- No new nodes; zero new Mathlib leaves.
- `citations.json`: sixteen entries, one per step/node pair, quoting the cited statements verbatim.
- `searches.jsonl`: the search command's actual records. `prepare.py` is sandbox-only preparation, not part of the delivery.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the blueprint tag, uniformizer/uniformiser, cotangent, and differential-basis terminology. The curve, divisor and differential declarations found do not state this whole item. Existing DAG audits that name proved regularity or cotangent declarations are dependencies, not grounds for attaching this item. The exact upstream master is reference material, not proof evidence.

## WANTED

None: the item and the algebraic inputs are in the local Stacks sources.

## Findings and changes

The imported item was statement-only. Its statement is true as written and needs no repair: finite separability is assumed, not derived from an arbitrary field. The proof now establishes the assertion that the local ring is a DVR as well as the assertion about every uniformizer. This matters because the former is part of the statement rather than an extra hypothesis.

I read `curves.tex`, Tag 0C1E, `lemma-uniformizer-works`, statement and entire proof (lines 2411–2430). Its route is smooth local regularity, nonzero residue differential via 00TU, and rank-one freeness. I made explicit the dimension and localization checks needed to apply that route to the curve convention of this node. The current main-20261015 proof of `lem-a1-finite-map-curve`, third paragraph, needs precisely this local input: the parent split writes a function near its sole pole in a local parameter and differentiates it. This delivery does not alter that parent or the unit or chapter route.

In particular I did not use `lem-sc-smooth-connected-curve-local-rings`, whose statement assumes an algebraically closed field, or invoke normality to use `lem-sc-normal-dim1-dvr`. Instead the cited algebraic regularity theorem applies over any field and the regular-dimension-one node supplies the DVR assertion. Nor did I cite only a definition of the differential sheaf for localization of differentials: the exact localization theorem is cited.

## Not duplicates

There are no new nodes and therefore no new/existing pairs to distinguish. The DAG and whole-blueprint searches found the needed cotangent injection, scheme-dimension and generalization-chain statements, smooth-affine comparison, regularity, DVR criterion, smooth differential rank, and localization nodes already present. Blueprint searches for `uniformizer differential`, `0C1E`, and `00TU` returned no blueprint statement of the item. The search for `regular local ring of dimension one` found `lem-sc-regular-dim1-dvr`, which is reused.

## Review by N2

I checked the actual statement of every cited node against its use, not just its title or source. Here is the mathematical review, in step order.

1. `def-pc-curve` and `def-pc-dimension` give dimension one using the supremum of local-ring dimensions. `lem-pc-scheme-dimension-local-rings` explicitly identifies that supremum with topological dimension. `lem-sc-scheme-sober` supplies a generic point of the integral scheme; `lem-sc-scheme-stalk-dimension-generalization-chains` explicitly measures stalk dimension by chains through the specified point. The closed point is distinct from the generic point, so that chain has length one. The upper bound comes from the curve hypothesis. For dimension at the point, every neighbourhood contains those two points and the strict irreducible-closed chain; closing chains in the ambient space gives the upper bound one. This directly proves the minimum in `def-kun-dimension` equals one. I read Properties 04MU (`lemma-dimension`) and 02IZ (`lemma-codimension-local-ring`) and Schemes 01IS (`lemma-scheme-sober`). Thus global dimension, local-ring dimension and dimension at the point are not silently identified.

2. `lem-weil-pbc-smooth-restrict-open-subschemes` states restriction preserves smoothness; `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` gives the equivalence for the same affine morphism; `lem-weil-pbc-affine-open-stalk-localization`, clause (c), identifies the actual germ map with prime localization. Therefore `lem-weil-pbc-smooth-over-field-regular-local` applies to a smooth algebra over the given field, with no perfectness assumption. Its regular local ring is Noetherian by the definition of regularity. `lem-sc-regular-dim1-dvr` has exactly the regularity and dimension-one hypotheses now proved. I read Algebra 00TT (`lemma-characterize-smooth-over-field`), including its final regularity assertion, and 00PD (`lemma-characterize-dvr`), condition (3); Morphisms 01V6 (`lemma-smooth-characterize`), including restriction; Schemes 01HV (`lemma-spec-sheaves`), (6); and More on Morphisms 02H6 (`lemma-smooth-formally-smooth`) to check agreement with the project's infinitesimal definition. The existing DVR criterion's external 00DV is a Nakayama reference in its proof, not the tag of the DVR equivalence: this delivery cites 00PD at this application.

3. `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension` supplies an actual affine chart with a free module of rank equal to dimension at the fibre point. The base is Spec of a field, so its nonempty affine open and its residue field are that same field; the fibre is X and the dimension proved in step 1 is one. The affine-stalk node again supplies the actual local ring. `lem-weil-pbc-kahler-differentials-localization` states the isomorphism for any multiplicative subset, so applies to the prime complement, not only a principal localization. Localizing a basis is elementary: localize the basis isomorphism and its inverse. I read Morphisms 02G1 (`lemma-smooth-omega-finite-locally-free`) and Algebra 00RT (`lemma-differentials-localize`), (2). No argument about the chosen uniformizer has been hidden in this step.

4. The precise definition in `def-sc-discrete-valuation-ring` says local domain, nonzero principal maximal ideal, and that a uniformizer generates that ideal. From these, the displayed cancellation argument proves its class modulo the square is nonzero. This is elementary and needs neither a new DVR lemma nor Nakayama. It proves the local class fact in the middle sentence of 0C1E explicitly.

5. `lem-weil-pbc-separable-residue-cotangent-injective` has precisely the map used, with the formula for its value on each maximal-ideal element. The local ring is Noetherian from step 2 and contains the base field because a unital map from a field into this nonzero ring is injective. The finite separable residue extension is a hypothesis of the item; a finite linear basis also generates it as a field, verifying the node's finite-generation requirement. I read Algebra 00TU (`lemma-computation-differential`), statement and entire proof, including its square-zero residue splitting argument. It sends the nonzero class of t to dt tensor 1, so the required nonvanishing really follows from its stated injection.

6. This is elementary linear algebra over a local ring using the preceding two steps: in a chosen free rank-one basis, the coefficient of dt has nonzero residue and therefore is a unit. Tensor the basis isomorphism and inverse to obtain the residue coordinate; the written inverse using that unit proves the claimed map is an isomorphism. This expands the final sentence of 0C1E without appealing to an uncited form of Nakayama or merely declaring that the element lifts a basis.

I checked B–E of `delivery-errors.md` against the resulting files. There is no unstated new lemma, new definition, duplicated node, clause renamed as a child, or proof moved into a single child. The only new proof steps marked elementary are the explicit cancellation and unit-coefficient arguments. All other steps cite the precise generic results they use. Every dependency occurs in a step, and every step citation has a verbatim statement quote in `citations.json`. No step exceeds 2000 characters; the longest is 1063, so there is no long-step hidden-lemma issue.

I tested the hypotheses on A = k[T] localized at (T): t = uT has differential (u + T u')dT with unit residue coefficient. At a nonrational separable closed point (P(T)), dP = P'(T)dT and P' is a unit locally, so no rationality assumption is needed. In characteristic p, if a is not a p-th power in k and the point is (T^p-a), its uniformizer has zero differential although the local differential module is free on dT; this confirms why the separability assumption is indispensable. The generic point is not a closed point on a positive-dimensional integral curve; its local ring is a field and is deliberately excluded. These checks found no statement dispute.

For Mathlib I ran LeanFinder twice with different statements, Loogle, LeanSearch, and grep using the prescribed command. I read all returned hits and the relevant source of `SubmersivePresentation.basisKaehler` and `IsStandardSmooth.iff_exists_basis_kaehlerDifferential`; these supply bases tied to presentations or general constructions, not the particular differential of every local uniformizer. The second LeanFinder query also returned the DVR cotangent-space dimension theorem; that covers only a proper part. None is an attachment or a one-line specialization of the whole item. The actual new search entries and their verdicts are appended after the inherited search record, without inventing searches. No search service was unavailable in these calls.

The off-unit uses declared in `split_report.tool_uses` are generic scheme dimension and local algebra inputs to 0C1E; the affine-line unit contains no replacements for them. They do not replace its finite-map or weight-estimate route. Mathlib leaves and Lean-closed inputs need no route exception. No other files of the project, any Lean source, or any launcher were written.

## Validation

The first dry run rejected two uses of the phrase “the item's” in steps 2 and 5 under the self-contained wording check. I replaced them with the explicit DVR assertion for A and the finite separability assumption on kappa(x)/k. The mathematics and citations did not change.

## Unfinished work

None in this one-level split. There are no new statement-only children to search or split. Independent maintainer review and any later Lean formalization remain outside this worker's stage-1 task.
