## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedImmersionOfValuativeFactorization` states
`AlgebraicGeometry.isClosed_range_and_isClosedImmersion_of_valuativeFactorization`.
Its only proof is `sorry`; no definitions or auxiliary theorems were added.
The node copy changes only `lean`. No statement correction or disputed statement is needed.

Hypothesis and conclusion correspondence:

- “j:Z → S ... of schemes”: `{Z S : Scheme.{u}} (j : Z ⟶ S)`, with explicit universe `u`.
- “quasi-compact immersion”: `[QuasiCompact j] [IsImmersion j]`.
- “for every valuation ring A with fraction field K”: `∀ sq : ValuativeCommSq j`.
  Reading Mathlib's full structure shows fields `R : Type u`, `CommRing R`, `IsDomain R`,
  `ValuationRing R`, `K : Type u`, `Field K`, `Algebra R K`, and `IsFractionRing R K`.
  Thus this includes all valuation rings, including fields, not only discrete ones.
- “every morphism g:Spec(A) → S whose restriction Spec(K) → S factors through j”:
  `sq.i₂` is g, `sq.i₁ : Spec K ⟶ Z` is its factorization witness, and `sq.commSq`
  gives `sq.i₁ ≫ j = Spec.map (algebraMap R K) ≫ sq.i₂`, with the ring map bundled.
  Universal quantification over squares is equivalent to the conditional formulation:
  whenever a generic factorization exists, each such witness forms a square; the
  demanded conclusion does not depend on the witness. Conversely every square supplies
  such a witness. No property is demanded when no generic factorization exists.
- “also factors through j”: `∃ l : Spec (CommRingCat.of sq.R) ⟶ Z, l ≫ j = sq.i₂`.
  This deliberately requires only factorization of g, exactly as the node states.
  It does not add the triangle compatibility contained in `sq.commSq.HasLift`.
- “image j(Z) is closed in S”: `IsClosed (Set.range j)`; Mathlib coerces `j` to its
  underlying continuous function on points.
- “In particular ... is a closed immersion”: the second conjunct `IsClosedImmersion j`.

Dependency declarations:

`def-weil-scheme-morphism-properties` has `lean.convention = true`, and explicitly fixes
no independent notion. Its note directs citers to the declarations of the component
nodes. Read its statement and whole record, then read the component nodes
`def-weil-closed-immersion` and `def-weil-finite-type-morphism` and their `mathlib_match`.
The relevant declarations are `AlgebraicGeometry.QuasiCompact` in
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, and `AlgebraicGeometry.IsImmersion`
and `AlgebraicGeometry.IsClosedImmersion` in Mathlib's respective morphism modules.
Their full signatures and docstrings were read. The only import is
`Mathlib.AlgebraicGeometry.ValuativeCriterion`, which provides `ValuativeCommSq` and
imports the scheme properties used here. No private copies of any notion are made.

Sources were read online because the local literature checkout has no Stacks files:
[Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ) supplies probes for closure points,
[Tag 01R8](https://stacks.math.columbia.edu/tag/01R8) identifies the underlying image
closure with the scheme-theoretic image for quasi-compact morphisms, and
[Tag 01IQ](https://stacks.math.columbia.edu/tag/01IQ) supplies the final immersion criterion.
The declaration docstring carries all three proof steps and the two proof-dependency ids.

Edge cases checked before writing:

- Empty Z: no generic maps from a field spectrum exist, so the hypothesis is vacuous;
  the empty image is closed and the empty immersion is a closed immersion.
- Empty S: any morphism to S has empty source, giving the same conclusion.
- A valuation ring that is a field is allowed; its generic restriction is an isomorphism,
  so this case imposes no unintended extra hypothesis.
- The identity immersion satisfies the hypothesis and both conclusions.
- A nonclosed open immersion can fail the hypothesis when a valuation probe has generic
  point inside and closed point outside, as intended.
- Arbitrary characteristic, non-Noetherian schemes, nondiscrete valuations and valuation
  rings of any rank are allowed. No finite-type or separation assumption is added.
- The scheme universe is arbitrary `u`. Probe rings and fields use that same universe,
  following Mathlib's standard valuative criterion for `Scheme.{u}`; no fixed small
  universe is imposed.

Searches made:

- `msearch.py ... leanfinder`: “A quasi compact immersion of schemes whose image is stable
  under valuation ring specialization is a closed immersion”. Eight results include
  `isClosedMap_iff_specializingMap`, `UniversallyClosed.of_valuativeCriterion`,
  `IsClosedImmersion.of_isPreimmersion`, and the immersion factorization criterion.
  None states this precise hypothesis with both conclusions.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsClosedImmersion,
  AlgebraicGeometry.QuasiCompact`. One result: the immersion factorization criterion;
  no exact match.
- `msearch.py ... grep`: `valuativeCriterion|valuation.*closed|of_isPreimmersion` in
  `AlgebraicGeometry`. Twenty hits, including the general existence criterion and the
  closed-image preimmersion lemma; no exact match.
- `msearch.py ... leansearch`: “quasi compact immersion closed image valuation ring
  factorization criterion”. Service unavailable (Internal Server Error); no verdict.
- `rg` on project `WeilConjectures/AlgebraicGeometry` for
  `Valuative|valuative|IsPreimmersion`, then across all `WeilConjectures` for
  `valuation_factor_closed|valuation-factor-closed|ValuativeCriterion.RelativeTo|
  closed.*valuative|valuative.*closed`: related dense-source criteria and the converse
  `IsClosedImmersion.exists_lift_of_isFractionRing`. Read their signatures/docstrings;
  they do not state this result (the latter assumes a closed immersion).
- `rg` on `lean/Sheaf` for `valuation|Valuative|IsPreimmersion`: unrelated valuation
  arithmetic and evaluation results; no duplicate statement.
- `rg` on all `WeilConjectures` for the item id: no hits.
- `rg` on `dag/lean_names_upstream.json` for valuation/closedness and valuative criteria:
  only the related generic closed-subscheme factorization and dense-source results.
- Exact proposed name search `isClosed_range_and_isClosedImmersion_of_valuativeFactorization|
  valuativeFactorization` in Mathlib, upstream source, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no collisions.

Validation: the server `scompile.py` run compiled the 46-line module in 1.6 seconds,
with exit code 0 and no warnings. The delivery dry run printed OK: compilation and preflight passed except for the
second-reading section, which the independent second reader will write before delivery.
Nothing was pushed.

## Second reading by K1

I independently read the node statement, its source tags, the dependency records, and the
Lean module. The correspondence is as follows.

- The source morphism `j:Z→S` is rendered by `{Z S : Scheme.{u}} (j : Z ⟶ S)`;
  the universe is arbitrary and no extra scheme structure is imposed. Verdict: exact.
- “Quasi-compact immersion” is rendered by the typeclass binders `[QuasiCompact j]`
  and `[IsImmersion j]`, using the Mathlib notions recorded by the dependency nodes.
  Verdict: exact; no finite type, Noetherian, separated, or characteristic hypothesis is
  added.
- A valuation ring `A` with fraction field `K`, and a map `g : Spec A → S` whose generic
  restriction factors through `j`, are rendered by `sq : ValuativeCommSq j`: its `R`, `K`,
  `i₂`, `i₁`, and `commSq` fields provide precisely these data, with the commutative
  generic triangle. Quantifying over all squares quantifies over every such witness, which
  is equivalent to the source's conditional wording because the conclusion only concerns
  `g`. Verdict: exact.
- “Also factors through `j`” is rendered by
  `∃ l : Spec (CommRingCat.of sq.R) ⟶ Z, l ≫ j = sq.i₂`. This asks exactly for a
  factorization of the bottom map and does not impose an extra compatibility condition.
  Verdict: exact.
- “The image `j(Z)` is closed” is rendered by `IsClosed (Set.range j)`, the underlying
  topological range of the scheme morphism. Verdict: exact.
- “In particular ... is a closed immersion” is rendered by the second conjunct
  `IsClosedImmersion j`. Verdict: exact, matching Tag 01IQ for an immersion with closed
  image.

The source text at Tags 02JQ and 01R8 supplies the valuation probe at every point of the
closure of the image for a quasi-compact morphism, and Tag 01IQ gives the closed-image
criterion for immersions. The Lean docstring records these three proof steps and cites the
same proof nodes. The empty source or target, zero/empty affine rings where represented by
schemes, valuation rings that are fields, arbitrary characteristic, nondiscrete or higher
rank valuations, and `n = 0` (which is not a parameter of this statement) introduce no
excluded case. The arbitrary universe `u` covers all scheme universes allowed by the node.

I checked both citers, `lem-sc-picard-locus-closed` and
`lem-sc-picard-valuation-probe-closure`; each uses the hypothesis and conclusion in the
same direction and remains valid. I searched Mathlib, `WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` by the theorem name and by valuation/closed-image concepts;
only general valuative criteria and immersion lemmas were found, with no declaration stating
this conjunction. No mismatch was found, so no source, node statement, dependency, or Lean
code was changed. The existing worker module compiles cleanly with its sole named `sorry`.
