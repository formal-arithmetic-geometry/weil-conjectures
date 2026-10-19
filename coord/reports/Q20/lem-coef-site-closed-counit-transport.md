# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-site-closed-counit-transport.json` — existing statement node, split into four steps; zero new nodes and zero Mathlib leaves.
- `citations.json` — retained verbatim quotations for every proof-step dependency.
- `searches.jsonl` — retained earlier searches and the additional recorded grep used to inspect the generic adjunction candidates.

## Attachments

None. Searches in the read-only slopmaster2 and master `WeilConjectures/` trees for the item id and the closed-counit/transport notions did not find a project declaration stating this item exactly. The nearby pro-etale `UpperLowerStar/ClosedImmersion.lean` concerns the ordinary pullback/direct-image counit, with its full-faithfulness theorem itself sorried; it does not state the exceptional derived transport identity.

## WANTED

None.

## What I checked and changed

The item statement is unchanged from the current repository. The interrupted attempt already supplied the four-step proof, citations and search log; I retained that argument. The first resumed dry run passed at `b96fe80190`. I then made the bounded-below typing of the ordinary etale object `I U_P S_P H` explicit, updated the report to describe the saved proof, and reconciled its search-result records with the actual Q20 log. One malformed Loogle attempt is recorded as an invalid query, not as evidence of absence; the subsequent corrected query ran successfully. No search was invented or silently discarded.

I read the historical parent source `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-dualizing.md`. Its current text invokes the finite-duality site comparison but no longer contains the former equation (*), so that equation's location is historical ancestry rather than a claim about a paragraph still present. The operative proof source is the explicit Hom chain in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-existence/thm-sf-ambient-adjoint-class.proof.md`; I also read the compact-support comparison proof in that directory. The proof is correctly marked agent-written and expands that chain on morphisms.

The logged Mathlib hits concern generic full faithfulness, restriction of adjunctions, sheaf adjunctions and scheme-module restriction. I inspected `Mathlib/CategoryTheory/Adjunction/Restrict.lean` (especially lines 62–84), `FullyFaithful.lean` (129–144), and `Basic.lean` (215–219). They supply the usual formal adjunction operations, but do not identify the geometric comparison, its normalized direct-image mate, or this particular relative exceptional Hom bijection. The formal calculations using those operations are written as elementary steps rather than new nodes.

## Review by Q20

I opened the current statements of all seven proof dependencies and compared them with the four steps and the retained citations. Step 1 uses `lem-exc-closed-ambient` for the ordinary etale adjunction, `thm-weil-pbc-site-comparison` for the specified isomorphic unit, `def-weil-exceptional-inverse-image` for the finite transported composite, and `def-sf-comparison-derived-pullback` for preservation of bounded-below objects. These statements give the required data. The hypothesis `IH` bounded below and the isomorphism `I(eta_H)` also put `I U_P S_P H` in the ordinary bounded-below category, so full faithfulness in Step 2 is applied within its domain. Applying `S_Z` supplies the etale-origin witness `(IH, alpha_H)` for `J S_P H`, without constructibility.

Step 2 unpacks the bijection fixed by `thm-sf-ambient-adjoint-class` and the transport specified by `def-weil-exceptional-inverse-image`. `lem-sf-class-compact-support-comparison` supplies the canonical compact-support comparison; at the identity-open compactification its extension-by-zero legs are identities, leaving the inverse direct-image comparison. `lem-weil-pbc-comparison-direct-image-canonical-mate` specifies precisely that named natural isomorphism, rather than an unspecified isomorphism of endpoints. Its normalization concerns the ordinary pullback/direct-image adjunction, not the exceptional counit being proved. The remaining arrows are the comparison adjunction, the ordinary exceptional Hom bijection, and full faithfulness from `thm-weil-pbc-site-comparison`. The displayed formulas show their directions and action on a morphism. All coefficients are ordinary constant finite-ring modules; no condensed coefficient category is substituted.

Step 3 uses naturality of the specified unit from `thm-weil-pbc-site-comparison` and target naturality of the ordinary adjunction from `lem-exc-closed-ambient`. Cancelling delta with its inverse, then substituting the two naturality equations, computes the general adjunct as `alpha_H` composed with `S_Z` of the ordinary adjunct. This is an elementary calculation from the cited adjunction data, not an assumed compatibility lemma.

Step 4 uses `lem-exc-closed-ambient` for the transpose of its counit being the identity and `thm-sf-ambient-adjoint-class` for source naturality and injectivity of the stipulated bijection. Step 1 supplies the etale-origin witness needed to evaluate that bijection at `J S_P H`. The two morphisms have the same transpose `alpha_H`; injectivity and composition with delta give exactly the asserted exceptional counit equation. Thus the exceptional normalization is proved rather than imported from the ordinary-mate normalization.

For the identity closed immersion, `I` is the identity but `J` is `S U`; I corrected the earlier report's claim that all functors and counits were literally identities. With the canonical identity direct-image comparisons, the equation is the comparison triangle `epsilon_(S H)` composed with `S(eta_H)` equals the identity. For the empty closed subscheme the source category is zero and both equations are the unique-map equations. The zero input gives the same check. No bounded-constructible or finite-Tor hypothesis is used, and no unbounded pro-etale adjunction is asserted.

Against delivery-errors B–E: there are no new-node form, duplicate or relabelling issues; the whole argument remains in the item's steps. The blueprint/DAG searches for counit and transport included the nearby `lem-sf-etale-proetale-exceptional-transport`, whose statement assumes bounded constructible finite-Tor input and preservation, and therefore does not state this arbitrary bounded-below identity. All proof-step quotations are verbatim parts of the current cited statements, the uses equal the proof-dependency union, and each non-elementary input is a named citation. Every step is below 2000 characters. No statement correction, unit-route change or SGA citation was introduced. The generic off-unit inputs are declared in `split_report.tool_uses` for the maintainer's review.

## What remains unfinished

Nothing in this one-level split. The cited existing nodes retain responsibility for their own proofs; this delivery introduces no further obligations.
