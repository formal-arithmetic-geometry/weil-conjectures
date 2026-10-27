1. Files written

- `dag/nodes/sec-smooth-purity/lem-route-smooth-purity-iso-zero-of-is-open-immersion.json`: item, statement and three proof steps; Mathlib search found no matching geometric normalization theorem.
- `dag/nodes/sec-smooth-purity/lem-pur-condensed-open-counit-realization.json`: new statement-only comparison lemma; unsplit, no Mathlib match. It concerns arbitrary completed integral constructible inputs and the actual open counit, with no smooth-purity map in its statement.
- `citations.json`: one verbatim statement quote per proof-step citation. `searches.jsonl` is the search command's own log.

2. Attachments

None. The live declaration `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion`, in `lean/WeilConjectures/SmoothPurity/Defs.lean` at lines 174–179, still has `sorry`.

3. WANTED

None.

4. Problems corrected

The imported statement was a provisional docstring and signature without its implicit geometric hypotheses or a definition of the chosen maps. The new prose introduces the same objects and exact equality as the signature, including positive characteristic, separated finite type, finite-extension-valued condensed coefficients, and both zero identifications. This is a faithful expansion, not a statement dispute or a changed target. The live `def-route-smooth-trace` was independently completed while this work was running; I reread its final reviewed construction and now cite its statement directly. I avoided citing `def-pur-condensed-smooth-purity-iso`, whose machine-added proof dependencies include this item and would make a cycle.

The first dry run rejected missing proof-origin metadata; this is now agent-authored with the current blueprint as its route source. My mathematical recheck also rejected my own initial use of the finite-ring `prop-exc-open-adjoint` in the condensed step. It is now used only at finite coefficients. The missing counit identification through condensed realization is stated as a generic new obligation, rather than inferred from objectwise isomorphisms or from equality after finite evaluation.

5. Unfinished work

The new comparison lemma is deliberately statement-only and joins the stage-1 queue. No Lean was written or compiled. This delivery is a one-level split, not a claim that its dependencies already have complete proofs.

## Not duplicates

No source-tag collision: the new node is sourced to the current coefficient-transport blueprint and is explicitly an agent-formulated obligation. Whole-DAG keyword searches and `tools/blueprint_refs.py search` for open/counit/realization and open/scalar found no blueprint node stating this combined comparison.

lem-pur-condensed-open-counit-realization vs lem-sf-integral-open-reduction-comparison: the existing statement stops at the completed integral open adjunction; the new one compares that actual counit with the condensed algebraic-closure adjunction after rationalization and scalar extension.

lem-pur-condensed-open-counit-realization vs lem-pur-compact-support-condensed-realization: the existing statement explicitly makes no assertion about right adjoints; the new one identifies the specified open restriction comparison and actual adjunction counit.

lem-pur-condensed-open-counit-realization vs lem-weil-pbc-condensed-e-realization: the existing adjunction clauses concern pullback/direct image, not extension by zero/restriction, and only finite coefficient fields; the new node fixes the open counit and the algebraic-closure realization.

lem-pur-condensed-open-counit-realization vs lem-pd-section-derived-open-adjunction-normalization: the existing statement compares internal and section-module versions of a fixed coefficient open adjunction; it does not compare completed reduction systems with condensed coefficient realization.

lem-pur-condensed-open-counit-realization vs lem-sfb-open-scalar-conjugate-normalization: the existing statement normalizes scalar change between already condensed coefficient rings and the open unit; it does not identify reconstructed strict-system counits with the actual completed and condensed open counits.

## Review by NF

I read the current `sk-thm-purity-transport` unit and proof, the upstream `SmoothPurity/Defs.lean` and `OpenImmersionUpperShriek.lean`, and every statement cited by the item's steps. I also read the reviewed construction of `def-route-smooth-trace`. The trace is concretely epsilon after F of c followed by the inverse Tate-realization map. Thus its adjoint is that actual composite by the Hom-equivalence inverse law, and smoothPurityIso is its inverse; I do not assume arbitrary isomorphisms define the normalized map.

Step 1 cites `lem-pur-finite-smooth-adjunction-general-base`, whose statement expressly specifies the diagonal/deformation construction, its adjoint trace, the d=0 étale normalization, and quotient coherence, and `prop-exc-open-adjoint`, which gives the finite-ring open adjunction on whole ordinary derived categories. A separated finite-type scheme over a field is Noetherian, and the given open is quasi-compact; no properness, algebraic closure, or surjectivity is added. Only finite coefficients are used here.

Step 2 cites `lem-pur-condensed-tate-integral-tower` for completed constructibility, canonical reductions and concentration in degree 0, and `lem-pur-condensed-exceptional-reconstruction` for its single-degree case (b), with r=0. I checked that the input is the actual normalized strict system with the quotient maps, not a collection of unrelated level isomorphisms. Its statement constructs the system comparison from degree-zero concentration and pins its counit to the system counit; it also expressly preserves compactification refinements. The new open-counit realization statement supplies exactly the remaining identification with the actual condensed counit, including the canonical unit comparison. Its hypotheses match the integral unit on Y and its restriction to X. It does not assert smooth purity or the item's equality.

Step 3 cites `def-route-smooth-trace` for the exact epsilon-F(alpha) formula, `lem-pur-condensed-tate-realization` for the canonical d=0 realized-unit identification on both schemes, and `det-sp-unique-right-adjoint` for uniqueness of the counit-preserving comparison, including at a single object. Writing alpha=c a^{-1} shows its inverse is a c^{-1}. The unit identification a followed by zero shift and zero twist is the canonical realized unit; hence a c^{-1} is exactly the asserted three-factor composite. The equality is between isomorphisms in the derived category, not a degreewise claim. All quotations in citations.json were taken from these statements, not their proofs. Each proof step is below 2000 characters.

For the new node I read Stacks `sites-modules.tex`, Tag 03DI, label lemma-extension-by-zero (the summand construction and explicit evaluation adjunction), Tag 03DJ, lemma-extension-by-zero-exact, and Tag 0E8I, lemma-j-shriek-and-tensor, plus `sites-cohomology.tex`, Tag 0GL1, lemma-j-shriek-and-tensor. These support the ordinary and K-flat scalar comparison used to formulate the obligation. None is represented as already proving the full completed-to-condensed comparison: the new source says this is agent-formulated. The intended future argument first uses the completed open-reduction comparison to transport the strict counit, then computes the scalar square on a K-flat extension summand, where both routes send [m] tensor b to b times m, and descends through the canonical derived localizations and full subcategory inclusions. This argument is retained here, not smuggled into the new statement as a proof. Its source and definition dependencies specify the actual functors and maps.

Edge cases checked: j the identity (all comparisons reduce to the ordinary unit counit identities), empty source (the relevant source categories and maps are zero), empty target, disconnected source or target, zero integral input for the new lemma, finite field k, and non-algebraically-closed k. A non-proper open immersion is covered; no use of finite étale pushforward or improper interchange of inverse limits with extension by zero is made. The comparison through the actual reduction unit is precisely why the new lemma is non-elementary. It is not a one-line specialization of the existing pure category-theory search hits, which do not identify these geometric comparisons.

Mathlib searches were made only by msearch.py and their hits read: geometric purity queries return scheme ring-section or standard-smooth algebra results, and the new comparison queries return condensed-set/topological adjunctions, generic Kan extensions, or complex-shape embeddings. None has the required completed constructible and condensed-module objects. The original unknown-identifier Loogle query is recorded as such, not as evidence for a theorem that it did not return.

Blueprint provenance: `tools/blueprint_refs.py ancestor lem-route-smooth-purity-iso-zero-of-is-open-immersion` reports None because its created.item chain runs through a target with no imported ancestor. The new node therefore has from.node=null as required by the second dry-run diagnostic, while from.place names the actual current coefficient-transport proof passage; the item retains its pre-existing historical ancestor field.
