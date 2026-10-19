# Worker report: Q20 / lem-trf-semistable-normal-target-factorization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-semistable-normal-target-factorization.json`: statement, split into eight proof steps; Mathlib verdict: no match. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 21 citations in the eight proof steps.
- `searches.jsonl`: actual logged Mathlib searches. `build_split.py` is sandbox-only working material.

## Attachments

None. Searches of the read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag, multipointed curves, semistability, and normal-target factorization found no declaration proving this item. The upstream master source is reference material only; it supplies no attachment.

## WANTED

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Temkin, Stable modification of relative curves, Proposition 3.5.2, Remark 4.1, Lemma 4.4.1(i), and the first sentence of Lemma 4.4.4, for this item. The archival file is absent here. I read the primary author's PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf online, including the section-4 preamble (finite-height valuation base with separably closed fraction field), printed pp. 20--21, 24--25 and 30--31. The proof is marked agent because that document is not in the local literature tree and because the marking factorization and finite-fibre argument are expanded here.

## Findings and corrections

The item was an unsplit statement with searches but no proof, not an earlier completed sandbox delivery. I retained its statement exactly, its citations, ancestry, created metadata, and inherited Mathlib searches. There was no statement dispute and no weakening. In particular the target X need not be integral, proper, separated, or Noetherian, and the valuation need not be discrete or excellent.

The key existing input is `lem-trf-valuation-curve-projective-preparation`, which covers arbitrary T-curves, rather than `lem-trf-valuation-curve-finite-normalization`, which assumes the curve integral. The former already supplies the finite normal T-curve and the factorization for a normal source. I did not recreate either input. The strict-semistable normality node cannot be applied to an arbitrary semistable source; instead the proof establishes normality using the finite normalization and the eta-normality theorem. Both are existing same-unit nodes. There is no cycle through the item in any cited dependency closure.

I also checked the comparison of the specified relative normalization with the absolute one, rather than silently equating them. A smooth generic affine algebra is a finite product of normal domains, so its integral closure in the product of component fraction fields adds nothing to that algebra. The closures of the original affine algebra inside these two ambient rings are identical.

## Not duplicates

No new nodes. Whole-DAG keyword searches located and reused the general projective-preparation, horizontal-curve/marking-closure, eta-normality, finite-fibre, properness, and section-ring nodes. Whole-blueprint searches for `semistable normalization`, `normal target`, `finite normal`, `schematic closure valuation`, and `normalization` found no blueprint node stating this entire factorization with its two contraction assertions; `blueprint.same_as` is empty. The two hits for `finite normal` concern finite-normalization cohomology comparisons, not the present statement.

## Review by Q20

I read the item and every cited statement, not merely the titles or the proofs of the inputs. I checked the first sentence of Temkin Lemma 4.4.4 against the normalization statement in Lemma 4.4.1(i), the marking construction in Remark 4.1, and the eta-normality statement of Proposition 3.5.2. The online Stacks texts 01R8 and 01W6 confirm the kernel-ideal and proper-to-separated tools. There are no new nodes whose source needs a separate review.

Step 1 uses only `lem-sc-flat-invertible-sections-torsion-free` for injectivity of multiplication on sections of the structure sheaf of each flat scheme. I verified its domain and invertible-sheaf hypotheses, and wrote out the valuation-domain integral-closedness and finite-height principal-generic-open arguments. The case V=K uses a=1. This is an elementary step with a cited input, not an unproved flatness assertion.

Step 2 uses exactly the first normalization clause of `lem-trf-valuation-curve-projective-preparation`; X satisfies its T-curve and smooth-generic-fibre hypotheses without being integral. `lem-trf-valuation-horizontal-curve-models` supplies reducedness and finitely many components so that the dense generic open has all the component generic points. `lem-trf-smooth-geometrically-normal` gives normal generic local rings. `lem-weil-pbc-finite-type-over-noetherian` applies only to the generic affine over a field, not over V. The generic affine is therefore within the locally Noetherian hypotheses of `lem-sbc-normal-sections-finite-product`. Its product of normal domains justifies the coordinatewise integral-closure comparison. `lem-weil-pbc-relative-normalization` supplies precisely the affine relative-closure charts being identified. These inputs give every asserted property of N, including finite presentation; I do not infer that property from finiteness alone.

Step 3 applies the exact marking-closure assertion of `lem-trf-valuation-horizontal-curve-models` to the reduced modification N->X. It gives the multipointed pair and proper eta-modification, not merely a closed subset. The extra finiteness of D_N->D is written out: the defining equations of D vanish on the generic marking and hence on its kernel-defined closure; the closure is closed in N x_X D. `lem-weil-pbc-finite-morphism-permanence` provides finite base change. The quotient of a finite module remains finite; `lem-weil-pbc-finite-proper` then gives separatedness and properness.

Step 4 uses the explicit semistable instance in the statement of `lem-trf-geometrically-reduced-eta-normal` over the normal integral qcqs T established in Step 1. Applying the preparation theorem to Y is valid because Y_eta is isomorphic to the smooth X_eta. Eta-normality makes the finite normalization of Y an isomorphism. No assertion for strictly semistable curves was substituted for general semistability.

Step 5 uses the preparation node's stated factorization for a normal-source eta-modification, with Y now normal. `lem-weil-pbc-proper-to-separated` applies over X, since f_Y is proper and N is separated over X. The generic-fibre identity and density are verified explicitly, giving the modification property for g_Y.

Step 6 checks the scheme-theoretic marking factorization, rather than inferring it from image containment. On every affine of N, each equation of D_N restricts to zero on E_eta and hence on E by schematic density. `lem-weil-pbc-scheme-image-qc-kernel` states exactly the ideal-kernel factorization used. I verified its quasi-compactness hypothesis using `lem-weil-pbc-qcqs-morphism-permanence`: E is quasi-compact and N quasi-separated because both relevant structure morphisms are finitely presented over affine T. The marking equation is obtained by cancellation of a closed immersion. Proper-to-separated is applied over D, where E->D is the original proper f_D and D_N->D is finite. Generic isomorphism and density give the full marking modification, so both maps of the pair factor correctly.

Step 7 uses only the definition in `def-trf-multipointed-curve-modification`: a semistable modification is defined by its source pair. The source schemes, marking immersion, smooth-locus condition and etaleness are unchanged.

Step 8 checks both directions of each contraction assertion. The nontrivial direction uses `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum` with an actual field kappa(x), and `lem-weil-pbc-fibre-ring-primes-bijection` identifies its primes with the points above x while preserving specialization. Finiteness of the algebra follows by tensoring the module generators. An irreducible nonempty image inside that finite discrete fibre is one point. `lem-weil-pbc-finite-morphism-permanence` supplies finiteness after every specified geometric base change, where the argument is rerun for the new components; it does not assume preservation of irreducibility of an old component.

The two off-unit non-Mathlib tools are declared in split_report.tool_uses for maintainer acceptance: flat sectionwise torsion-freeness and the finite-product description of sections of a normal locally Noetherian scheme. They are generic tools and do not replace any part of this unit's normalization route. All the other non-Mathlib inputs follow the same sk-i-curve-zero route.

For the B--E checklist: there are no statement-only new nodes to hide a proof or duplicate an item clause; the item has a complete proof using existing statements. Its TeX and complete hypotheses were retained. Citations are verbatim and every substantive fact in each step is supplied by the listed nodes or the explicit affine/ideal argument. The proof-dependency list is exactly the union of the uses. All eight steps are shorter than 2000 characters; no long step is concealing a separate lemma. Edge cases checked: empty X or D; disconnected or nonseparated curves; height zero (the normalization and pair maps are identities); higher finite height; positive characteristic with separably closed but imperfect K; nonclosed fibre image point x; and geometric components that split after a residue-field extension. The finite-fibre argument allows nilpotents in the finite fibre and does not require reduced fibres of nu.

The Mathlib searches are exactly the logged msearch.py invocations, with both semantic phrasings and source grep. I read Normalization.lean around fromNormalization (174), the integral instance (200), normalizationObjIso (223), and normalizationDesc (377). That API constructs an integral relative normalization and maps out of it toward another integral factorization; it does not prove the finite valuation-curve target or the marked contraction assertions. The earlier inherited searches and their explanations are retained. No search was invented, and no compiler or Lake command was run.

## Unfinished work

Nothing in the requested stage-1 split. The reused inputs retain their existing status and are not claimed to be new Mathlib leaves. Independent maintainer review and archival promotion of the requested source remain outside this delivery.
