# NF: prop-a1-fourier-middle-extension

## Files written

- `dag/nodes/sec-deligne-laumon-a1/prop-a1-fourier-middle-extension.json`: statement; split using existing DAG statements, no Mathlib match. Five complete proof steps, each shorter than 2000 characters.
- `dag/units/sk-p-dl-a1-middle.json`: only `realized` and `realized_by`. The item realizes the first assertion and first unit step; `lem-a1-unramified-nonexceptional` realizes the separate final assertion and second unit step. The definition is also included in the statement realization.
- `citations.json`: one verbatim operative statement quotation per step/node pair.
- `searches.jsonl`: actual search-command log. No new nodes and no Mathlib leaves.

`prepare.py` is an item-specific sandbox preparation script, not a delivery node.

## Attachments and Lean audit

No attachment of the item is claimed. I read `WeilConjectures/DeligneLaumon/AffineLine/MiddleExtension.lean` in the supplied slopmaster2 checkout, especially lines 151–207. `AlgebraicGeometry.exists_middleExtension_fourierTransform` at line 195 has a short proof, but uses `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isEmpty_iso_fourierTransform_middleExtension_toComplex`, whose proof at lines 162–166 is `sorry`. The Fourier equivalence in `WeilSheaf/Fourier.lean`, lines 1383–1390, is also sorried. Consequently the item cannot be attached as closed. Arithmetic irreducibility, the stronger constituent-nonexceptionality, and the nontrivial-character hypothesis agree with the current blueprint statement.

The audit's auxiliary list is partly stale relative to the supplied source. The named `WeilSheaf/LowerShriekOperations.lean` and `WeilSheaf/FourierInversion/{Delta,UpperStar,Composite}.lean` files do not exist, and searches for their named helper declarations in the current `WeilConjectures/` tree have no hits. I have preserved the audit rather than manufacture statements from missing source. Their mathematical roles have existing DAG homes: compact-support composition is in `prop-functor-package`; the two inverse-Fourier composites are in `lem-fd-inversion` and the exact inverse equivalence in `thm-a1-fourier-t-exact`; the delta/kernel computation is performed explicitly in Step 3. The missing upper-star implementation helpers are not invoked by this proof. The still-present declaration `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine`, lines 405–415 of `SixFunctors/ProEtale/Adic/LowerStar.lean`, is stated by the existing `lem-sf-adic-affine-direct-image-finiteness`; it is a coefficient-model-specific implementation input, not a new lemma of this item. The punctual-exclusion declaration is precisely the existing item's Steps 2–3; making it a new node would duplicate the principal clause instead of splitting it. Its argument is now Steps 2–5 of the item.

## WANTED

None. The current blueprint and Laumon's article used for checking the normalization and kernel computation are available locally.

## Statement correction and source issues

STATEMENT-DISPUTED: the imported statement did not bind the character or explicitly require it to be nontrivial. I replaced it by the statement already recorded in `blueprint_update`, exactly as in the main-20261015 source. This is the current source's hypothesis, not an added hypothesis for convenience. If trivial characters were allowed, take the affine line over a prime field and a nontrivial rank-one linear Artin–Schreier sheaf. It has no trivial geometric constituent, hence is nonexceptional relative to the trivial character, but its transform with trivial kernel is zero because its compactly supported cohomology vanishes (Laumon (1.1.3.4)). It therefore cannot have the asserted nonzero middle-extension transform.

The imported proof cited `lem-fd-base-change` for extension to the algebraic closure. Its current statement only permits morphisms of separated finite-type base schemes over the finite field; that citation does not justify this infinite extension. The Weil-pair definition already places the underlying object on the geometric fiber. Steps 2–4 forget the Frobenius structure and use the defining geometric integral transform, so no such extension theorem is needed. No coefficient categories are identified: all calculations use the rational/common-stage adic category in the existing definitions and package.

The old proof also used earlier H1–H3 without repeating them in each step's `uses`, left proper base change and the projection/composition identities unstated in the punctual calculation, and left the finite-support decomposition and ordinary open restriction uncited. These are repaired. I use the full final assertion of `thm-a1-fourier-t-exact`, which already includes mutually quasi-inverse exact equivalences; I do not separately reconstruct that theorem from weaker definitions. The optional converse about exceptional inputs is unnecessary for this proposition; the unit's converse also follows by applying that equivalence to the explicit inverse transform of a skyscraper.

## Existing-node and Mathlib searches

I searched the full DAG and blueprint with `blueprint_refs.py search` for `punctual`, `skyscraper`, `linear Artin`, `middle extension`, and `point category`, and ran `ancestor` for this item. I inspected the statements rather than importing dependencies from their proofs. The origin is this blueprint item; no other blueprint node states its complete assertion. The existing first-formula node only handles the origin, but the arbitrary-point calculation is three formulas from already stated six-functor identities, so it does not justify creating another node.

The actual Mathlib searches were LeanFinder for the Fourier–Deligne middle-extension statement, Loogle for `"fourierTransform", "Simple"`, whole-Mathlib grep for `Fourier.*Deligne|middleExtension|perverse`, LeanSearch with two distinct formulations, and an AlgebraicGeometry grep for `ArtinSchreier|artin.schreier|FourierDeligne`. I read their returned signatures: the semantic hits concern analytic Fourier transforms, general sheaf constructions, and concentration of derived objects. None states this geometric integral-transform assertion. The exact queries and results are retained in the log and node. No unavailable service was reported as a negative search.

## Not duplicates

No new nodes were created. All point, open–closed and six-functor facts were reused, and the simplicity-preservation and skyscraper calculations were written as short applications of their statements. In particular no new node restates the item or its punctual-exclusion clause.

## Review by NF

I read the main-20261015 statement and full proof file, the chapter and unit records, and the imported proof and audit. I checked the normalization in the local Laumon article: (1.2.1.1), (1.2.2.1)–(1.2.2.3), (1.2.2.9), and the translation formula (1.2.3.2). The proof remains an agent expansion of the blueprint, accurately marked as such. No new-node sources need review because there are no new nodes.

For Step 1, I opened `thm-a1-curve-perverse-heart`, `prop-a1-curve-perverse-simples`, and `thm-a1-fourier-t-exact`. The first explicitly includes the abelian Weil fixed-pair heart, not an asserted triangulated category of Weil pairs. The second says both that all middle extensions of irreducible lisse sheaves are simple and that every simple is punctual or a middle extension. The last explicitly supplies exact quasi-inverse equivalences, including the twist. The short subobject/quotient argument uses those precise assertions. Both affine lines meet the perfect-field smooth-curve assumptions; the input is nonzero irreducible lisse and the character is nontrivial.

For Step 2, `def-weil-weil-sheaf-complex` defines the faithful forgetful functor on geometric objects. `lem-a1-qbar-open-closed-cohomology` explicitly identifies the essential image of closed direct image with sheaves supported on the closed set. `lem-sf-point` (3) explicitly gives the point equivalence with bounded finite-dimensional coefficient complexes; for a sheaf it is a vector space in degree zero. Thus choosing bases on the finitely many components of the reduced support really gives the displayed direct sum. No Frobenius semisimplicity, rationality of the support over the finite base, or equivariant choice of bases is used.

For Step 3, I checked the actual clauses of `prop-functor-package`: proper base change applies to the point inclusion, proper shriek equals star for the graph inclusion, the projection formula moves the lisse kernel across that inclusion, and compact-support composition has the required identity equation. The four schemes and both projections are separated of finite type over the algebraic closure. The kernel is rank-one lisse and therefore a valid finite-Tor projection factor. `def-fd-kernel` states its pullback formula, and `lem-fd-as-characters` explicitly states the inverse-character/sign formula. Together with the defining shift in `def-fd-transform` these give the displayed inverse transform in three formulas. This is marked elementary relative to these already cited general identities, in accordance with the rule against creating a node for their short specialization. It is not justified merely by naming a definition.

For Step 4, the exact inverse equivalence supplies the initial isomorphism, and `def-fd-transform` supplies additivity through its underlying exact triangulated functor on geometric categories. I checked `def-wf-tate-twist` and wrote the compatible-root trivialization of its inverse limit; it is expressly geometric and need not respect Frobenius. The open restriction and cohomology are those of `lem-a1-qbar-open-closed-cohomology`, whose statement includes exactness and ordinary `j^*j_* = id`. `def-wf-middle-extension` makes the distinction from the derived direct image explicit. There is no lost higher-direct-image term because the input here is the ordinary middle-extension sheaf placed in degree minus one.

For Step 5, `lem-fd-as-characters` supplies rank one and lissity, and the constituent definition excludes every geometric parameter, including zero. A positive-rank summand is a constituent by its explicit inclusion and projection, so no unproved semisimplicity claim is needed. The classification node supplies exactly the final dense open and nonzero irreducible lisse Weil sheaf.

I checked B–E point by point: self-contained statement and explicit notions; no invented Mathlib searches; no new nodes to duplicate clauses; verbatim quotations rather than proof-only citations; no new cycles (server check); declared generic tools for off-unit statements; and no silent change to the unit route. The small cases checked are the origin (constant inverse transform with shift `[1]`), a nonzero geometric point (negative parameter for the inverse character), non-rational support (split only geometrically), arbitrary point-fiber dimension (multiplicities retained), and zero support (excluded by the inverse equivalence). All steps are under 2000 characters. I corrected the missing character hypothesis and the unsupported infinite base-change citation as described above.

The three off-unit tools are declared in `split_report.tool_uses`: `prop-functor-package`, `lem-sf-point`, and `lem-a1-qbar-open-closed-cohomology`. They implement the unit's specified punctual-exclusion argument; none replaces its route.

## Validation and unfinished work

The server-only `srvcheck.py` checks both passed: `check_dag` introduced no findings; `review_split` reported PASS, zero new nodes, and realization of the unit. No mathematics of this item is left to finish at stage 1. Existing cited dependencies remain their own DAG items; no claim is made that the library is already proved in Lean. The required final delivery dry run and push are performed after this report is written.
