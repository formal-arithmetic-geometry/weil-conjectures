# Q93 stage-1 report: sk-prop-sf-rf-shriek-preservation

## Files written

- `dag/nodes/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation.json` — split item, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sf-open-tor-bound-arbitrary-field.json` — statement-only node, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sf-closed-support-tor-bound.json` — statement-only node, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sf-affine-chart-factorization-gluing.json` — statement-only node, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sf-module-object-ordinary-coefficient-equivalence.json` — statement-only node, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sf-etale-proetale-exceptional-transport.json` — statement-only node, no Mathlib match.
- `citations.json` — 61 step/node verbatim statement quotes.
- `searches.jsonl` — the item searches recorded by `msearch.py`.

## Attachments

- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion` belongs to `sk-prop-sf-rf-shriek-preservation` (`WeilConjectures/SixFunctors/Etale/Derived/Stability/OpenImmersion.lean:195`).
- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isFinite_of_etale` belongs to `sk-prop-sf-rf-shriek-preservation` (`WeilConjectures/SixFunctors/Etale/Derived/Stability/Basic.lean:131`).
- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion` belongs to `sk-prop-sf-rf-shriek-preservation` (`WeilConjectures/SixFunctors/Etale/Derived/Stability/UpperShriek.lean:58`).
- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension` belongs to `sk-prop-sf-rf-shriek-preservation` (`WeilConjectures/SixFunctors/Etale/Derived/Stability/UpperShriek.lean:123`).
- `AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek` belongs to `sk-prop-sf-rf-shriek-preservation` (`WeilConjectures/SixFunctors/Etale/Derived/Stability/UpperShriek.lean:322`).

## WANTED

None. The proof follows the current main-20261015 blueprint proof document and the cited Stacks/Zheng inputs already represented in the DAG.

## Not duplicates

- `lem-sf-open-tor-bound-arbitrary-field` vs `det-cor-sf-direct-image-ctf-open-tor`: the existing node assumes a separably closed field and states a pro-étale comparison; this node proves the arbitrary-field finite-constant-to-all-module stalk/filtered-union passage used here.
- `lem-sf-closed-support-tor-bound` vs `lem-exc-closed-amplitude`: the existing node is an amplitude criterion for a closed right adjoint; this node is the explicit Tor triangle calculation giving the additional upper endpoint (+1).
- `lem-sf-affine-chart-factorization-gluing` vs `lem-weil-pbc-lft-affine-pairs`: the existing Mathlib leaf characterizes finite-type ring maps; this node adds the closed immersion into affine space, finite-cover local bounds, and constructibility gluing.
- `lem-sf-module-object-ordinary-coefficient-equivalence` vs `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: the existing node defines the section-action equivalence; this node states its finite discrete coefficient, derived tensor, localizing-closure, and compact-support consequences.
- `lem-sf-etale-proetale-exceptional-transport` vs `lem-exc-comparison-tor-interval`: the existing node compares Tor intervals; this node transports the ordinary exceptional adjunction and the compact-support composite across the site comparison.
- `lem-sf-etale-proetale-exceptional-transport` vs `lem-sf-constructible-exceptional-adjunction-coefficients`: the existing unsplit node is the broader coefficient-stage adjunction statement; this node is the finite-ring étale-to-pro-étale transport lemma used in this proof and does not assume the target preservation result.

## What was wrong or repaired

The prior delivery was returned because steps 3, 7, and 8 were longer than 2000 characters and carried independent lemmas inline. I kept the arbitrary-field statement and its route, created five statement-only nodes for those hidden arguments, and replaced the three long steps by short cited applications. The finite-constant-to-all-module argument and the support-triangle (+1) calculation are now separate nodes; chart factorization/gluing, coefficient equivalence, and étale/pro-étale transport are also separately named. No SGA 4 or SGA 4½ source is used. The item statement remains the repaired arbitrary-field statement with explicit section-action and derived-category identifications.

## Review by Q93

I read the item node, `dag/chapters/sec-six-functors-basics.json`, and `dag/units/sk-prop-sf-rf-shriek-preservation.json`, then checked the source declarations and docstrings in `WeilConjectures/SixFunctors/Etale/Derived/Stability/Basic.lean`, `OpenImmersion.lean`, `UpperShriek.lean`, and `UpperShriekConstructible.lean`. The five declarations listed under Attachments are sorry-free and cover the corresponding finite étale, open, closed, smooth, and dimension-free clauses; no single declaration states the whole item, so the item is split.

Step 1 uses the finite-type/Noetherian, compactification, ordinary adjoint, geometric-stalk, pullback exactness, and open-immersion nodes exactly for the hypotheses stated there; it also checks the zero-ring and empty-scheme cases. Step 2 verifies the complementary open is quasi-compact and finite type, uses relative cohomological dimension over an arbitrary field, ordinary direct-image constructibility, the closed-amplitude criterion, and exact finite direct image; the cited nodes state each of these inputs. Step 3 now cites `lem-sf-open-tor-bound-arbitrary-field` for the finite-constant projection and stalk/filtered-union passage, and `lem-sf-closed-support-tor-bound` for the support triangle and the (+1) upper endpoint; their statements contain exactly those conclusions. Steps 4 and 11 use the unoriented smooth tensor formula and local rank-one Tate line, with shifts and Tor intervals checked at geometric stalks and no global orientation claimed.

Step 5 spells out the Hom chain for an affine chart and uses compact-support composition only on bounded-below inputs. Step 6 proves the bounded-below representing-object test by brutal lower tails and the telescope triangle, with the cited hocolim and triangulated-category statements. Step 7 now cites `lem-sf-affine-chart-factorization-gluing` for finite affine charts, closed-immersion/affine-space factorization, and finite-cover gluing; the chart locality comparison and steps 2–4 provide the local exceptional bounds. Step 8 cites `lem-sf-module-object-ordinary-coefficient-equivalence` and `lem-sf-etale-proetale-exceptional-transport` for the coefficient-category identification, derived tensor/localizing closure, and transport of the ordinary exceptional adjunction; the Tor and open-extension comparison nodes supply their stated comparisons. Step 9 checks the counit transpose, all shifted Hom tests, and closure under arbitrary sums in the localizing category, so the representing map is an isomorphism. Step 10 restricts the already established natural adjunction bijections to the full finite-Tor constructible subcategories. All hypotheses, including (p\ne\ell), separatedness, quasi-compactness, finite coefficient exponent, and the same compactification, were checked where used.

I reran the required Mathlib searches for the item and all five new nodes (LeanFinder, Loogle, grep, and LeanSearch); the logs record the actual hits and parser/unknown-identifier outcomes. Every new node is statement-only and unsplit, carries its blueprint ancestry, and has no Mathlib match. The item proof dependencies equal the union of the step uses, and `citations.json` quotes the complete statement of every cited node for each step. No additional source or compiler work was needed or performed.
