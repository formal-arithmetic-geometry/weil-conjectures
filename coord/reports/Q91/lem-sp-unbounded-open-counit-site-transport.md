# Q91: lem-sp-unbounded-open-counit-site-transport

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-unbounded-open-counit-site-transport.json`: statement, split in eight steps. Not a Mathlib leaf: the search results give generic adjunction/localization APIs, not the specified geometric comparison and both actual adjunction maps.
- `citations.json`: fourteen step/node entries with verbatim excerpts checked against the cited statements.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox also retains the actual search log and the item-specific preparation script. No repository, launcher or Lean file was changed, and nothing was compiled.

## Attachments

None for this item. Searched the project Lean tree for its exact blueprint tag and for open counits, extension by zero and site comparison. The existing `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparisonUpperStarIso` in `lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/LowerShriekComparison.lean:88` defines the sheaf comparison; it does not state the complete unbounded theorem. The existing homotopy-adjunction declaration gives only the generic complexes/homotopy part, already attached to its own DAG node. The existing unit-normalization and bounded-below evaluation-counit nodes likewise do not give this entire item.

## WANTED

None. The blueprint, Stacks source and the relevant Mathlib localization source are present. There is no SGA citation or change of route.

## What was wrong and corrected

STATEMENT-DISPUTED: the final sentence referred to the fixed compact-support comparison without recording its domain. `def-sp-fixed-compact-support-comparison` explicitly defines it on bounded-below etale inputs, via the inclusion from D-plus into the unbounded category. Substituting an arbitrary complex with nonzero cohomology in arbitrarily negative degrees into that fixed natural transformation is ill-typed: that complex is not an object of its source D-plus. The final sentence now identifies the restriction of the unbounded open comparison with the fixed comparison on its actual domain, and says explicitly that the unbounded map extends it. The two displayed equations and all unbounded adjunction claims are unchanged. This is a domain correction, not an added constructibility, finite-Tor, quasi-compactness or Noetherian hypothesis.

The original node had no proof. Existing DAG nodes already supply the ringed-slice adjunction, its exactness, termwise/homotopy adjunction, localized adjunction and the sheaf comparison's canonical unit equation. Accordingly no clause was moved to a new node. The derived counit equation is proved explicitly by transposing both sides; the restricted-equivalence transport and the identity-proper-factor calculation are also written out.

The recorded Lean compact-support comparison file contains historical text about choosing a direct-image isomorphism. It is not used to replace the fixed definition's *specified counit mate* with an arbitrary isomorphism. Step 8 uses the named mate's statement in the DAG, which is the map required here.

## Unfinished work

No unfinished part of this split. Stage-2 formalization and proofs of existing supporting nodes remain their owners' work. Dry-run and delivery results are reported by the delivery command.

## Not duplicates

No new node pairs: no new nodes were created. Whole-DAG searches by 03DI, 03DJ, 09AF, localized/termwise adjunction, exact localization and open unit normalization found the existing tools used here. Whole-blueprint searches with `blueprint_refs.py search` for termwise adjunction, extension by zero and unit normalization did not identify an imported node stating this entire theorem. Its nearest imported ancestor is `det-sp-reduction-exceptional`, via `lem-sp-open-proetale-counit-scalar`; that provenance is retained.

## Review by Q91

I read the current reduction unit and chapter, and the current blueprint's exceptional-comparison proof, especially Locality: the adjunctions compose and the scalar comparison is compatible with open extension. This item makes that actual-adjunction input precise, without changing the chart or purity route. I read Stacks `sites-modules.tex`, `lemma-extension-by-zero` (03DI) and `lemma-extension-by-zero-exact` (03DJ), including the two Hom constructions; `proetale.tex`, `lemma-jshriek-comparison` (09AF), including the common-right-adjoint proof; and `derived.tex`, `lemma-right-derived-exact-functor` (015F) and the Hom adjunction used in `lemma-adjoint-preserve-K-injectives` (08BJ). I also read Mathlib's `CategoryTheory/Localization/Adjunction.lean:33` through its formulas at lines 118 and 125. These sources cover arbitrary unbounded complexes for exact functors, rather than a bounded-below resolution argument. The proof is marked agent because the explicit counit and localization assembly refines the blueprint and Stacks text.

For step 1 I checked that the cited etale adjunction statement explicitly describes the Hom transpose and evaluation counit, and that its exactness node includes the ordinary module category and quasi-isomorphism preservation. The unit's summand is indexed by the actual structure map V to U. It is not an assertion that the sheafified extension vanishes on every object which fails to factor through U; only the presheaf has that zero value.

For step 2 I checked the pro-etale localization node's topology, coefficient-ring restriction, and ordinary module categories, then the ringed-slice exact-adjunction statement. The latter gives exactness and the sheafified-sum extension; it does not by itself assert a normalized counit. I therefore wrote the inverse Hom constructions using the module-sheafification universal property, whose cited statement really gives unique factorization. Checking an arbitrary summand gives both inverse maps. During self-review I corrected an initially imprecise identity-summand description to the summand indexed by the given map V to U, and checked naturality using its actual restriction map.

For step 3 the termwise-adjunction statement explicitly supplies complex maps, Hom bijections, homotopy classes and their actual units/counits, with no boundedness condition in clauses (a) and (b). For step 4 the exact-functor node really supplies factorization for all complexes. The comparison definition supplies a finite-limit-preserving left adjoint on fixed-ring modules; being a left adjoint it also preserves finite colimits. The localization node supplies the actual unit/counit formulas and triangles. These citations justify descent, rather than treating the phrase 'localize the adjunction' as a proof.

For step 5 I read the entire existing unit-normalization statement and its recorded Lean definition: its comparison a is precisely the canonical pullback comparison after restriction identifications, and its c is the specified open comparison. Thus it gives the sheaf equation used here, with the same finite discrete ring and arbitrary open immersion. The cited localization universal property explicitly gives unique natural-transformation descent, composition compatibility and equality testing on localized representatives. This use requires no faithfulness of the localization on morphisms.

For step 6 I checked the types of both transposed maps: their common source is J-pro C-U U-et H after precomposing by e-inverse. Substituting the unit equation at U-et H cancels e-inverse with e; naturality of r at the etale counit then reduces the second transpose to r-H by the right triangle. The first transpose is r-H by the pro-etale right triangle. This proves compatibility of the actual evaluation counits without invoking a mere existence isomorphism or the bounded-below evaluation-counit node. Step 7 spells out all Hom identifications and the resulting transpose, so essential surjectivity and fullness identify the transported adjunction on the specified full subcategories, including its counit.

For step 8 I reread the fixed compact-support definition, the named direct-image-mate statement and the pullback comparison statement. The first limits the domain to bounded-below inputs; the second really defines its map by the counit transpose; the third includes identity coherence. For the identity proper factor the morphism is quasi-compact and quasi-separated even when X is neither quasi-compact nor Noetherian. In its identity functor identifications the mate is the identity; composing with the inverse open comparison therefore gives e-inverse in the fixed definition's orientation. No direct-image comparison for an arbitrary unbounded input is claimed.

I checked B--E of delivery-errors against this split: all objects and coefficient categories are fixed in the statement, every non-elementary external input has a node whose statement was read, there are no new statement-only or duplicate nodes to audit, no dependency on the parent counit-scalar lemma was introduced, and the non-elementary steps are all under 2000 characters. The pure categorical calculations are elementary steps with their actual formulas. I tested j equal to the identity, U empty (including the empty-site sheafification), the zero ring, and complexes unbounded in both directions. The formulas reduce to identities or zero maps as appropriate; no stalk-conservativity or finite-amplitude argument is used. Off-unit generic tools are declared in `split_report.tool_uses`, with their purpose; none replaces the unit's route. Every citation excerpt was checked as a literal substring of the current dependency statement.
