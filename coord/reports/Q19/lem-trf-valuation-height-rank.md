## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-height-rank.json` — repaired item split; two non-elementary inputs are cited.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-prime-convex-correspondence.json` — statement-only node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-convex-chain-rational-rank.json` — statement-only node; no Mathlib match.
- `citations.json` — verbatim quotations for every non-elementary step citation.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the upstream master for the item tag and its exact valuation-chain statement found no finished project declaration.

## WANTED

WANTED: the archival copy `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf` is absent. I read the author’s v3 PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, including §2.1 pp. 7–8, and therefore retained agent proof origin while recording the missing local archive.

## Not duplicates

- `lem-trf-valuation-height-rank` vs `lem-trf-abhyankar-finite-type-field-height`: the former bounds a chain in one valuation ring by its value-group rational rank; the latter bounds valuations of finitely generated fields by absolute transcendence degree plus one and uses this item, so citing it here would create a cycle.
- `lem-trf-valuation-height-rank` vs `lem-trf-valuation-algebraic-height`: the existing node compares prime chains under algebraic field extension; it does not give the single-valuation convex-subgroup/rational-rank bound.
- `lem-trf-valuation-prime-convex-correspondence` vs `lem-trf-valuation-algebraic-height`: the new node identifies primes with convex subgroups for one valuation ring; the existing node concerns restriction across an algebraic extension.
- `lem-trf-convex-chain-rational-rank` vs `lem-trf-abhyankar-inequality`: the existing node is the relative residue-transcendence Abhyankar inequality; the new node is the ordered-group convex-chain consequence used after the prime/convex correspondence.
- `lem-trf-convex-chain-rational-rank` vs `lem-trf-prime-field-valuation-rank`: the existing node bounds the rational rank of a valuation on a prime field; the new node applies to arbitrary totally ordered abelian groups.

- `lem-trf-convex-chain-rational-rank` vs `lem-trf-valuation-height-rank`: the child concerns only arbitrary totally ordered abelian groups and convex-subgroup chains; the item starts from a valuation ring and concludes a prime-chain bound.
- `lem-trf-convex-chain-rational-rank` vs `def-trf-modification`: the child is an ordered-group inequality; the existing definition is the geometric notion of a proper birational modification.
- `lem-trf-convex-chain-rational-rank` vs `def-trf-multipointed-curve-modification`: the child has no curves or modifications; the existing definition concerns morphisms and stability of multipointed curves.
- `lem-trf-convex-chain-rational-rank` vs `def-trf-multipointed-curve`: the child is an ordered-group statement; the existing definition introduces relative curves and markings.
- `lem-trf-convex-chain-rational-rank` vs `def-trf-rational-rank`: the existing node only defines rational rank; the child proves the strict convex-chain inequality.
- `lem-trf-convex-chain-rational-rank` vs `def-trf-schematically-dense-open`: the child concerns convex subgroups; the existing definition concerns injectivity on sections for dense opens.
- `lem-trf-convex-chain-rational-rank` vs `def-trf-semistable-multipointed-pair`: the child is purely ordered-group theory; the existing definition concerns semistable marked geometric fibres.
- `lem-trf-convex-chain-rational-rank` vs `def-trf-strict-semistable-curve`: the child has no schemes or local charts; the existing definition is the strict semistable curve chart condition.
- `lem-trf-convex-chain-rational-rank` vs `def-trf-strictly-semistable-curve`: the child is an ordered-group inequality; the existing definition concerns local nodal charts of a relative curve.
- `lem-trf-convex-chain-rational-rank` vs `lem-trf-abhyankar-finite-type-field-height`: the latter specializes to finitely generated fields and concludes a transcendence-degree height bound, while the child is the general ordered-group sublemma it uses indirectly.
- `lem-trf-convex-chain-rational-rank` vs `lem-trf-base-modification-comparison-fibre-image`: the child concerns convex subgroups and rational rank; the existing node concerns proper geometric comparison after a base modification.
- `lem-trf-convex-chain-rational-rank` vs `lem-trf-abhyankar-inequality`: the existing node bounds relative value-group rank plus residue transcendence degree by field transcendence degree; the child bounds chains of convex subgroups in an arbitrary ordered group.
- `lem-trf-valuation-prime-convex-correspondence` vs `lem-trf-valuation-height-rank`: the child gives only the prime/convex correspondence; the item additionally derives the numerical prime-chain inequality.
- `lem-trf-valuation-prime-convex-correspondence` vs `def-trf-modification`: the child is valuation theory; the existing definition is proper birational geometry.
- `lem-trf-valuation-prime-convex-correspondence` vs `def-trf-multipointed-curve-modification`: the child has no curves or modifications; the existing definition concerns morphisms and stability of multipointed curves.
- `lem-trf-valuation-prime-convex-correspondence` vs `def-trf-multipointed-curve`: the child identifies primes and convex subgroups; the existing definition introduces flat finitely presented relative curves and markings.
- `lem-trf-valuation-prime-convex-correspondence` vs `def-trf-rational-rank`: the existing node defines rational rank only; the child identifies prime ideals with convex subgroups for a valuation ring.
- `lem-trf-valuation-prime-convex-correspondence` vs `def-trf-schematically-dense-open`: the child is valuation-ring order theory; the existing definition concerns schematically dense open immersions.
- `lem-trf-valuation-prime-convex-correspondence` vs `def-trf-semistable-multipointed-pair`: the child has no semistable curves or geometric fibres; the existing definition concerns marked semistable pairs.
- `lem-trf-valuation-prime-convex-correspondence` vs `def-trf-strict-semistable-curve`: the child is about valuation primes; the existing node defines etale local polynomial/nodal charts.
- `lem-trf-valuation-prime-convex-correspondence` vs `def-trf-strictly-semistable-curve`: the child has no relative curve charts; the existing definition is a local strict semistability condition.
- `lem-trf-valuation-prime-convex-correspondence` vs `lem-trf-abhyankar-finite-type-field-height`: the latter concludes a finite transcendence-degree height bound and uses the item; the child supplies only the single-valuation prime/convex correspondence.
- `lem-trf-valuation-prime-convex-correspondence` vs `lem-trf-base-modification-comparison-fibre-image`: the child concerns valuation ideals and ordered groups; the existing node concerns images of proper comparison fibres after modifying a base.
- `lem-trf-valuation-prime-convex-correspondence` vs `lem-trf-abhyankar-inequality`: the existing node is the relative Abhyankar numerical inequality; the child is the separate prime-spectrum/convex-subgroup correspondence.


## What was wrong and what changed

The returned packet said that Temkin’s source was unread and retained “local document copy unavailable” in the item, proof steps, and both child nodes. I repaired this by reading the online v3 PDF. On p. 7 (PDF text lines 401–416), Temkin states the correspondence between points of the valuation-ring spectrum, overrings, and convex subgroups of the value group; lines 417–436 define height/convex rank. On p. 8 (lines 480–495), I read the definitions of value-group rational rank, Lemma 2.1.2 (the Abhyankar inequality), and Corollary 2.1.3(i). The item’s chain inequality is the elementary ordered-group consequence of the convex-subgroup correspondence and rational-rank definition; the two child statements isolate exactly those inputs. The local PDF remains WANTED because the standing rules forbid downloading it.

The item’s creation record incorrectly named the earlier NY item `lem-trf-abhyankar-finite-type-field-height`; it now records `created.item = lem-trf-valuation-height-rank` and `group = Q19`. Its historical blueprint ancestry remains under `lem-trf-local-term-locality` and now has the item itself prepended to `blueprint.from.via`, as required for a created node. The unit record `sk-i-curve-zero` is not edited: this is an auxiliary valuation input below the unit’s realized key node `lem-trf-local-term-locality`, and the unit’s existing `realized` fields already correctly identify that key statement and its two route steps. No chapter or unit statement is changed.

## Review by Q19

I reread the current shared item, the retained sandbox item and both child statements, then compared every hypothesis and conclusion with Temkin §2.1. The valuation-ring alternative and quotient order in item Step 1 are elementary. Step 2 cites the full statement of `lem-trf-valuation-prime-convex-correspondence`, which supplies the prime/convex correspondence and preserves the number of strict inclusions. Step 3 cites the full statement of `lem-trf-convex-chain-rational-rank`, whose hypotheses are exactly the totally ordered value group and the strict convex-subgroup chain produced by Step 2, and whose conclusion is the required rational-rank inequality. The source check covered the p. 7 correspondence and height discussion and the p. 8 Lemma 2.1.2/Corollary 2.1.3(i) passages; the source places in all three node records now say this explicitly and give the online URL.

I checked the edge cases (n=0), the trivial valuation with Γ=0, a rank-one group such as ℤ, and lexicographic ℤ². I also checked that the child statements are strictly smaller than the item and do not restate its conclusion, that their Mathlib searches are actual recorded no-match searches, and that `citations.json` quotes literal substrings of the cited statements. The item’s `proof_deps` is the union of its two non-elementary uses. No source hypothesis was added or dropped, and no unit realized field was changed.

## What could not be finished

The local Temkin archive is still absent, so the WANTED request remains open. No Lean was written and no compiler, Lake, build, or local DAG checker was run.
