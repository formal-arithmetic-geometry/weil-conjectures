# Stage-1 report: lem-trf-functorial-fan-desingularization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-functorial-fan-desingularization.json`: the item, split into five source-based proof steps; statement unchanged.
- `dag/nodes/sec-trace-formula/def-trf-monoscheme-toric-realization.json`: definition, unsplit; no Mathlib match for the full monoscheme/toric-tower vocabulary.
- `dag/nodes/sec-trace-formula/lem-trf-toric-normalized-desingularization.json`: statement only, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-toric-monoid-comparison.json`: statement only, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-sharpening-fan-bijection.json`: statement only, unsplit; no Mathlib match.

The three new statements have empty `proof` and `proof_deps`, and null `proof_origin`. `citations.json` records a verbatim statement excerpt for every step/node citation. All five proof steps are under 2000 characters.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact item tag/id and the notions monoscheme, Kato fan, toric desingularization, torus-equivariant centers and saturated blowups. There is no matching project declaration. The read-only upstream master tree likewise gives no exact item declaration; its sorry declarations were not treated as completed proofs.

## WANTED

None. The ILO PDF is present in `literature/` and was read directly; the required inputs are explicitly stated there. These fan/monoscheme theorems have no Stacks tags; the sources therefore give the exact ILO theorem/lemma numbers and printed pages. No SGA source is used.

## Problems and limits

The imported item had an empty proof and only its definition dependency. Its statement is retained. The construction must work for fine torsion-free monoids, not just saturated ones, and for fans which have no global monoscheme lift. The new proof respects both distinctions. It fixes the toric algorithm once, descends its actual ideal centers inductively, and transfers the resulting rule through sharpening; it does not choose unrelated resolutions on affine charts.

The item's maintainer-owned unit and historical blueprint ancestry are retained. This is an auxiliary of the historical nearby-duality/alteration branch of `lem-trf-local-term-locality`, via the listed created-item chain; the current normal-cone proof of the unit is not changed. No unit realization field is touched, because this item is not the unit's key node.

Nothing mathematical is left unfinished at this one-level split. The new unsplit facts are queued as such, rather than assigned provisional proofs.

## Not duplicates

- def-trf-monoscheme-toric-realization vs def-trf-fine-fan-blowup: the existing node defines sharp fans and their blowups; the new node defines unsharpened monoschemes, the extra group factor in smoothness, monoid-algebra realization, torus action and normalized scheme towers. It uses the existing monoid and fan vocabulary by citation.
- lem-trf-toric-normalized-desingularization vs lem-trf-functorial-fan-desingularization: the new node is a characteristic-zero algorithm on schemes with torus-equivariant ring-ideal centers; the item constructs saturated fan towers from it. Scheme-to-monoid descent and sharpening remain real arguments.
- lem-trf-toric-normalized-desingularization vs lem-trf-monoidal-resolution-tower: the existing theorem is about saturated log blowups of arbitrary fs log schemes; it depends on the item and cannot supply the independent toric scheme algorithm.
- lem-trf-toric-monoid-comparison vs lem-trf-log-regular-toric-refinement: the existing lemma preserves log regularity after a specific saturated toric chart extension of a log scheme. The new node characterizes torus-equivariant ring ideals, identifies normalized toric blowups with saturated monoscheme blowups, and compares smoothness; it makes no log-regularity assumption.
- lem-trf-toric-monoid-comparison vs lem-trf-fs-face-sharpening: that node only describes units and the sharp quotient of a localization of an fs monoid. It gives neither equivariant ideals nor toric blowup comparisons or the regular-toric-scheme criterion.
- lem-trf-sharpening-fan-bijection vs def-trf-fine-fan-blowup: the existing node defines fan towers but does not identify them with monoscheme towers or transfer a functorial rule across finite affine covers.
- lem-trf-sharpening-fan-bijection vs lem-trf-functorial-log-blowup-etale-descent: that node concerns descent of prescribed log-scheme towers across strict étale charts. The new node concerns sharp monoidal spaces, the ideal/tower bijection under sharpening, and affine fan synchronization, including fans having no global monoscheme lift.

## Research and searches

Read the whole-DAG statement/title results for monoscheme, Kato fan, toric, desingularization and sharpening, and the relevant existing nodes above. Whole-blueprint searches for `monoscheme`, `toric`, `desingularization`, `monoidal space`, `toric monoid comparison`, `blowup sharpening`, and the earlier full statement phrasings returned no matching blueprint theorem. The only nearby existing sharp-monoid result is the face-localization lemma, whose statement was opened and compared. The exact blueprint ancestor was checked with `tools/blueprint_refs.py ancestor`.

For every final new node, ran LeanFinder and LeanSearch with two different phrasings, Loogle, and the Mathlib source grep through the required `msearch.py N8 lem-trf-functorial-fan-desingularization ...` command. The new node's id prefixes the semantic queries so the intended statement is visible in the log. The node records reproduce the exact queries and full returned output, also retained in `node-search-results.json` and `searches.jsonl`. Loogle's actual final searches returned zero hits except `"MonoidAlgebra"`, which returned ordinary monoid-algebra declarations, not the comparison theorem. Grep found no toric desingularization, monoscheme or fan blowup implementation; the definition grep's four hits are about Cartesian monoid schemes represented by bialgebras, a different object. Read Mathlib/AlgebraicGeometry/Group/Affine.lean around lines 140--175 and Mathlib/AlgebraicGeometry/Normalization.lean around lines 120--140: these define affine monoid schemes and relative normalization, respectively, and do not provide any one-line specialization to these nodes. All search services used for the final records responded; no unavailable response is misreported as a negative match.

## Review by N8

I read ILO Exposé VIII §§2.2.1–2.2.12, §§2.3.1–2.3.17, §§3.1.3–3.1.29 and §§3.2.1–3.2.21. The decisive source is the construction in §3.2.19, printed p.106: the normalized algorithm's torus-equivariant ideal is monoidal by Lemma 3.2.15; its normalized blowup is the realization of a saturated monoscheme blowup by Corollary 3.2.18; this repeats inductively. Theorem 3.1.27 then transfers the rule to fans. I checked each new node against those passages: the definition follows §§3.1.3–3.1.22 and 3.2.2/3.2.14; the toric algorithm follows Theorem 2.3.10, Remark 2.3.12 and Corollary 2.3.17; the comparison packages Lemmas 3.2.9, 3.2.12, 3.2.15, 3.2.17 and Corollary 3.2.18; the sharpening correspondence is Lemma 3.1.25 and Theorem 3.1.27, with the finite-disjoint-union synchronization in §3.1.26 referring to Remark 2.3.5(ii). I read Remark 3.2.21 as a compatibility statement, not as an independent existence proof.

Step 1 cites the definition for the domain and the algorithm theorem for a single rule on that whole domain, so the choices can be synchronized. In Step 2 I checked that the cited algorithm really supplies equivariant centers at every stage; that the comparison really supplies unique monoid ideals, the normalized/saturated blowup identification, the same torus, and finite fine torsion-free output; and that nowhere density rules out the zero ideal on any component. Its inductive assertion starts at M_0=M, and each application constructs M_{i+1}, so no induction hypothesis is borrowed from a later stage. The empty-center scheme case corresponds to the unit monoid ideal, not to an empty monoid ideal.

Step 3 uses the algorithm's terminal regularity and the comparison's explicit regular-over-Q criterion, not smoothness reflection over an arbitrary imperfect field. It uses smoothness preservation to apply the scheme algorithm to a smooth monoscheme map, and uses the ideal bijection's pullback compatibility and injectivity to identify actual centers, rather than just the endpoints of blowups. The comparison explicitly identifies a unit ring ideal with the whole monoid sheaf, so the contractions match. Step 4 verifies identities/composition by those same uniquely determined ideals and canonical saturated-blowup maps, writing out what compatibility means for the ordered surviving subsequence. The definition supplies the universal-property interpretation; no unstated descent theorem is invoked in this step. Step 5 uses the sharpening node's stated rule bijection and finite-cover synchronization, rather than assuming the whole fan lifts to a monoscheme. Finally, the fan definition makes all three listed special kinds of morphisms smooth on stalks with r=0, so the all-smooth comparison includes them. I checked that each cited node's statement, not its proof or just its title, contains everything the step uses, and recorded verbatim excerpts in citations.json.

For small cases, I checked the zero monoid and the empty fan (zero-length resolution is permitted), smooth orthant fans (the trivial rule locally fits the definitions), a monoid which is fine but not saturated such as the additive monoid generated by 2 and 3 (normalization/saturation must genuinely be present), ideals on a torus (the only invariant ideals are zero and the unit ideal), a center missing one disjoint-union component (the ideal on that component is the whole sheaf), and a fan formed by gluing affine fans only at their generic points (there is no assumed global monoscheme lift). The comparison permits empty monoid ideals only for describing the zero ring ideal; the constructed tower never uses them. These checks prompted me to retain the full fine torsion-free domain, to state the torus action and pullback compatibility explicitly, and to use the existing finite-cover content of the sharpening theorem instead of manufacturing a separate finite-cover lemma. No new node is an elementary consequence or a restated clause of the item: the definition introduces new objects, the algorithm is a scheme theorem, the comparison is the algebraic descent input, and sharpening is a generic correspondence independent of the existence of a resolution.

The first full server preflight found a citation-parser format issue in the sharpening statement: two ids shared one bracket. I changed them to separate bracketed node citations and refreshed the exact quote; no mathematical statement changed.
