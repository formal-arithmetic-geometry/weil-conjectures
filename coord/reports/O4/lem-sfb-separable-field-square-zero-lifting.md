# O4 stage-1 report: lem-sfb-separable-field-square-zero-lifting

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-separable-field-square-zero-lifting.json`: statement, split; full arbitrary separable extension retained, with four proof steps.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-separably-generated-field-h1-zero.json`: statement, Mathlib leaf; separating transcendence basis implies zero first cotangent homology.
   - `citations.json`: a verbatim statement quote for every citation of every item proof step.
   - `searches.jsonl`: actual msearch records, four searches for the item and four for the new leaf.
2. Attachments: none. Searches of `lean/WeilConjectures/` by the item's blueprint tag and by separability, formal smoothness, lifting, and homology found no declaration stating the whole item. The existing finite-subfield homology theorem is reused as a dependency, not claimed as an attachment of the item.
3. WANTED: none.
4. Issues found: the imported statement is correct and unchanged. The crucial distinction is between separability of an arbitrary extension and existence of a separating transcendence basis of the entire extension. The latter alone is covered directly by Mathlib's field smoothness result. LeanSearch's index advertises an `EssFiniteType` hypothesis for that result, but the pinned local `Smooth/Field.lean:44-51` and Loogle's signature have no such hypothesis; the leaf follows the local file. No hypothetical finiteness or algebraicity assumption was added to the item.
5. Unfinished mathematics: none at this split level. The new node is a Mathlib leaf, so there is no new unsplit task.

## Sources and route

Read Stacks `algebra.tex`, Tag 0322 (`proposition-characterize-separable-field-extensions`), Tag 0320 (`lemma-formally-smooth-extensions-easy`, the complete proof, especially (3)), Tag 031Z (`lemma-characterize-formally-smooth-field-extension`), Tag 07BQ (`lemma-colimits-NL`), and Tag 031J (`proposition-characterize-formally-smooth`, including (6) implies (1)). Read `fields.tex`, Tag 09FN (`lemma-vector-space-is-free`) and its following splitting argument. Verified tag/label correspondence in `literature/stacks-project/tags/tags`.

Read the chapter and unit records and the latest blueprint's `det-thm-sf-ctf-stability-direct-images` statement and proof. This item supports proof (3) through its inherited alteration/deformation prerequisites, where the arbitrary separable residue-field lifting input occurs in 07EJ and 0C34. The Stacks homology proof preserves that route. The unit itself is not this item and its realization fields were not edited.

`python3 tools/blueprint_refs.py ancestor lem-sfb-separable-field-square-zero-lifting` returns `None`: following `created.item` reaches `Sheaf.SixFunctors.CtfStabilityDirectImages`, a declaration identifier rather than a DAG node, although the inherited descriptive provenance names the actual blueprint node. The new node therefore records the command's null `from.node`, inherits the exact explanatory `from.place`, and prepends the item to `via`, as prescribed. This is a pre-existing provenance-chain gap, not a mathematical gap. Searches of the whole blueprint for `separable field`, `separably generated`, `0320`, `031Z`, `lifting field`, `differentials`, and `cotangent`, together with whole-DAG tag, keyword and declaration searches, found no blueprint node with the new statement. Both `same_as` fields are `[]`.

## Not duplicates

lem-sfb-separably-generated-field-h1-zero vs lem-weil-pbc-h1-cotangent-finite-subfields: the new leaf proves vanishing for a separably generated extension; the existing lemma assumes vanishing on every finitely generated intermediate field and passes it to the full extension. These are the input and the passage-to-union steps, respectively.

lem-sfb-separably-generated-field-h1-zero vs lem-weil-pbc-popescu-artinian-flat-subalgebras: the existing result constructs directed Artinian flat subalgebras from a finite-dimensional homology hypothesis; it does not assert zero homology for a separably generated field.

lem-sfb-separably-generated-field-h1-zero vs lem-weil-pbc-vector-space-projective: the existing leaf asserts projectivity of arbitrary vector spaces and says nothing about cotangent homology or separable generation.

lem-sfb-separably-generated-field-h1-zero vs lem-weil-pbc-field-char-p-nilpotent-lifting: the existing result lifts ring maps from fields of characteristic p across nilpotent ideals in characteristic-p rings, so it is over the prime field; it does not impose or preserve a specified possibly imperfect base field k. The new leaf has arbitrary k and a homology conclusion.

Additional nearby statements checked: `lem-weil-pbc-char-zero-field-extension-formally-smooth` assumes characteristic zero; `lem-kun-fg-separable-smooth` and `lem-kun-algebraic-separable-smooth` describe filtered unions of smooth algebras; `lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra` assumes finite generation and constructs a smooth subalgebra; `lem-weil-pbc-separable-residue-cotangent-injective` proves injectivity of a local-ring conormal map. None states the new homology assertion. The leaf is a restricted homology input, not a renamed copy of the item's lifting conclusion.

## Review by O4

I checked the statement against 0322 and followed the complete proof of 0320 (3). Its essential point is to pass through cotangent homology; it does not assert that separately chosen lifts on finitely generated fields glue. The new leaf is the separating-basis input to that proof. Reading 0320 (1), (2), and their composition in (3), with the equivalence in 031Z, gives exactly its statement. I also read Mathlib `Smooth/Field.lean:44-51` and `Smooth/Basic.lean:69-75`: the algebraic independence plus separable algebraic hypothesis gives formal smoothness, whose named class projection is precisely vanishing of the canonical first cotangent homology. No comparison theorem or finite-type hypothesis is hidden in the match.

For step 1 I opened `def-weil-pbc-separable-field-extension`: clause (2) supplies separable generation of each finitely generated intermediate field, and clause (1) supplies its separating basis. The new leaf then states exactly the required vanishing, with no characteristic condition. This is instantiation of those statements, not an extra assertion that L itself has a separating basis.

For step 2 I opened `lem-weil-pbc-h1-cotangent-finite-subfields`. Its hypothesis quantifies over exactly the intermediate fields treated in step 1; its conclusion is precisely H_1(L_{L/k})=0. I also read its project Lean declaration and the finite-support proof, and the source 07BQ. This generic off-unit tool is declared in `split_report.tool_uses`; it does not replace any unit-level route.

For step 3 I opened `def-weil-pbc-kahler-differentials`, which explicitly defines Omega as an L-module, and `lem-weil-pbc-vector-space-projective`, which applies to every module over a field, not just finite-dimensional ones. Thus its hypotheses hold for Omega_{L/k}, even when this vector space has infinite dimension. This agrees with the actual proof of 031Z.

For step 4 I opened `lem-weil-pbc-smooth-ring-map-square-zero-lifting`. Despite its title, its statement requires only zero H_1 and projective Omega, with no finite presentation assumption. Steps 2 and 3 provide exactly those hypotheses. I opened `def-weil-pbc-algebra-hom-quotient`, which supplies the k-algebra quotient and the given quotient map. Substitution A=k, B=L, N=J therefore gives the requested k-linear lift, rather than merely a ring lift. The source is 031J (6) implies (1).

I tested E=k (empty separating basis and zero homology), purely transcendental extensions with arbitrary basis cardinality, separable algebraic extensions (empty basis), and mixed separably generated extensions. All satisfy the new leaf. For an imperfect base k=F_p(s), the purely inseparable extension obtained by adjoining a p-th root of s has no separating transcendence basis and is correctly excluded; it would obstruct lifting to k[X]/((X^p-s)^2), so dropping the separability hypothesis would be false. For the item I checked J=0 and the zero test ring; neither needs exclusion. No source or statement dispute was found.

Against delivery-errors B--E: the sole new node is self-contained, has definition dependencies, has single-escaped TeX, and has no proof or proof-dependency list beyond the empty fields required for a leaf. Every search in it is an actual msearch query in the log, with its result read and its match checked locally; no service was marked absent on an unavailable answer. The source overlaps are distinguished above. Each non-elementary step cites the statements it uses, and `citations.json` copies those statements verbatim. There are no elementary placeholder claims, cycles introduced by a new lemma depending on its user, inline identifications, or long steps over 2000 characters. The item was not moved into a single new node: the four steps assemble the restricted homology input, passage to arbitrary unions, projectivity, and lifting. The full characteristic-free, non-algebraic statement is retained. I corrected the possible search-index/version mismatch in the verdict rather than changing the mathematics. No Lean file was written and no compiler or build command was run.
