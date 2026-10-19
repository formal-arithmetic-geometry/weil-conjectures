# Worker report: def-finrepair-property-c

## Files written

- `dag/nodes/sec-smooth-purity/def-finrepair-property-c.json`: definition; split using its four existing statement dependencies; Mathlib searches found no exact definition. No new nodes and no Mathlib leaves.
- `citations.json`: empty list, because a definition has no proof steps.
- `searches.jsonl`: actual msearch.py search log; six searches, including the second semantic phrasing and second grep.

## Attachments

None. Searching WeilConjectures/ in the slopmaster2 checkout for the blueprint id gives no declaration. Concept searches found `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_finite` (SixFunctors/Etale/Derived/Stability/DirectImage.lean:113) and `AlgebraicGeometry.ProEtale.ctfLowerStar` (SixFunctors/ProEtale/TraceFormula/Defs.lean:226). I opened both: the former is a theorem about bounded constructible complexes, and the latter is a functor on the pro-etale finite-Tor subcategory assuming its preservation hypothesis. Neither defines this predicate on higher direct images of arbitrary constructible finite-coefficient sheaves. No attachment is claimed; upstream master is reference material only.

## Wanted sources

None. The source of the definition and all four dependency statements are available.

## Findings and changes

Read the chapter record sec-smooth-purity and unit sk-prop-sf-cbc, including its master _section.md. This item is an auxiliary definition, not the unit's key statement. No unit realization fields are changed. The imported statement agrees verbatim with its master node source; its proof is correctly empty. The four dependencies are all needed, and each already supplies the named notion. Kept the source, statement, dependencies, audit, and import flags unchanged; set status to split, recorded real Mathlib searches, filled blueprint.same_as with [], and supplied split_report.

The definition uses the source's finite-type scheme convention (finite type of the structure morphism when working over a field); it is not a theorem imposing an unmentioned finiteness hypothesis on f. The predicate can be evaluated for any such f without assuming properness, separatedness, or that the predicate holds. No stronger assertion about boundedness is hidden in it.

Blueprint searches `constructibility under direct image`, `finrepair-property-c`, `R^qf`, and `C(f)`, and whole-DAG keyword searches were read. The finrepair composition, cancellation, modification and projective nodes USE this predicate and do not duplicate its definition. Constructibility theorems and uniform-vanishing definitions have different statements. There is no other blueprint node defining exactly this predicate, so same_as is empty. Since no nodes are created there are no duplicate pairs to distinguish.

## Unfinished work

None for this one-level definition split. Its existing dependency nodes retain their own states. No Lean was written, and no compiler or Lake tool was run. Delivery is left to the second reader.

## Review by NM

I read the entire defining paragraph and final sentence of literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/def-finrepair-property-c.md (order 1592). The finite coefficient ring, scheme morphism, all q >= 0, every constructible module sheaf F, constructibility of R^q f_* F on S, and explicit absence of a uniform-vanishing assertion are preserved. There is no literature proof to split: naming a proposition by a universal quantifier is the construction itself, with no existence or well-definedness lemma required beyond the definitions already cited.

I opened each of the four dependency JSON statements. sbc-def-coefficient-conventions fixes a positive N, a finite commutative Lambda annihilated by N, and N invertible on the schemes carrying coefficients; this excludes discrete adic or rational coefficients. def-weil-pbc-scheme-conventions defines morphisms and refers finite type to the existing finite-type-morphism definition, whose statement explicitly treats the structure morphism for schemes over a field. def-weil-pbc-direct-image has a separate *Module sheaves* paragraph, not just the abelian-sheaf construction: it defines direct image on constant-ring module sheaves, its right derived functor on D+, and R^q by the same cohomology formula. def-weil-pbc-constructible-complexes explicitly defines constructible SHEAVES by finite partitions with finite locally constant restrictions before it defines bounded constructible complexes. Thus no inference from bounded complexes or finite Tor amplitude is needed to define this predicate.

As a source cross-check for the constructibility notion I read etale-cohomology.tex, labels definition-finite-locally-constant (03RU), definition-constructible (03RW), and lemma-constructible-quasi-compact-quasi-separated (095E), especially the finite locally constant module clause and the partition criterion. Over finite Lambda, a finite-type Lambda-module is finite as a set, consistent with the cited constructible-sheaf convention. I do not import the 095E equivalence as a new theorem or use it to assert any higher-direct-image theorem; the definition uses exactly the global partition meaning specified in its dependency.

C1--C4: there are zero proof steps, hence zero proof citations or hidden non-elementary proof facts. The statement citations were checked individually as above; no definition node is used as a theorem about preservation. C5--C8 and D1--D5: no new fact or clause is renamed as a node, no cycles can be added because all dependency edges are unchanged, and no proof route is replaced. B1--B9: no new nodes, the item has valid original TeX and self-introduced f, Lambda, F, q, actual search records, no unsupported Mathlib match, and completed blueprint references. B10: concept hits in Lean were opened and rejected as non-identical declarations. The Mathlib hits were also read: FinitePresentation.lean:117--124 is Chevalley for subsets, and Topology/Constructible.lean describes a Boolean algebra of subsets. The second semantic search returns coherent-topology sheaf-composition results; the second grep returns no hits. LeanSearch's HTTP failure is recorded as unavailable rather than absence.

For E1--E6 I checked typing on the small etale site with constant Lambda-modules, q=0 as well as q>0, and that no properness, finite Tor amplitude, or adic completeness is assumed. On an empty scheme the empty partition is permitted; with zero coefficients the only module sheaf is zero; neither case is excluded by the quantifiers. For f an identity, the predicate expresses constructibility degree by degree and has no added request for a bound independent of F. These checks test the meaning of the definition, not a new theorem that C(f) always holds. No mathematical correction or source dispute was needed; the corrections are the missing split metadata and genuine searches.

## Second reading by NM

- Item statement: compared every hypothesis and quantifier with the entire defining paragraph and final sentence of master blueprint `sec-smooth-purity/sk-prop-sf-cbc/def-finrepair-property-c.md`, order 1592; exact agreement, including the absence of uniform vanishing. This definition has a blueprint source, not a Stacks theorem tag.
- Statement dependency `sbc-def-coefficient-conventions`: opened its statement; finite commutative coefficients annihilated by positive N and invertibility of N on the schemes are supplied, with no additional coefficient hypothesis introduced here; pass.
- Statement dependency `def-weil-pbc-scheme-conventions`: opened its statement and followed `def-weil-finite-type-morphism`; finite type over a field means the structure morphism is finite type, and morphisms of schemes are defined; pass. No separatedness or properness is imposed on f.
- Statement dependency `def-weil-pbc-direct-image`: opened the full statement, including its module-sheaf paragraph; it defines direct image and its derived functor for constant-ring modules, and R^q as the cohomology of the degree-zero sheaf's derived image; pass for q=0 and all positive degrees.
- Statement dependency `def-weil-pbc-constructible-complexes`: opened its statement; it defines constructible sheaves independently of bounded complexes through finite partitions with finite locally constant restrictions; pass. Cross-checked Stacks etale-cohomology.tex, definition-finite-locally-constant (03RU), definition-constructible (03RW), and lemma-constructible-quasi-compact-quasi-separated (095E). The finite-ring module convention agrees with finite-type locally constant modules; the item uses its cited global-partition convention without asserting an equivalence for arbitrary non-qcqs schemes.
- Proof steps: none; inspected the empty proof and proof_deps arrays. This names a predicate and asserts neither preservation nor existence of a bound, so there is no non-elementary proof fact to cite. Empty citations.json is correct.
- New nodes: none; inspected all sandbox node files (only the item is present). B1--B7 and the request for independent Mathlib searches for each new node have no new node to apply to. The six existing actual search records introduce no Mathlib leaf.
- Edge cases: zero coefficients and the empty scheme leave the universal predicate well-defined; the empty partition is allowed. For an identity morphism over a field, q=0 refers to the original constructible sheaf and positive q to the higher direct images, with no uniform-vanishing quantifier inserted. There is no claim that C(f) holds for an arbitrary f.
- Lean attachment check: independent read-only keyword/id search in slopmaster2 and upstream master found no declaration naming this predicate. The PropertyC hits concern etale topological invariance, not constructibility under derived direct image; no closed attachment is justified by those names.

Changes: appended this independent second reading only; retained the first worker's report and Review by NM. No mathematical or node-field repair was needed. The prescribed delivery command with a trailing dot prints usage without doing a dry run; use its documented two positional arguments. Its default clone is the explicitly read-only repository, so use WEIL_CLONE_PREFIX with a disposable copy outside that repository for both packaging calls; no direct writes or git commands are made in the read-only tree.
