## Worker report

Files written: `dag/nodes/sec-proetale-coefficients/def-sfb-modobj-restriction.json` (existing definition; now a Mathlib leaf), `citations.json` (empty because a Mathlib leaf has no proof steps), and this report. The search command maintains `searches.jsonl`.

No new nodes. One Mathlib leaf, counting the item. No Lean files, compiles or builds.

Attachments: none. A search throughout `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, `def comap`, and `restriction of scalars` found no project declaration stating this entire general construction. The named declaration is in Mathlib, so this is a Mathlib leaf, not an ATTACH claim. Project declarations for sheaves, ordinary modules, and compositions of restriction functors do not replace the general construction.

WANTED: none.

What was wrong: the import says `lean_not_found` for `CategoryTheory.Mod.comap`, but the pinned Mathlib source contains exactly that declaration. The semantic services return historical `CategoryTheory.Mod_` names; Loogle and the local pinned source establish the current `CategoryTheory.Mod` names. The imported proof has unjudged elementary fields and is unnecessary once the full Mathlib construction is identified. I kept the natural statement verbatim, replaced the imported proof by the leaf record, and added the already existing `sk-def-sfb-ring-object` to statement dependencies because its statement explicitly defines monoid objects and their morphisms. All maintainer-owned/import fields were preserved.

Nothing remains unfinished. The sandbox is intended for the independent second reader; no delivery was pushed.

## Sources and blueprint search

Read the current main-20261015 chapter `sec-proetale-coefficients/_section.md`, its unit `sk-def-sfb-change-of-scalars/_section.md` (in particular clause 1), the item's markdown and its separate `def-sfb-modobj-restriction.proof.md` (unit, associativity, and linearity paragraphs), and the statements of `sk-def-sfb-module-objects`, `sk-def-sfb-ring-object`, and `sk-def-sfb-change-of-scalars` in the DAG. The corresponding new chapter/unit JSON records are absent in this snapshot; I used the actual current blueprint markdown and did not alter unit or chapter metadata.

Ran `tools/blueprint_refs.py search 'restriction of scalars'` across all blueprint nodes, a second search for `restriction`, and `ancestor def-sfb-modobj-restriction`; also searched the whole DAG for `Restriction of scalars|restriction of scalars|Mod.comap`. The existing change-of-scalars unit has a strictly larger multi-clause statement and itself uses the item for its first clause. The other general comap nodes assert compatibilities, equivalences or preservation properties. `pur713-def-restriction` is the specialization to commutative ring objects of abelian sheaves on a pro-etale site. None calls for a new node or a replacement dependency. `same_as` is empty: there is no second node with the same full statement. As this is an imported blueprint node, `blueprint.from` remains null.

All five Mathlib searches recorded in the node were actually run with msearch.py and are in searches.jsonl. Both semantic services were available; the recorded results distinguish their historical names from the checked pinned names. The grep results locate comap at line 403, scalarRestriction at 363, scalarRestriction_hom at 387, and selfLeftAction at Action/Basic.lean:174. Read Mod.lean:351-410 and Action/Basic.lean:170-181 directly.

## Review by NJ

I compared every clause of the item with clause 1 of the current change-of-scalars unit and with the pinned Mathlib construction. The item assumes only a monoidal category C, monoid objects R,S, and a monoid morphism phi. `CategoryTheory.Mod.comap` (Mathlib/CategoryTheory/Monoidal/Mod.lean:403) assumes those data and a monoidal left action on a category D. Taking D = C uses the existing `CategoryTheory.selfLeftAction` at Action/Basic.lean:174: it defines the action object as tensor product, the action on maps as tensor of maps, and its unitor and associator as those of C. Thus it adds no hypothesis such as braiding, closedness, abelianness, commutativity, or existence of limits/colimits.

For the action clause (the old first and second proof paragraphs), `CategoryTheory.Mod.scalarRestriction` at Mod.lean:363 defines `smul := f` acting on the left `followed by gamma`, exactly gamma_N composed with (phi tensor N). Its `one_smul` proof uses preservation of the unit by the monoid morphism, then the old action unit law (365-367). Its `mul_smul` proof uses exchange/naturality, the old associativity equation, then preservation of multiplication (368-377). I checked the order of the composite: Lean's `a ≫ b` notation here means first a, then b, matching the displayed mathematical formula, with no opposite or right module.

For linearity (the old third paragraph), `CategoryTheory.Mod.scalarRestriction_hom` at 387-395 takes an arbitrary B-linear map g and proves it is A-linear for precisely the two restricted module structures. It uses action exchange with the original linearity equation. For the final functor clause, `comap` at 403-410 returns the same `M.X` at the object level and the same `g.hom` at the morphism level, with those restricted structures. Its return type is `Mod D B` to `Mod D A`, the required contravariant direction in coefficient morphisms. Identity and composition are the underlying category's operations. This covers every clause, not only the existence of an action.

I opened the two statement dependencies. `sk-def-sfb-module-objects` gives the action map, its two axioms and linear morphisms/category in clauses 1-2; its later coefficient specialization is not used. `sk-def-sfb-ring-object` explicitly gives the monoid multiplication/unit laws and says a morphism is compatible with multiplication and units. This justifies adding it as a notion dependency, without using its claims about sheafification. No step takes a theorem from a definition node: the delivery is a Mathlib leaf with no proof steps or proof dependencies. Consequently citations.json is the empty list; there are no missing step/node pairs and no C4 quotation substitutions.

I checked the B-E return cases against this result. No unsplit child, non-self-contained statement, clause renamed as a lemma, duplicate, invented Stacks citation, unproved transport argument or extra route dependency is introduced. The only leaf match is checked in the pinned source with exact names, files and lines. The current chapter and unit route is followed by directly realizing its restriction construction, and no SGA source is used. Small cases: phi = identity gives the original action; restricting to the tensor unit yields its canonical unit action; the terminal monoidal category gives the identity functor on its unique module. These require no excluded nonzero or nonempty hypothesis. Noncommutative monoids are allowed throughout. No statement dispute or source correction was needed; the correction is to the import's missing-Mathlib assessment and the missing notion dependency.

## Earlier second reading (a previous round; superseded)

- Item statement: checked every hypothesis and clause against `def-sfb-modobj-restriction.md` and Mathlib `CategoryTheory.Mod.comap`; verdict exact, including the action formula, functor direction, and identity-on-underlying-data clause.
- Item proof: there are no proof steps because this is a Mathlib leaf; `scalarRestriction`, `scalarRestriction_hom`, and `comap` were read in the pinned source and jointly cover the action axioms, linearity, and functor construction.
- New nodes: none; consequently B1--B7, node-level citations, and duplicate-node checks introduce no additional obligations.
- Mathlib leaf: reran grep, LeanFinder, Loogle, and the recorded semantic search with `msearch.py`; verified `CategoryTheory.Mod.comap` in `.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mod.lean:403` and `selfLeftAction` in `.../Action/Basic.lean:174`, with supporting declarations at lines 363--395.
- Edge cases: identity morphism, tensor-unit object, terminal monoidal category, and noncommutative monoids introduce no missing hypotheses or excluded cases.

Changes made during this second reading: no mathematical or structural edits were required. I added this second-reading record, confirmed the existing `sk-def-sfb-ring-object` statement dependency is needed for the monoid-object terminology, and confirmed the dry-run delivery preflight passes.

## Repair of returned delivery (2026-10-16)

The earlier reviewed delivery was returned because the statement of `sk-def-sfb-ring-object`, which is a statement dependency of this definition, changed after review. I re-read the current expanded statement in the live DAG, including its explicit monoid-object multiplication, unit, and morphism clauses, and revalidated that the restriction construction only needs the monoid-object terminology and morphism data already supplied by that node. The item remains a Mathlib leaf: it has no proof-step citations, so `citations.json` remains empty and no citation quote became stale. I also checked that the current origin contains the updated dependency before rerunning the delivery preflight; it passed at commit `1221204685`.

## Second reading by NJ

- Item statement: checked the monoidal category, monoid-object morphism, module-object action, restricted action formula, linearity clause, functor direction, and identity-on-underlying-data clause against the source node and `CategoryTheory.Mod.comap`; verdict exact, with no added hypotheses.
- Item proof: the item is a Mathlib leaf, so there are no proof steps or citations; read `scalarRestriction`, `scalarRestriction_hom`, and `comap` in the pinned `Mathlib/CategoryTheory/Monoidal/Mod.lean` at lines 363--410 and `selfLeftAction` in `Action/Basic.lean` at lines 174--181; verdict all action, unit, associativity, linearity, and functor clauses are supplied.
- New nodes: none; B1--B7 and duplicate-node checks therefore introduce no new obligations.
- Mathlib search: reran grep, LeanSearch, Loogle, and LeanFinder with the queries recorded in the node; verdict `CategoryTheory.Mod.comap` is an exact construction after specializing the self action, while the semantic `Mod_` names are historical aliases.
- Dependencies: checked `sk-def-sfb-module-objects` for module actions and linear maps and `sk-def-sfb-ring-object` for monoid-object terminology and morphisms; verdict each cited dependency supplies the notions used.
- Edge cases: identity morphism, zero/terminal monoidal category, tensor-unit module, and noncommutative monoids were checked; verdict no excluded case or extra commutativity, limits, or nonzero hypothesis.
- Changes: added this exact second-reading section and retained the worker's Mathlib leaf and dependency repair; no mathematical statement change was needed.
