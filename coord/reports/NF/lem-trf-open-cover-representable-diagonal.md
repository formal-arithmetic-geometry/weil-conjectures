# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-open-cover-representable-diagonal.json`: item, statement, split; no exact Mathlib match. Its statement is unchanged. Added the existing definition nodes for open subfunctors, scheme representability and fibre products to statement dependencies.
- `citations.json`: eleven step/node entries, each quoting the cited statement verbatim.
- No new nodes, no new Mathlib leaves, and no unit record changes.

## Attachments

None for the item. The project search under `lean/WeilConjectures/` for the item id, representable diagonals, and local representability found the generic criterion `AlgebraicGeometry.isRepresentable_of_isSheaf_of_zariskiCovers` in `WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Representability.lean:700`. Its hypotheses require a representable open cover already; it does not state this item's diagonal-cover construction or all its conclusions. It already belongs to `lem-pc-schemes-criterion`, which is cited. No claim of a new attachment is made.

## WANTED

None. All needed sources are available locally.

## Corrections and limitations

The imported node had an empty proof and no Lean audit. Its statement correctly extracts just the first two paragraphs of Stacks 02WR: algebraicity and an atlas of each F_i, and algebraicity of the coproduct, are unnecessary for these paragraphs. I preserved that statement and all import/ancestry metadata. The final diagonal implication is written explicitly using the scheme diagonal and a scheme fibre product rather than citing a general diagonal equivalence without a DAG node.

The historical nearest blueprint ancestor is `lem-trf-local-term-locality`; the item is far below its polarized/log descent chain. I read its current statement and proof and the chapter/unit records. This split supports the existing intermediate open-gluing argument; it does not change the contracting-correspondence route or claim to realize the unit's key proposition. The unit's realized fields are therefore untouched.

Nothing mathematical remains unfinished in the item's split. Proofs of the cited nodes remain their owners' responsibility.

## Searches and reuse

Searched the whole DAG for 02WR, 01JJ, open subfunctors, representable diagonals, and Zariski/fppf comparisons; ran `tools/blueprint_refs.py search` for representable, diagonal and 01JJ and `ancestor` for the item. The results include the existing `lem-pc-schemes-criterion` (01JJ), `def-pc-open-subfunctor` (01JI), `lem-pc-zariski-coverings-are-fppf`, and `lem-weil-pbc-scheme-morphism-gluing`. Reused all of them instead of creating nodes. The sibling coproduct-base-change and local-open-descent statements were read but not used: their additional conclusions are unnecessary, and the covering argument here follows directly from the hypothesis and definitions.

The five searches in this sandbox's searches.jsonl were run with the prescribed msearch command and their results read. Two semantic phrasings, Loogle, grep and LeanSearch find local scheme representability and generic relative-diagonal equivalences, not the whole item. Read Mathlib/AlgebraicGeometry/Sites/Representability.lean:185-211 and CategoryTheory/MorphismProperty/Representable.lean:628-673, as well as the project relative criterion and its over-S hypotheses. The existing six search records imported with the item are retained; only this session's actual logged queries were appended. No compiler, Lake, local preflight, or Lean-writing tool was used.

## Review by NF

I read spaces.tex, Tag 02WR (`lemma-glueing-algebraic-spaces`), statement and complete proof, especially its first two paragraphs; schemes.tex, Tag 01JI (`definition-representable-by-open-immersions`) and Tag 01JJ (`lemma-glue-functors`), statement and proof; topologies.tex, Tag 021N (`lemma-zariski-etale-smooth-syntomic-fppf`); and spaces.tex `lemma-representable-diagonal`, statement and proof. The source's algebraic-space hypothesis is used in its second paragraph only to obtain representability of V_i times over F_i V'_i. Our item's hypothesis supplies exactly that fact, without an atlas. The set-indexed size condition is preserved.

For step 1 I opened `def-pc-open-subfunctor` and `def-pc-fppf-site`. The former says precisely that factorization through the representing open is equivalent to membership after pullback. The latter explicitly includes joint surjectivity, which is what gives every point of T an image lying in one of the V_i. No descent of open sets, no openness theorem for fppf morphisms, and no assumption that a set-theoretic image inclusion implies factorization is used. The factorizations are furnished by the representing property, before the point argument.

For step 2 I read `def-pc-subfunctor` and the same open-subfunctor definition. The description by pairs constructs both directions of the identification G_i = h_V_i times over F_i h_V'_i, and checks restriction compatibility. Injectivity of F_i(W) into F(W) is essential and is stated by the subfunctor node. The assumed diagonal hypothesis applies to the schemes V_i,V'_i themselves, with their universal maps to F_i. Thus no hypothesis of algebraicity, separatedness, quasi-compactness, or affine intersections is inserted. This is an elementary identification followed by applying an explicit hypothesis, not a new lemma.

For step 3 I again checked the exact open-subfunctor statement. On an arbitrary scheme test (u,v), its common F-value c cuts out O_i; the membership equivalence identifies the pullback along G_i with this same open. Step 1 applies to the scheme W and the section c. This verifies the full test-scheme covering condition, which cannot be replaced by checking only the chosen representatives. The argument is an instance of the definition, with no hidden base-change theorem.

For step 4 I read the full statements of `lem-weil-pbc-scheme-morphism-gluing`, `lem-pc-zariski-coverings-are-fppf`, and `def-weil-pbc-sites-and-cohomology`. The first gives existence and uniqueness for each coordinate and equality of the composites to S; the second says a Zariski covering is an fppf covering; the equalizer in the third makes equality of the two F-sections detectable on that cover. This proves the Zariski sheaf property actually needed by 01JJ and avoids an uncited general theorem on limits of sheaves or fppf subcanonicity.

For step 5 I checked all clauses of `lem-pc-schemes-criterion` against steps 2-4. The current blueprint_update states the absolute version on all schemes; the existing statement and its closed relative declaration provide the over-S criterion used here. I read the relative declaration's source and verified it takes small values and a small index family. Our G(W) is a subset of Mor_S(W,T) times Mor_S(W,T'), so its values are small in the scheme universe even if the ambient F-values live in the larger universe. Its G_i are subfunctors represented by schemes in the chosen bound. The small family is exactly the original I. This is a generic tool use of the existing 01JJ node; no statement-only new node disguises the conclusion.

For step 6 I read `def-pc-fibre-product` and `def-trf-algebraic-space`. The former states existence and the complete universal property for scheme fibre products. The latter defines representability of a sheaf map by every scheme test. Given x,y on W, the scheme R from step 5 maps to W times over S W; pulling back along the scheme diagonal forces both coordinates equal to the test morphism r. Thus maps into E are exactly the required equalizer. This writes the diagonal-test construction instead of appealing to an unavailable pair-test equivalence. The products are over S, and the final pullback is over W times over S W; no wrong base is substituted.

I checked B1-B10 and C1-C8: there are no new nodes, no duplicate creation, no off-route replacement (the generic tools are declared in split_report), no cited proof internals, and every used theorem is the statement of a named existing node. D1-D5: the six steps carry the actual covering, pair-identification, sheaf, gluing, and diagonal-test arguments. No whole conclusion is moved to a new node. E1-E7: the fppf lifts exist by the item's hypothesis, the test opens exist by relative open representability, and the pair representation uses precisely the F_i diagonal assumption. No source error or statement dispute was found. No step exceeds 2000 characters.

Small cases checked: empty I forces F(T) empty for every nonempty T by joint surjectivity, so every occurring representing G is empty; T empty is covered by the empty open family and unique maps glue from it. A singleton family reduces to a single open covering the whole test scheme. Disjoint F_i produce empty cross-fibre-products, allowed by the representing hypothesis. Nothing assumes T or its intersections affine, and schemes with nilpotents are handled by the functorial factorization criterion rather than by pointwise image alone. There is no new statement needing separate small-case testing. My only corrections to the inherited material are the completed proof, explicit missing notion dependencies and the fresh search records; no source hypotheses or conclusions were changed.

## Not duplicates

No new nodes were created. The general 01JJ representability criterion, 01JI open-subfunctor definition and covering comparison already exist and are reused.

## Resumed validation, 2026-10-22

Continued the existing sandbox rather than replacing its work. The required first dry run passed at 01362e0ac6e. Compared the item against the current repository: its statement and ancestry remain unchanged and no released repair note exists. Reopened the statements of all proof citations, reread Stacks 02WR, 01JI, 01JJ and 021N and the relative project criterion, and verified all eleven citation quotes against the current node statements. The relative criterion remains at line 700 in the current source; corrected the report line reference. Its small-value hypothesis holds because G(W) is a subset of a product of two sets of S-morphisms. The scheme pullback in step 6 imposes equality of the two maps to W and thus represents the diagonal test. Reused the logged searches and inspected their candidate declarations without repeating the unchanged questions. No mathematical proof or search record needed repair.
