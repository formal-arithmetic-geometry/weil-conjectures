# Stage-1 delivery: lem-sfb-syntomic-smooth-composition

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-syntomic-smooth-composition.json`: statement, split; existing statement and statement dependencies preserved; seven complete proof steps. No new nodes and no new Mathlib leaves.
- `citations.json`: 26 entries, one for every step/node pair, each quoting that node's statement verbatim.
- `searches.jsonl`: actual Q124 msearch records for the item, with both semantic phrasings, Loogle, source grep and LeanSearch. Earlier O4 searches in the item are retained.
- `report.md`: this report.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item id and for syntomic, including smooth/syntomic combinations. There is no project declaration stating all clauses. Existing syntomic presentation and flat-smooth-fibre declarations address prerequisites, not this item. In particular a sorry-free local presentation declaration does not prove composition. No Lean was written or compiled.

## WANTED

None. All sources used for the split are present in `literature/stacks-project/`.

## What needed correction

The item had no proof. Its statement is correct and was kept verbatim. The source's proof of 00SZ(1) has typographical primes/ring labels (the upper prime is in the final algebra, and the localization target must be the final algebra localized at both elements). Steps 2 and 3 use distinct primes in S and T and explicitly write a=psi(g)h in T. This is a correction of proof notation, not a statement dispute or a changed hypothesis.

I did not create nodes for syntomic composition, smooth-implies-syntomic, or etale-implies-syntomic: these are the clauses being proved. I also did not create a duplicate relative-CI composition node. Step 1 proves that presentation calculation explicitly from existing dimension bounds. Its successive-quotient identification is the elementary polynomial quotient universal property; the non-elementary dimension assertions have their own cited statements.

I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. The created-item chain records a longer alteration prerequisite below direct images. `tools/blueprint_refs.py ancestor` returns None for this inherited chain, as the live item's existing blueprint field also records. I retained that null ancestor and its detailed place/via data. Whole-blueprint searches for syntomic, complete intersection, standard smooth, and 00SZ found no duplicate blueprint statement. No chapter, unit, or route was changed. This item is not a unit key node, so no realization record is written.

## Mathlib searches

I ran msearch with Q124 and this item for: leanfinder “Syntomic ring homomorphisms compose and every smooth or etale ring map is syntomic”; Loogle `Algebra.Smooth, Algebra.Etale`; grep `syntomic|relativeGlobalCompleteIntersection|isRelativeGlobalCompleteIntersection` in RingTheory; LeanSearch “Flat finitely presented ring maps with local complete intersection fibres compose”; and the second leanfinder phrasing “Composition of flat algebras of finite presentation with complete intersection fibres; locally standard smooth algebras have complete intersection fibres”. All returned successfully. The source grep returned zero hits. Semantic hits cover smooth/standard-smooth composition, flat composition, finite-presentation composition, and etale-to-smooth. They do not state the syntomic composition assertion or supply its lci-fibre condition. The Loogle etale-to-smooth hit covers only an elementary final reduction, not an attachment for the full item. These actual results are recorded without changing the earlier O4 searches. No new node needs a search record.

## Not duplicates

No new nodes were created. I read and reused the existing ring-level syntomic-at-prime relative-presentation criterion, the trace-formula relative-CI principal-cover gluing theorem, relative-CI base change, the standard-smooth base-change and dimension-at-points theorems, and the generic upper/lower dimension bounds. The scheme-level syntomic pointwise-model and syntomic-etale-source-locality nodes were considered but are not substitutes for ring composition. The stronger relative-CI chart gluing node already provides all three syntomic conditions and explicitly includes the empty cover.

## Review by Q124

I read Stacks algebra.tex, definition-lci (00SL), lemma-local-syntomic (00SO), definition-relative-global-complete-intersection (00SP), lemma-syntomic (00SY) and lemma-composition-syntomic (00SZ), including both parts of the latter's proof. For smooth inputs I read lemma-standard-smooth (00T7), including its fibre-dimension proof of (7), and lemma-smooth-syntomic (00TA), including its final local-to-global argument. For etale inputs I read definition-etale (00U1) and lemma-etale-standard-smooth (00U9); the final step uses the defining cotangent conditions directly. The tags were checked in the local tags table. There are no new-node sources to review.

Step 1 uses the statement of relative-CI base change to retain both presentations over each residue field. The affine fibre-product statement identifies the scheme fibres with the rings to which the relative-CI definition assigns dimension. The polynomial-quotient lower-bound statement requires number of variables at least number of equations; I verified this before applying it: a nonzero final fibre has a prime and hence a nonempty fibre over the intermediate ring, forcing both differences n-c and m-d to be nonnegative. The proper-ideal/maximal-ideal statement justifies existence of that prime. The finite-type-algebra-Noetherian statement applies because the coefficient is a field and both rings have finite polynomial presentations. The source-dimension/fibre bound applies to the finite type map Spec(V) to the locally Noetherian Spec(U); its exact statement bounds the total dimension by dim(U) plus the uniform fibre bound. Together with the lower bound it gives equality, not merely an upper bound or equidimensionality assumption. The combined quotient presentation is written explicitly. No general composition theorem is assumed.

Step 2 uses the ring-level syntomic-at-prime theorem, whose statement I opened. Its finite-presentation-at-a-prime condition is satisfied with localization at 1. Its local flatness condition follows from the exact equivalence in the flat-map local criterion. Its fibre condition asks for a principal global-CI neighbourhood of the distinguished fibre prime; the local-CI definition gives exactly that cover and that neighbourhood. I checked both applications, first at s in S over R and then at q in T over S. This avoids substituting the different scheme-level pointwise-local-ring hypothesis.

Step 3 uses the base-change theorem on S to S_g and on the already chosen S to T_h relative presentation. Localization base change and localization transitivity give the indicated target T_a with its scalar structures. The product a avoids q because g avoids its contraction and h avoids q. Step 1 then supplies the whole relative-CI property of the composite chart, rather than citing the desired syntomic composition clause.

Step 4 uses exactly the quasi-compactness and standard-open/unit-ideal clauses in the spectrum lemma to obtain a finite relation. The gluing theorem's statement takes precisely that relation and relative-CI presentations and concludes flatness, finite presentation, and the residue-field lci condition. Thus no unnamed flatness or finite-presentation composition result is used. The gluing theorem explicitly allows the empty cover when T=0.

Step 5 uses the standard-smooth base-change theorem with the specified presentation, retaining n and c. The existing dimension-at-points statement is for the spectrum at every prime, not the local-ring dimension; this is the right notion for the dimension-supremum theorem. The maximal-ideal lemma ensures a nonzero fibre has a point, so the supremum of constant n-c is n-c. This gives the precise relative-CI definition, including ignoring zero fibres.

Step 6 uses the locally-standard-smooth ring-map statement, not its scheme analogue; it gives principal neighbourhoods of every prime over the fixed base R. Steps 5 and 4 then furnish the required charts and gluing. Step 7 uses the affine etale/ring-map equivalence, which states finite presentation, H1=0 and Omega=0, and the smooth definition, which states finite presentation, H1=0 and finite projectivity of Omega. The zero module is free on zero generators, so this last reduction is elementary and has no finiteness or separation gap.

All 26 uses have verbatim quotes in citations.json. I checked B through E of delivery-errors against the actual node and cited statements: there are no new statement-only nodes to be hollow, no clause renamed as a lemma, no proof of a dependency used in place of its statement, and no scheme theorem applied as though it already stated a ring theorem. Generic tools from other units are declared with their purposes in split_report.tool_uses. Every proof step is shorter than 2000 characters (the longest is 1320), and the displayed arguments have no hidden comparison, descent, or composition black box.

I tested identity maps, polynomial smooth maps, etale localizations, empty spectra, zero fibres, the zero final ring, and charts with no variables or no relations. For example k[x]/(x^2) followed by adjoining y with y^2=0 produces two equations in two variables, with dimension zero as both bounds require. If a relative presentation has more equations than variables, its nonempty fibre condition is impossible, so it contributes only zero fibres and is never fed to the polynomial lower-bound theorem outside its hypotheses. The proof assumes neither Noetherianity of the original base nor surjectivity of either input map.

## Unfinished work

No mathematical part of this one-level split remains. Existing cited nodes remain owned by their workers; this delivery changes only the assigned item and supplies its report. Server preflight and delivery are performed after this report is written.
