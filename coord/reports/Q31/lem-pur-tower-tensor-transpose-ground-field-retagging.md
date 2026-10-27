# Stage-1 delivery: lem-pur-tower-tensor-transpose-ground-field-retagging

## 1. Files written

- `dag/nodes/sec-six-functors/lem-pur-tower-tensor-transpose-ground-field-retagging.json`: statement, now split into five steps; no whole-item Mathlib match.
- `citations.json`: thirteen step/node citations, checked as verbatim substrings of the current cited statements.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

New nodes: 0. Mathlib leaves: 0. The item's statement, statement dependencies, provenance, and existing searches are retained. The additional searches are copied from the actual command log. No Lean was written or compiled; no repository or launcher file was changed.

## 2. Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, retagging, towerGamma, tensorTranspose, coefficient towers, and projection/transpose vocabulary. The existing finite sheaf projection maps do not state this result on strict varying-coefficient towers. The exact blueprint tag has no hit.

## 3. WANTED

None. This is an agent-written expansion of the available blueprint argument, marked `proof_origin.by = agent`.

## 4. Findings and changes

The item had a statement and no proof. Its statement is consistent with the intended projection/counit argument, and was not changed. The essential distinction is that finite evaluation is conservative but need not be faithful: equality of the tower arrows cannot be inferred from equality at each level. The split proves the equalities directly in the ordinary derived tower category.

The sources read were the main-20261015 tower-gamma statement and proof, especially proof clause (2), and the main-20261015 proof of `thm-pur-weil-equivariance-of-purity-and-trace`, Steps 1–3. I also read the chapter and unit records `sec-six-functors` and `sk-thm-sf-package`. The latter's projection-formula and orientation assembly is respected: this auxiliary supplies only the tensor/counit comparison within that route. The older parent text informally treats adjunction compatibility as automatic; here the actual counit-preserving comparison and both Hom images are displayed. No SGA source is used.

No new definition or theorem is needed. The apparent generic lemmas (inverse naturality and comparison of transposes) each reduce to the displayed few-line computations. In particular, I did not create a new node restating the transpose clause. Mathlib's `CategoryTheory.Adjunction.homEquiv` (`CategoryTheory/Adjunction/Basic.lean`, lines 160–171) and `rightAdjointUniq` / `homEquiv_symm_rightAdjointUniq_hom_app` (`CategoryTheory/Adjunction/Unique.lean`, around lines 100–108) cover that generic algebra, but do not identify the geometric tower projection transformation. The second LeanFinder phrasing found these declarations; I read their source. LeanSearch's monoidal-counit and counitAsIsoOfIso hits were also inspected and concern different hypotheses/conclusions. The inherited unavailable search remains recorded as unavailable, while this run's successful searches retain their actual results.

The whole-blueprint searches for retagging and tensor transpose returned no matching blueprint node. The projection search located the existing definition and tower operations rather than a duplicate statement. DAG searches for retagging, inverse projection, counit-preserving isomorphisms and tensor-map transposes led to the six nodes reused below. The item's existing blueprint ancestor/place/via are retained, with `same_as = []`.

## 5. Unfinished work

None for this one-level split. Existing dependencies remain existing dependencies, including the unsplit operations-retagging node. This delivery does not claim their proofs are finished.

## Not duplicates

No new nodes were created, hence there are no new/existing pairs to distinguish. The general adjunction computation stays inside the item's proof.

## Review by Q31

I read the actual statements of all six cited nodes, rather than relying on their titles or on their proofs. I checked the source's clause (2) against the unchanged item: the same coefficient unit, dualizing object, inverse projection and counit define the transpose. The comparison here concerns that construction and requires no orientation comparison. Every step is under 2000 characters; none hides an additional geometric lemma.

Step 1 uses `lem-pur-tower-operations-ground-field-retagging`, which explicitly identifies the tower tensor/pullback comparisons and the same-compactification ordinary adjunctions before evaluation. `def-exchange-projection` states the precise proper mate formula with its unit and counit. `det-sp-tower-shriek-levels` supplies those operations and maps in the ordinary tower derived category. I wrote the unit/counit formula instead of merely saying that the projection map transports. The unit and counit here belong to proper pullback/direct image; they are distinguished as eta/delta from the exceptional counit epsilon.

Step 2 uses the same three statements. The definition explicitly gives PF as the proper mate followed by the proper pushforward of the open tensor comparison. The retagging statement explicitly includes that open comparison. Since all scheme maps and their composite are the same underlying maps, substitution in this formula proves equality. This is an elementary composite calculation from the cited data, not a new assertion about invariance of arbitrary derived constructions.

Step 3 uses only clause (2) of `det-sp-tower-gamma`: that statement supplies the inverse-projection comparison for the dualizing object and the domain of its transpose. It is applied separately to f and its retagged presentation. I do not extract an orientation from clause (1), assume equality of orientations, or use invertibility of the resulting purity map. The operations-retagging statement supplies the tensor symmetries and their naturality. I checked the inverse square's direction: its source is F(omega^sigma tensor f^*K), its target is Fomega tensor K. Multiplying the original naturality square by its two inverses yields exactly the written equation. The two tensor symmetries then give the B-square with the order f^*K tensor omega.

Step 4 uses the counit-preserving uniqueness clause of `det-sp-tower-gluing` and the projection/counit definition in `det-sp-tower-gamma` (2). At the coefficient unit, the relation is epsilon_1 F(rho_1) = epsilon^sigma_1, in that order. Inserting the B-square and tensor functoriality proves the C-square with the common unit constraint. No assertion of geometric base-change compatibility is silently inserted.

Step 5 uses the explicit representing bijection in `det-sp-tower-gluing`, whose formula is epsilon_K composed with F(h). The transpose definitions of `det-sp-tower-gamma` (2) give both required Hom images. Both arrows have source A = f^*K tensor omega^sigma and target GK. The displayed computation shows they have the same image, so injectivity proves equality. `sk-def-sp-normalized-towers` explicitly says the constructible subcategory is full in the ordinary tower derived category; this justifies reading the equality as the required ambient equality. Its ctf category is defined before imposing the separate normalization condition, so no normalization hypothesis has been added.

For the hypotheses, f remains the same smooth separated morphism with the same dimension after retagging, and the coefficient rings and quotient maps do not change. All uses of gamma/gluing have exactly their finite-field, finite-extension, and smooth pure-dimension setting. The inputs K and M are in their stated uniform ctf categories; the transpose domains and inverse comparisons are already supplied by gamma (2), without requiring a new etale-origin or Tor-preservation claim here. Step 1 only forms the projection transformation for general M,K; it does not infer invertibility on an unsupported domain. No arbitrary compatible family of finite derived maps is lifted.

I checked sigma = identity (rho is then the identity by counit-preserving uniqueness), d = 0 (there is no twist/shift argument in this proof), K = 0, and X empty (all displayed Hom/counit computations still apply). Non-normalized towers are allowed throughout, including zero transition maps; the proof is entirely functorial in the actual tower category and never uses reduction isomorphisms. Tensor symmetry handles the order of K and omega explicitly, so no unaccounted sign or commutation is assumed.

Against delivery-errors B–E: there are no new nodes to fail self-containedness, duplication, or statement-only rules; every cited notion already occurs in the unchanged statement dependencies. All proof uses are enumerated and their used formulas are quoted in citations.json. The union of uses is proof_deps. The split adds an argument instead of restating clauses, has no induction or new dependency cycle, and does not change the unit route. The three domain-specific off-unit tools are declared in split_report.tool_uses with their exact limited uses. No mathematical correction or statement dispute was necessary.
