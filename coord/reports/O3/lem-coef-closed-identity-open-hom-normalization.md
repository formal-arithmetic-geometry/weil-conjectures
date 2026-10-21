# Stage-1 report: lem-coef-closed-identity-open-hom-normalization

## Files written

- `dag/nodes/sec-six-functors/lem-coef-closed-identity-open-hom-normalization.json`: item, statement, now split into four proof steps. Statement unchanged. No exact Mathlib match.
- `citations.json`: 17 entries, one verbatim statement quotation for every node used by each proof step.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Existing search records were retained; the searches actually run for O3 are in `searches.jsonl` and their new query/result summaries were appended to the item. The repeated Loogle and grep queries already present in the item were not duplicated in its array.

## Attachments

None. Searched the actual live source `lean/WeilConjectures/` by the blueprint tag and by the closed/identity-open/Hom and canonical comparison notions. There is no project declaration stating every clause. The related `lean/Sheaf/AlgebraicGeometry/SiteClosedCounitTransport.lean` has `sorry` at the theorem body and states the downstream counit lemma, not an attachment for this item. Its docstring helped verify the intended four-factor orientation; it is not proof evidence. No Lean was written and no compiler or build tool was run.

## WANTED

None. The blueprint proof and the relevant Stacks sources are present.

## Audit of the item and source

The source read for the item is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-existence/thm-sf-ambient-adjoint-class.proof.md`, especially its displayed Hom chain and its sentence identifying the final factor as full faithfulness. I also read its statement and the ancestor `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-dualizing.md`, whose proof identifies the local closed counit followed by the affine-space counit. This split provides the identity-open domain/normalization input to the existing parent counit calculation; it does not replace the unit's biduality route.

The statement has no mathematical error requiring correction. Its two lower-bound assumptions are kept. In particular no lower-bound preservation by an arbitrary exceptional adjoint is silently assumed. The isomorphism obtained by applying I to the actual comparison unit gives precisely the intermediate lower bound needed here.

The main citation issue was that the statement of `lem-sf-class-compact-support-comparison` gives the canonical isomorphism and endpoints but not its factorization, and `thm-sf-ambient-adjoint-class` gives the relative bijection without displaying its map formula. I therefore cite the existing `def-sf-compact-support-site-comparison-construction` for the exact two comparison legs and `def-weil-boundary-exceptional-comparison-data` for the proper-case Hom map. The proof proves bijectivity of the latter from its four factors; that definition itself is not cited as a bijectivity theorem. I considered the existing general bounded site-transpose lemma, but its imported purity conventions place E inside a fixed algebraic closure; the item does not add that convention. That lemma is not a dependency of this delivery.

The Mathlib searches found generic adjunction restrictions, uniqueness, sheaf adjunction formulas and scheme integral-closure normalization. I read `Mathlib/CategoryTheory/Adjunction/Restrict.lean:36-84`, `Adjunction/Unique.lean:112-139`, and `Sites/CoverLifting.lean:349-379`. None identifies this specific derived etale/pro-etale mate or its specified closed exceptional Hom normalization, so the item is not a one-line Mathlib specialization. The second semantic phrasing removes the ambiguous word normalization and still finds only general adjunction facts.

## Not duplicates

There are no new nodes, hence no new/existing pairs requiring justification. Searched the entire DAG by identity-open, comparison/Hom normalization and the Stacks tags 09AF and 0B65, and used `tools/blueprint_refs.py search` for identity-open, Hom bijection, site comparison construction, and bounded site adjunction. Those searches found the existing comparison construction and proper-case Hom-map definition used here. `blueprint_refs.py ancestor` confirms `lem-coef-finite-dualizing`; the original from.place and via are retained and same_as is empty. The generic proper-case Hom-map definition is a notion used in the proof, not a new restatement of a conclusion.

## Review by O3

I checked the split myself against delivery-errors B through E, with the cited node statements open. There are no new statement-only obligations to conceal arguments in. The statement is identical to the repository copy; its original proof, citations, search history, source and blueprint provenance were preserved. The four proof steps now carry the actual domain and normalization argument. All are below 2000 characters.

For Step 1 I read `def-weil-l-adic-coefficient-extension`, `lem-weil-pbc-closed-immersion-proper`, `pqf-lem-proper-basic`, `lem-kun-dimension-finite-type`, and `def-weil-finite-type-morphism`. Their statements respectively supply finite coefficients, properness, the qcqs/separated/finite-type properties, a finite dimension bound, and quasi-compactness of P over the affine field point. I checked Stacks morphisms.tex Tags 01W5 (lemma-closed-immersion-proper) and 01W1 (definition-proper), and the blueprint finite-dimension lemma. Closed i really is proper without requiring Z or P to be proper over k. The empty Z case admits d=0. The dimension check is only to put the already-stipulated class adjunction in its stated geometric domain.

For Step 2 I read the statements of `thm-weil-pbc-site-comparison`, `def-sf-comparison-derived-pullback`, and `def-weil-pbc-etale-origin-witness`. The comparison theorem asserts invertibility of the actual unit on all bounded-below finite-ring module objects, without constructibility. Applying I and then S_Z to its inverse gives explicit inverses, and the assumed lower bound on IH passes across the resulting isomorphism. Exact S_Z gives the remaining lower bounds. The resulting pair has exactly the direction S_Z IH -> J S_P H required by the witness definition. I checked Stacks proetale.tex Tag 099V (lemma-relative-comparison), in section 099R, for the underlying comparison-unit argument. The module extension is taken from the existing module theorem, not silently from the abelian-sheaf source alone.

For Step 3 I read the canonical comparison theorem, the exact construction definition, the open-comparison statement and the named direct-image mate statement. The construction explicitly uses the proper counit mate followed by the open comparison, and defines the ambient map by inversion. The open-comparison statement includes compatibility with composition; at the identity this makes the invertible component idempotent, hence the identity after cancellation. This gives C = delta inverse with the required orientation, not merely some isomorphism with those endpoints. The named mate lemma applies because Step 1 verifies qcqs. I read Stacks proetale.tex Tag 09AF (lemma-jshriek-comparison), where the open map is the adjunction comparison, and categories.tex Tag 0B65 (lemma-transformation-between-functors-and-adjoints) for the fixed counit-mate normalization. The identity-open identifications are the ones already stipulated by the item; the proof never selects another comparison.

For Step 4 I read `def-weil-boundary-exceptional-comparison-data` in full: it defines h by exactly the four operations used, while explicitly asserting no bijectivity. I checked its finite commutative ring, proper map and quasi-compact target hypotheses in Step 1. I use only that map definition, not its later compatibility property or its lower-bound interface. The stipulated class construction in `thm-sf-ambient-adjoint-class` is evaluated at the identity witness; its first leg is now delta by Step 3. I read `lem-exc-closed-ambient` for the ordinary adjunction and `def-weil-pbc-direct-image` for the module D+ direct-image domain. The comparison adjunction gives the second map by its unit formula, the ordinary adjunction gives beta, and full faithfulness gives the final S_Z bijection because the two etale objects are in D+ by Step 2 and the hypotheses. The explicit four outputs establish the requested specified formula. I did not identify it merely by uniqueness of a right adjoint, which would leave the normalization unresolved.

I tested H=0 and L=0: the chain is the unique map of the zero Hom groups and the witness has the indicated inverse. For Z empty, the source derived category is the zero category and the same argument works. For i the identity, the proper mate is the identity in the canonical site coordinates and the displayed chain is the ordinary comparison transport. For a nontrivial closed immersion, properness alone is enough for the direct-image comparison; there is no constructibility, finite-Tor or ambient unbounded pro-etale adjunction assumption. All coefficient functors stay in the ordinary constant-R module presentation. The proof uses no SGA source. The step-use union is exactly proof_deps and every quotation in citations.json was checked as a literal substring of its cited statement.

## Unfinished work

None within the authorized stage-1 item. The existing prerequisites remain the project's own obligations; no claim of completing their Lean proofs is made. The required server dry run and delivery are performed after writing this report.
