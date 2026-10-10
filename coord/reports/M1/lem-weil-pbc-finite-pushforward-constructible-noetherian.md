Files written:

- `item.json`: split item; no new nodes; Mathlib search found no exact match.
- `citations.json`: verbatim statement excerpts for all cited nodes and steps.

Attachments: none.

WANTED: Stacks Project Etale Cohomology, Lemma 095R source text if the local literature mirror is restored; the imported node and proof identify this as the source.

The imported item had a complete three-paragraph proof but omitted its required search records, blueprint metadata, and citation quotes. I retained the statement and route, changed the proof origin to Stacks Lemma 095R, and marked the item split. No child node was created because each non-elementary dependency already exists in the DAG. The first paragraph's pullback-preserves-constructibility observation is elementary from the definition and is stated as such.

## Review by M1

I checked the item against the imported blueprint proof and the Stacks 095R identification. Step 1 uses the existing finite-exchange statement exactly for restriction to a reduced closed base change; its statement supplies the finite Cartesian exchange isomorphism. The accompanying pullback of a finite locally closed partition and finite constant etale trivializations is a direct definition-level argument. Step 2 uses the existing Noetherian-components statement exactly to obtain finitely many irreducible components, then performs the stated Noetherian induction and disjoint refinement. Step 3 uses the existing generic finite-pushforward statement with the required hypotheses after replacing an irreducible closed subset by its reduced integral structure and choosing an affine open; its dense lisse open is precisely the input needed to finish the induction.

I verified that all cited nodes pre-exist and that every citation quote is verbatim. The finite-exchange node belongs to the proper-base-change unit, so it is recorded as an explicit tool use because this unit's route needs the generic base-change fact and supplies no replacement. I checked the edge cases of the empty closed subset, a reducible zero-dimensional scheme, and an identity finite morphism: the induction and resulting partition are immediate in each case. Mathlib searches were run through `msearch.py`; LeanFinder returned only topological constructibility results, Loogle reported an unknown identifier, grep found no match, and LeanSearch was unavailable.

## Second reading by M1

- Item statement: checked against Stacks tag 095R, label `lemma-finite-pushforward-constructible`; the Noetherian finite-morphism and abelian-sheaf specialization has all source hypotheses.
- Step 1: checked against the finite-exchange node and the constructibility definition; exchange supplies the closed-base-change identification, while pulling back strata and finite constant trivializations is definition-level.
- Step 2: checked against the finite-components node; Noetherian induction and the ordered component differences give disjoint locally closed pieces covering each reducible closed subset.
- Step 3: checked against the generic finite-pushforward node; after reduction, the affine open is integral Noetherian, and open restriction of direct image is the defining section formula. The complement is proper and handled by induction.
- Existing nodes: all three cited nodes were found by `rg -l` in `dag/nodes`; no new node was needed, so B1-B7 introduce no additional obligations.
- Edge cases: the empty scheme, zero sheaf, field base, identity finite map, and zero-dimensional reducible base all satisfy the stated conclusion directly; the $n=0,1$ cases are vacuous here because no numerical parameter occurs.
- Search records: retained the worker's four `msearch.py` records (LeanFinder, Loogle, grep, and unavailable LeanSearch); no exact Mathlib declaration was found.

Changes made: clarified the open-base-change identification in Step 3 and added this source, dependency, edge-case, and search audit.
