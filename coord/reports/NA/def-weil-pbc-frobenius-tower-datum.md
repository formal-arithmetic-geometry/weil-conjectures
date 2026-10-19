# Stage-1 report: def-weil-pbc-frobenius-tower-datum

1. Files written: `dag/nodes/sec-proper-base-change/def-weil-pbc-frobenius-tower-datum.json`, definition, split; `citations.json`, empty because this item is a definition with no numbered proof steps.
2. Attachments: none. I searched the slopmaster2 `WeilConjectures/` tree for the item id, Frobenius-equivariant datum terminology, tower/Frobenius symbols, and related declarations; no sorry-free declaration states the complete item.
3. WANTED: none.
4. Corrections: the imported statement and its two level-map dependencies agree with the master blueprint node and require no correction. The definition is kept as one self-contained datum: its witnesses, four automorphisms and commutation equations, Cartesian Frobenius faces, exact-equivalence functors, pullback/proper exchange maps, compatible tower isomorphisms, and coefficient normalizations are all retained. No clause was moved into a new node or weakened. Whole-DAG and blueprint searches found no duplicate node or alternate statement. Mathlib searches found only unrelated Frobenius algebra/isocrystal declarations and no general datum matching this construction.
5. Nothing remains unfinished; this is a statement-only definition split.

## Review by NA

I read the item source `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-frobenius-tower-datum.md`, the chapter and unit records, and the complete statements of `def-weil-pbc-level-map-arrows` and `def-weil-pbc-level-map-corners`. The item uses exactly those corner and arrow constructions. I checked each imported clause against the source: the etale-origin witnesses and their transition compatibility; all four automorphisms and the four commuting equations; Cartesian identifications and cube compatibility; the definition and consequences of `Phi_Z`; the two pullback exchanges; the two proper finite-level exchanges; the `vartheta_n` maps and their transition equation; and identity Frobenius and normalization/cocycle requirements for constant coefficients. No hidden hypothesis or altered coefficient category appears.

Because `kind` is `definition` and `proof` is empty, there are no numbered argument steps or non-elementary proof facts to cite; `citations.json` is therefore the empty list. The dependency statements were opened to verify that they define the four level corners/arrows used by the item, rather than relying on proof text. I checked the source checkout for the blueprint tag and all prominent names and found no completed declaration to attach. The recorded LeanFinder, Loogle, grep, and LeanSearch queries were run through `msearch.py`; their hits are unrelated Frobenius ring/isocrystal APIs or unavailable services, so this item is not a Mathlib leaf. Small sanity checks (identity Frobenius on all four schemes, a one-level tower, and zero/identity transition maps) satisfy the displayed equations and reveal no missing clause. No Lean files, compilers, Lake, or live project files were used.

## Dry run

`python3 /home/ubuntu/weil-launcher-nt/deliver.py NA def-weil-pbc-frobenius-tower-datum --no-push` completed with `OK (not pushed) ... preflight passed`.

## Second reading by NA

- Item statement: checked against blueprint node `def-weil-pbc-frobenius-tower-datum` (order 1332), clause by clause; the witnesses, four commuting Frobenius maps, Cartesian faces, exact-equivalence consequences, pullback/proper exchanges, tower isomorphisms, and coefficient normalizations agree.
- Dependency `def-weil-pbc-level-map-arrows`: opened its statement and confirmed it supplies the four finite-level arrows used by the surrounding construction; no proof text is relied on.
- Dependency `def-weil-pbc-level-map-corners`: opened its statement and confirmed it supplies the four corners and Cartesian pullback identification; no proof text is relied on.
- Definition form: statement-only with no numbered proof steps, so `citations.json` remains empty and no step dependency audit is applicable.
- Mathlib/Lean audit: reran the recorded searches and checked the slopmaster2 tree for the item and its distinctive Frobenius/tower terminology; no exact declaration or general Mathlib match exists.
- Edge cases: identity Frobenius, a one-level tower, and zero/identity transition maps satisfy the displayed equations; no clause excludes these cases.

I changed the item blueprint metadata to record its nearest blueprint ancestor and the exact portion of that node realized by this split. The statement and dependencies were already faithful to the source, so no mathematical text or node was removed or weakened.
