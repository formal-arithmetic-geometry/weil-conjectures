Files written:

- `dag/nodes/sec-abelian-varieties/lem-pc-finite-free-map-residue-localization.json`: item split into two elementary matrix-minor steps; no new nodes.
- `citations.json`: empty because both steps use only the item hypotheses, finite-matrix definitions, and exactness of localization in the elementary calculation.

Attachments: none.

WANTED: `literature/stacks-project/algebra.tex`, Tag 00O0 source text is referenced by the imported node but is not present as a local file; the proof follows the cited finite-free matrix calculation.

The imported node had no proof and had stale `created` metadata from the parent item. I retained the statement and dependencies, filled the proof, marked both matrix steps elementary, and added the blueprint split report. The existing `lem-pc-finite-projective-cokernel-localization` node uses this item as its finite-free specialization, so it is a parent rather than a duplicate. No Lean declaration in the source checkout carries this item tag.

## Review by G1

I read the item node, its parent `lem-pc-finite-projective-cokernel-localization`, the unit record `sk-prop-av-cube`, and the imported blueprint reference identifying the localization clause. I checked the source citation recorded for the item, Stacks Tag 00O0, against the statement: the injective fibre case is the maximal-minor argument, and the isomorphism fibre case is the determinant and adjugate argument. Step 1 explicitly verifies that the selected determinant is outside the prime, that localization makes the minor invertible, and that the resulting identity block gives both injectivity and a finite-free cokernel; it also records the exactness identification of the localized cokernel. Step 2 verifies the equal-rank condition and the determinant inverse. Both steps use no external node statement, so `citations.json` is correctly empty. I searched the whole DAG and blueprint for duplicates and found only the parent node, which cites this item, plus unrelated scheme-level residue-field criteria. The required LeanFinder, Loogle, grep, and LeanSearch searches were run and recorded in the item; no Mathlib declaration states the result. I corrected the previously empty proof and status while leaving the target statement unchanged.

## Second reading by G1

- Item statement: checked against Stacks Tag 00O0, Lemma `cokernel-flat`, parts (1) and (3), hypothesis by hypothesis; verdict correct, including zero-rank, equal-rank, and field cases.
- Step 1: checked against Tag 00O0(1)'s maximal-minor and localized-cokernel argument; verdict correct. The identity block gives injectivity and a finite-free cokernel, and localization exactness identifies the localized cokernel.
- Step 2: checked against Tag 00O0(3)'s determinant argument; verdict correct. The adjugate gives the inverse after inverting an element outside the prime.
- New nodes: none; existing definition nodes were searched across `dag/nodes`. The statement now cites `def-weil-pbc-free-module` as well as the projective-module and localization definitions, so “finite free” is defined.
- Mathlib and Lean checks: the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches were inspected; no exact Mathlib theorem or Lean declaration was found.
- Small cases: zero modules, rank-one maps, equal-rank maps, and $R$ a field all reduce to the stated minor/determinant argument.
- Changes: added the missing free-module statement dependency and citation; retained the elementary proof and source mapping. The imported node's stale `created.item` is maintainer-owned and is preserved by the delivery tool.
