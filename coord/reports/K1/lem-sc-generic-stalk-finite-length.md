Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-generic-stalk-finite-length.json`: item, split; no Mathlib match.
- `citations.json`: verbatim citation for item step 1.

Attachments: none. Existing nodes `lem-weil-pbc-finite-module-support-annihilator` and `lem-weil-pbc-fg-ideal-radical-power` supply the two general commutative-algebra facts used in step 1.

WANTED: none.

The item was not stated by any declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. The imported statement agrees with Stacks Tag 00L5. I searched the DAG and blueprint for Tag 00L5, support at a maximal ideal, and finite-length support lemmas; the two existing general commutative-algebra nodes were found and reused, so no new child node was created. Mathlib searches were run for the item using LeanFinder, Loogle, grep, and LeanSearch; only general finite-length criteria appeared, so the item is not a Mathlib leaf.

## Review by K1

I read the item source, Algebra Lemma Tag 00L5, and the blueprint paragraph that uses this item (Tag 0BEN, first paragraph). Step 1 cites `lem-weil-pbc-finite-module-support-annihilator` for support as the annihilator zero locus and `lem-weil-pbc-fg-ideal-radical-power` for the maximal-ideal power; both statements say exactly the facts used. Step 2 spells out the powers filtration and checks that every quotient is a finite-dimensional residue-field vector space; this is an elementary filtration argument from the finite-module hypothesis. Step 3 checks positivity from nonzeroness and the definition of length. The Noetherian local, finite-module, support, and nonzero hypotheses are all retained in the item statement. I corrected the imported status from `unsplit` to `split`, removed a duplicate child that merely restated a clause of Tag 00L5, and recorded verbatim citation quotes.

## Not duplicates

`lem-sc-generic-stalk-finite-length` vs `lem-weil-pbc-finite-module-support-annihilator`: the existing node identifies support with the annihilator zero locus for any finitely generated module; the item concludes finite length under the stronger local support hypothesis.

`lem-sc-generic-stalk-finite-length` vs `lem-weil-pbc-fg-ideal-radical-power`: the existing node gives a power containment for finitely generated ideals in a radical; the item concludes finite length of a module.

What could not be finished: no Lean proof was written, as required for stage 1; the child remains statement-only for the next worker.

## Second reading by K1

- Item statement: checked against Algebra Lemma Tag 00L5; the stated forward implication and positivity are correct for a nonzero finite module over a Noetherian local ring.
- Step 1: checked against the Tag 00L5 proof and the statements of `lem-weil-pbc-finite-module-support-annihilator` and `lem-weil-pbc-fg-ideal-radical-power`; the annihilator/radical-power argument has the hypotheses it uses.
- Step 2: checked against the Tag 00L5 filtration argument; finite residue-field flags are elementary, while finite-length additivity is supplied by `lem-weil-pbc-length-additive-short-exact`.
- Step 3: checked against `def-weil-pbc-module-length`; the chain $0\\subsetneq M$ proves strict positivity directly.
- New nodes: none; the item is the only new node and is not a duplicate or Mathlib declaration.
- Changed Step 2 to cite the existing length-additivity node, adding its verbatim quote and proof dependency.
- Rewrote Step 3 to state the strict-chain argument rather than merely asserting positivity.
