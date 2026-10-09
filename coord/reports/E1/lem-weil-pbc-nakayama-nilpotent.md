# lem-weil-pbc-nakayama-nilpotent

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-nakayama-nilpotent.json`: item split into three source-faithful elementary steps; no new nodes. Mathlib verdict: no match for nilpotent-ideal Nakayama without finiteness assumptions, as already established by LeanSearch, LeanFinder/Loogle, and source grep.

## Attachments

None.

## WANTED

None.

## Problems found

None. The statement correctly identifies Stacks Algebra Lemma 00DV (11), and its two equivalent forms are parts (9) and (10). The existing Mathlib searches are complete and their no-match verdict is justified.

## Unfinished

Nothing.

## Review by E1

I checked the revised node against Stacks Algebra Lemma 00DV, parts (9)-(11), and the existing statement/dependency fields. The three steps are the source route: the induction gives the nilpotent ideal case, the quotient gives the submodule form, and the image substitution gives surjectivity. Each step is explicit and uses no undeclared reusable result; the node stays within its unit route. The recorded LeanSearch, Loogle/LeanFinder, and Mathlib grep searches support the no-match verdict. I accept the split.
