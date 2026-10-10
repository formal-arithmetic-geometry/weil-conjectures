# lem-weil-pbc-finite-type-field-finite-isolated-points

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-field-finite-isolated-points.json`: the item, split into four proof steps; no new nodes and no Mathlib match.

## Attachments

None. A search of the slopmaster2 Lean source by the item id, the isolated-point terminology, and the relevant Stacks tag found no sorry-free declaration stating this item.

## WANTED

WANTED: `literature/stacks-project/algebra.tex`, Lemma 00UK (lemma-etale-makes-quasi-finite-finite), proof lines 40362-40420, for the item's source. The repository's `literature/` tree does not contain the Stacks checkout; I read the corresponding TeX in `/home/ubuntu/c1-stacks-review/algebra.tex`.

WANTED: `literature/stacks-project/algebra.tex`, Lemmas 00FN, 00FR and 00E0, for the cited Noetherian, finite-minimal-prime, and basic-open facts. Their statements are already represented by existing DAG nodes; the same local TeX checkout was read for the source comparison.

## Source distinction

The Stacks passage says isolated closed points, while this item's statement quantifies all primes whose singleton is open. The proof below establishes the stronger statement directly: every such prime is minimal, so it lies in the finite minimal-prime set.

## What was wrong or incomplete

The imported item had no proof. Its existing Mathlib searches correctly report no single theorem for finiteness of isolated points. The split makes the implicit Noetherian argument explicit and observes that an open singleton prime is minimal, so the isolated set injects into the finite set of minimal primes. No statement correction or new support node was needed.

## What could not be finished

Nothing in the stage-1 split. This stage writes no Lean; the cited existing leaves remain independently maintained.

## Review by J1

I read the item's source passage, Algebra Lemma 00UK (lines 40362-40420), including the sentence that the finite-type fibre is Noetherian and therefore has finitely many isolated closed points, and I read the supporting source passages for 00FN (finite-type Noetherian permanence), 00FR (finite Noetherian irreducible components/minimal primes), and 00E0 (basic opens). I also checked the ancestor blueprint clause naming the finite set of isolated points as the induction parameter.

Step 1 cites `lem-weil-pbc-finite-type-algebra-noetherian`. Its hypothesis is met because the base is the field `k`, whose only ideals are `0` and `k`, and the item gives the finite-type map `k -> A`; the conclusion is exactly that `A` is Noetherian. Step 2 cites `lem-weil-pbc-noetherian-finitely-many-minimal-primes`, whose statement gives finiteness of the minimal-prime set for this Noetherian ring. Step 3 cites `lem-weil-pbc-spec-localization-away-basic-open`: from an open singleton `{q}` it supplies `f` with `q in D(f) subseteq {q}`. If `p subseteq q` is prime, `f notin q` implies `f notin p`, so `p in D(f) = {q}` and `q` is minimal. Step 4 uses the finite minimal-prime statement again to conclude that the isolated-prime set is a subset of a finite set. The proof-dependency list is exactly the union of these step uses, and no off-unit tool citation is present.

I tested the edge cases: `A = k` has one isolated (and minimal) prime; `A = k[x]` has no isolated prime; `A = k x k` has two isolated minimal primes; and the zero ring has empty spectrum, hence an empty finite isolated set. I searched the DAG and blueprint for the item wording, the 00UK clause, and the isolated/minimal-prime fact before writing; no duplicate node or Lean declaration was found. The item's existing LeanSearch, Loogle and Mathlib-source searches were retained.
