# Stage-1 report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-set-iso-classes-bounded-size.json`: item, split with no new nodes.
- `citations.json`: three verbatim citations to `def-sp-grothendieck-abelian`.

## Attachments

None. I searched the slopmaster2 `WeilConjectures/` and `Comparator/` trees for the item id and its key notions; no declaration states this lemma.

## WANTED

None. The source is available in the machine review mirror at `/home/ubuntu/c1-stacks-review/injectives.tex`; the node keeps the project source path `literature/stacks-project/injectives.tex`.

## Not duplicates

`lem-pur-kinjective-set-iso-classes-bounded-size` vs `lem-pur-kinjective-acyclic-quotient-complexes-bounded-size`: the latter concerns bounded-above acyclic complexes and a uniform cardinal bound, while this item concerns individual objects and their isomorphism classes.

## Review by C1

I read the source proof of Stacks `lemma-set-iso-classes-bounded-size` in `injectives.tex` (the review mirror has the same file referenced by the node). I also read `def-sp-grothendieck-abelian`; its statement supplies exactly the generator and small-colimit hypotheses used below. Step 1 follows the source: for each proper subobject choose a map from the generator whose image escapes it, and take the coproduct; the image cannot lie in any proper subobject, so the map is epi, and the number of summands is bounded by the size. Step 2 checks the set argument explicitly: for each cardinal at most `kappa`, subobjects of the corresponding coproduct form a set and kernels classify quotient isomorphism classes; taking the set-indexed union remains a set. Step 3 applies Step 1 to place every bounded-size object among those quotients. Each cited statement says the generator and small-colimit facts used by the corresponding step, and the remaining arguments are elementary set and abelian-category reasoning. I tested the edge case `M = 0` (the empty coproduct maps epimorphically to zero) and the case `kappa = 0` (only objects with no proper subobjects are included); no statement change was needed.

## What was wrong or incomplete

The imported node had no proof. I filled its blueprint split metadata and added the complete three-step proof; no new node was necessary because the source proof is elementary once the Grothendieck-abelian definition is cited.

## What remains

Nothing for this item.

## Second reading by C1

- Statement: checked against Stacks `lemma-set-iso-classes-bounded-size`, including the definition of generator and the cardinal bound; verdict: correct.
- Step 1: checked against the source proof and the generator clause of `def-sp-grothendieck-abelian`; verdict: correct, including the zero object and empty coproduct cases.
- Step 2: checked against the source proof and the set-theoretic quotient-by-kernel argument; verdict: the original proof omitted the nontrivial fact that subobjects form a set.
- Step 3: checked against the source implication from (1) to (2); verdict: correct after Step 2 is supplied.
- Existing node `def-sp-grothendieck-abelian`: checked for the small-colimit and generator hypotheses; verdict: cited correctly.
- New node `lem-pur-kinjective-set-of-subobjects`: checked against Stacks `lemma-set-of-subobjects`; verdict: necessary unsplit auxiliary statement, with its abelian-category and generator notions explicitly cited and no exact Mathlib declaration.

Changes made: added `lem-pur-kinjective-set-of-subobjects`, cited it from Step 2, and added its verbatim citation. This makes the set-of-quotients argument explicit instead of treating well-poweredness as elementary.
