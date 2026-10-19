# Stage-1 report: lem-per-prime-to-ell-decomposed-etale-finite-subcover

## Files written

- `lem-per-prime-to-ell-decomposed-etale-finite-subcover.json`: statement, split proof, citations, and blueprint fields updated; status `split`.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-prime-to-ell-decomposed-locus-constructible.json`: new statement-only node; Mathlib searches found no match.
- `citations.json`: verbatim citations for every proof-step dependency.

## Attachments

None. No sorry-free declaration in the project states this item or the new pointwise locus node.

## WANTED

None. The cited ILO paper and the existing DAG compactness nodes are available.

## Not duplicates

- `lem-per-prime-to-ell-decomposed-locus-constructible` vs `lem-per-completely-decomposed-etale-finite-subcover`: the new node permits every finite residue degree prime to $\\ell$, while the existing item requires residue-field isomorphism (degree one), so the statements differ.
- `lem-per-prime-to-ell-decomposed-etale-finite-subcover` vs `lem-per-completely-decomposed-etale-finite-subcover`: the item conclusion allows prime-to-$\\ell$ residue degrees and is strictly weaker than the existing completely decomposed conclusion.

## What was checked and corrected

The item statement was compared with ILO Exposé II Corollary 2.2.4 (printed p. 27) and retained exactly, including the absence of quasi-compactness and separation hypotheses on the individual étale sources. I read the existing completely decomposed finite-subcover split and its dependencies; it follows the same constructible-compactness reduction but cannot prove the prime-to-$\\ell$ conclusion because degree one is a stronger condition.

The new node is ILO Exposé II Proposition 2.2.2 (printed p. 26). It states that for an étale morphism over a Noetherian scheme, the locus of points admitting a residue-field lift of finite degree prime to $\\ell$ is ind-constructible, hence open in the constructible topology. I searched the full DAG and blueprint for this proposition, its locus, and its tags; no existing node states it. I also searched Mathlib with LeanFinder, Loogle, grep, and LeanSearch; the hits concern generic étale loci, residue-degree bookkeeping, or ordinary constructibility and do not specialize to this statement.

Step 1 uses the existing nodes for locally Noetherian schemes, minimal closed subsets, compactness of Noetherian spaces, quasi-separatedness, spectrality, and quasi-compactness of the constructible topology. I read each cited statement and verified that the finite affine Noetherian cover supplies the locally Noetherian and quasi-compact hypotheses. Step 2 applies the new pointwise locus statement separately to every $u_i$ and checks that its étale and Noetherian hypotheses are exactly those in the item; no quasi-compactness or separation of $U_i$ is used. Step 3 applies the already cited constructible-topology compactness to the open loci $C_i$ and unfolds their definition to recover the required finite residue-degree lifts, including the empty-scheme case. Every citation quote in `citations.json` is copied from the cited node's statement.

## Review by Q150

I read the item, the new node, the unit and chapter records, the existing completely decomposed finite-subcover node, all statements cited by the three steps, and ILO II Proposition 2.2.2 and Corollary 2.2.4. The source's pointwise proposition supplies exactly the non-elementary prime-to-$\\ell$ locus fact; the compactness argument then supplies the finite subfamily. I verified that Step 1's Noetherian-to-spectral chain has every required hypothesis, that Step 2's degree condition matches the item's `[\\kappa(z):\\kappa(x)]` condition, and that Step 3 uses only finite subcover compactness. I tested edge cases conceptually: an empty $X$ gives the empty finite index set; a one-point base reduces to choosing one member with a prime-to-$\\ell$ lift; a degree-one lift is included as a prime-to-$\\ell$ lift. The new pointwise node is strictly smaller than the item and is not a restatement or duplicate of the degree-one lemma. No source error, attachment, cycle, or unrecorded dependency remains.

## What could not be finished

Nothing at the natural-language DAG stage; the required dry run remains to be run.
