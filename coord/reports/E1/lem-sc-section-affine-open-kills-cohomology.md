Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-section-affine-open-kills-cohomology.json`: item, split with two proof steps; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology.json`: statement-only supporting node for Stacks 09MR; no Mathlib match.
- `citations.json`: verbatim statement excerpts for all step citations.

Attachments: none.

WANTED: The repository checkout does not contain `literature/stacks-project/`; I read the corresponding local Stacks source at `/home/ubuntu/c1-stacks-review/coherent.tex`, including Lemma 01XR (`lemma-section-affine-open-kills-classes`), Lemma 09MR (`lemma-invert-s-cohomology`), and Lemma 01XB (`lemma-quasi-coherent-affine-cohomology-zero`).

What was checked or corrected: the imported item had no proof. I searched the whole DAG, blueprint index, and both Lean source trees for the item tag and theorem names; no existing node states 09MR and no sorry-free Lean declaration states either theorem. The existing `pqf-lem-affine-vanishing` node states exactly the affine quasi-coherent cohomology vanishing used here, so I cited it rather than creating a duplicate. The new node states the full localization result needed by the source proof, introducing X, L, s, F, the graded cohomology module, its graded ring, the quasi-compact/quasi-separated hypothesis, and the localization map. It is statement-only as required for an unsplit supporting node.

## Review by E1

I read the item source and hypotheses against Stacks Lemma 01XR: X is quasi-compact and quasi-separated, L is invertible, X_s is affine, F is quasi-coherent, p is positive, and xi is a cohomology class. I read the complete 09MR statement in the local `coherent.tex` source and made the supporting node state its localization isomorphism, including the map `xi/s^n` to `s^{-n} xi`. I also opened the existing `pqf-lem-affine-vanishing` node and verified that it says higher cohomology vanishes for every quasi-coherent module on every affine open.

Step 1 cites exactly those two statements. The localization node supplies the identification of the localized graded cohomology with cohomology on X_s; the affine-vanishing node applies because restriction of a quasi-coherent module to an open subscheme is quasi-coherent, and p>0. Step 2 uses the localization definition: a class whose localization is zero is killed by a power of the denominator, and the degree-e action is precisely the map induced by `f` mapping to `f tensor s^e`. This is the only elementary algebraic step. The citations file quotes verbatim text from each cited node.

I tested edge cases in the statement while checking the split: if xi=0, e=0 works; if s is the unit section, X_s=X and affine vanishing forces xi=0; if X is empty, the cohomology group is zero. Mathlib searches for the new node used LeanSearch, LeanFinder, and a source grep under Mathlib's algebraic geometry directory; no matching declaration was found. The item already contained the correct blueprint ancestor/place and has been given a two-step proof, proof dependencies, proof origin, split report, and status `split`.

What could not be finished: no Lean compilation is appropriate at stage 1, and the local repository lacks the Stacks checkout under `literature/`; the source was nevertheless read from the supplied local Stacks checkout and the expected literature path is recorded in the node source fields.
