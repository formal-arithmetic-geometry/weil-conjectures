Files written:

- `dag/nodes/sec-picard-framework/lem-sc-torsion-sections-generic.json` — statement, unsplit; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-torsion-subsheaf-quotient.json` — statement, split; no Mathlib match.

Attachments:

- None for the delivered item or the new node. The existing `lem-weil-pbc-quasi-coherent-module-kernel`, `lem-weil-pbc-module-stalk-exact`, and `pqf-lem-pushforward-qcoh` nodes were searched and cited.

WANTED:

- None. The Stacks source file was available locally at `/home/ubuntu/c1-stacks-review/divisors.tex`.

What was wrong or incomplete:

- The imported item was unsplit and had no proof. Its statement was retained, with the meaning of stalk torsion and torsion-free made explicit.
- The blueprint proof used the generic-point torsion criterion without a node. I created `lem-sc-torsion-sections-generic` for Tag 0AXR rather than hiding that fact in an elementary step.
- The generic-point pushforward fact is supplied by the existing cross-unit `pqf-lem-pushforward-qcoh`; this is declared as a tool use because the Picard unit has no replacement node for that generic sheaf fact.

What I could not finish:

- No Lean was written or compiled, as required for stage 1.

## Review by K1

I read the item source in `literature/stacks-project/divisors.tex`, specifically the statements labelled `lemma-torsion-sections` (Tag 0AXR) and `lemma-torsion` (Tag 0AXT), and compared each hypothesis with the node: integrality supplies the generic point and domain stalks, quasi-coherence supplies the module sections, and the generic-point map is the stated `j`. I also read the Picard Riemann–Roch blueprint proof paragraph that introduces this item. The new node reproduces all four equivalent conditions of 0AXR and defines stalk torsion by annihilation by a nonzero local element; its source, dependencies, and blueprint ancestor were checked against those files.

Step 1 of the item uses exactly the new 0AXR statement to show that generic-zero sections are stable torsion sections, then uses the existing kernel node for quasi-coherence and the existing pushforward node for quasi-coherence of `j_* F_eta`. I checked the pushforward hypotheses: the generic-point morphism is quasi-compact and quasi-separated, so the cited statement applies. Step 2 writes the germ argument directly: a stalk germ in the kernel is represented on a neighbourhood, and the 0AXR equivalence identifies precisely the germs killed by a nonzero local element; the converse is obtained after shrinking to where the annihilation equation holds. Step 3 uses 0AXR at the generic point and the fact that the torsion kernel has zero generic stalk to show every torsion quotient section is zero; this is precisely the quotient assertion in 0AXT. No step is marked elementary because each relies on a cited sheaf or torsion lemma.

I searched all DAG nodes and the blueprint for existing 0AXR/0AXT-equivalent statements before creating the child; no matching node was found. I searched the slopmaster2 source for the item id and torsion-subsheaf declarations and found no exact declaration. LeanSearch was unavailable (HTTP 500); LeanFinder, Loogle, and Mathlib grep found only generic torsion predicates and no scheme-sheaf theorem, so both nodes remain unsplit with no Mathlib match. Small cases checked were `F = 0`, `F = O_X` on an integral affine scheme, and a skyscraper module at a closed point: the generic criterion gives zero torsion for `O_X`, all sections for a module supported away from the generic point, and the quotient is torsion-free in each case. JSON parsing and the repository DAG checker passed; the checker reported only pre-existing global reach/route diagnostics.
