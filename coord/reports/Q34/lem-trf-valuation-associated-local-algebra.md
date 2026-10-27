# Stage-1 delivery: lem-trf-valuation-associated-local-algebra

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-associated-local-algebra.json`: statement, split; five proof steps, with every non-elementary input cited. The statement is unchanged. No exact Mathlib match.
- `citations.json`: eleven entries, one for every step/node pair, using verbatim complete statement quotes.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The searches added to the item are the five actual calls recorded in `searches.jsonl`; the inherited search records remain intact.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and the valuation/associated-prime notion, including the ring-theory tree. No project declaration states the valuation specialization implication. The associated-prime localization results returned by Mathlib do not give specialization to the closed fibre.

## WANTED

None. All sources used are present in the read clone.

## Findings and corrections

The item had no proof. Its statement is the algebraic content of the third proof paragraph of Stacks 0GSI, and is correct. I retained every hypothesis and conclusion. I corrected the bibliographic description from “nonzerodivisor power” to the actual source's prime-avoidance/nonzerodivisor selection argument; no power is needed. I did not change the unit, chapter, ancestor, blueprint fields or imported searches.

The whole-DAG tag and keyword searches found existing nodes for 00LC, 00LD, 00DS and 0GSG, and the closed-fibre Noetherian fact. In particular, I did not create a duplicate “regular element in a primary ideal” node: the radical argument is a short elementary inference preceding the existing prime-avoidance theorem. I did not cite `lem-pc-localization-preserves-nonzerodivisor`: it concerns a ring and a principal localization, whereas this proof needs a module localized at a prime. The required assertion follows immediately from the explicitly cited localization equality criterion, and is written out.

Blueprint searches using `tools/blueprint_refs.py search` for “valuation associated”, “associated primes”, and “prime avoidance” found no matching blueprint nodes. The ancestor command gives `lem-trf-local-term-locality`, agreeing with the inherited `blueprint.from.node`. The item is not a unit key node. The current ancestor's blueprint update and the unit/chapter records were read; this local algebra item remains in the inherited semistable-alteration branch, without changing any route. Existing Mathlib leaves and definitions are tools, and the two valuation results belong to the item's own unit, so no off-route tool declaration is needed.

## Not duplicates

No new node was created. The existing statements supply every ingredient; no new/existing node pair needs adjudication.

## Review by Q34

I read the complete local algebra paragraph of Stacks Tag 0GSI (`more-morphisms.tex`, lemma-associated-point-specializes), including its final generic-fibre contradiction. I also read Tag 0GSG (lemma-mod-injective-valuation-ring), its hypotheses and proof, and the statements and proofs of Algebra Tags 00LC (lemma-finite-ass), 00LD (lemma-ass-zero-divisors), 00DS (lemma-silly), 00HT (lemma-flat-localization), and 00DK (lemma-tensor-localization). There are no new-node sources to review.

Step 1 uses `lem-trf-valuation-closed-fibre-noetherian` exactly for the Noetherian property of $R$. Its local essentially finite type map and valuation-ring hypotheses are present. Finiteness of $L$ is not silently inferred from that node's finite-presentation clause: I reduce an explicit finite generating family of $N$, using `def-weil-finitely-generated-module`. Consequently `lem-weil-pbc-noetherian-associated-primes-finite` applies to the Noetherian ring $R$ and finite module $L$. Its statement is about module associated primes, not just ring associated primes.

Step 2 invokes `lem-weil-pbc-prime-avoidance` only after proving that the image ideal $J$ of $\mathfrak q$ is contained in none of the associated primes. I checked the proof of this assertion: the inverse image of an offending prime contains $\mathfrak q+\mathfrak m_AB$, then its radical $\mathfrak m_B$, so equality forces the offending prime to be $\mathfrak m_R$. This contradicts the temporary assumption. The cited avoidance statement requires a nonempty finite family, so I handle the empty family separately by taking $g=0$. Each member of the nonempty family is prime, satisfying the stronger-than-required primality condition. The quotient map lets us lift an element of $J$ to $\mathfrak q$ itself.

Step 3 uses the statement of `lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes`, rather than its ring-module specialization. Avoidance gives injective multiplication on $L$, including the empty-family case. I read `lem-trf-valuation-finite-module-injectivity` and checked its variables with source and target both $N$: finite $B$-modules, $B$-linearity of multiplication, $A$-flat target, local essentially finite type map, and precisely this injective quotient map. Its conclusion gives injectivity on $N$, which is all that this proof uses; no finite-presentation hypothesis was inserted.

Step 4 uses `lem-weil-pbc-localization-flat` for the fraction field, verifying its three localization conditions directly from fractions in a domain. It then uses the actual injective-tensor theorem `lem-trf-flat-tensor-preserves-injection`, with flat module $K$ and the $A$-linear injective map from Step 3. The tensor factors in that theorem are in the opposite order to $N_K$. I therefore spell out the inverse exchanges on pure tensors, justified by the universal property in `def-weil-pbc-module-tensor-product`; the exchanges commute with multiplication by $g$. No unjustified tensor exactness is hidden behind a flatness definition.

Step 5 uses only the equality criterion of `def-weil-pbc-module-localization` and the annihilator definition in `def-weil-pbc-annihilator-associated-primes`. If $g(v/s)=0$, some allowed denominator $t$ kills $gv$; injectivity gives $tv=0$, proving $v/s=0$. This works for arbitrary modules and arbitrary prime localization, without a Noetherian hypothesis on $B$ or $T$. The assumed associated maximal ideal supplies an annihilator witness; its properness proves that witness nonzero, and $g$ belongs to that maximal ideal because it belongs to $\mathfrak q$. The resulting contradiction is exactly the source's last inference.

I checked B--E against the actual files: all objects are introduced, all non-elementary inputs are existing nodes, every `uses` has a verbatim statement quote, no step invokes a cited node's proof, no new clause-restatement node is introduced, and there is no downward dependency on the parent specialization theorem. None of the steps exceeds 2000 characters. I checked the field-base case ($\mathfrak m_A=0$), the zero-module case (excluded by the generic associated-prime hypothesis), the empty associated-prime family, and $\mathfrak q=0$. In the last case the radical argument correctly rules out any closed-fibre associated prime except the maximal ideal; the same contradiction works. No statement dispute was found.

## Unfinished work

None in the split. Existing dependency nodes retain their own independent stage states. Only stage 1 was performed: no Lean was written, no compiler or Lake/build tool was run, and all writes are within this item's sandbox.
