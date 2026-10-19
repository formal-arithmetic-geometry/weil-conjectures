# Worker report: lem-coef-finite-free-compact-composition

Files written:

- `dag/nodes/sec-six-functors/lem-coef-finite-free-compact-composition.json`: repaired item node; the system clause is proved by identifying finite-free coefficient extension with a strict-system projection word and applying the strict-system projection composition identity.
- `citations.json`: 15 verbatim statement excerpts covering every citation in the four proof steps.

Attachments: none. I searched the project source for the item tag and coefficient-composition declarations; no sorry-free declaration states this item exactly.

WANTED: none.

## Not duplicates

`lem-coef-finite-free-compact-composition` vs `lem-pur-finite-free-compact-composition`: the latter states the ordinary finite-level coefficient comparison and composition equation; this item additionally states that the same equation is an equality of specified maps in the normalized semilinear system model before total limit.

`lem-coef-finite-free-compact-composition` vs `lem-pur-system-level-projection-formula-coherence`: the latter is the general strict-system projection-formula composition identity; this item specializes its second tensor input to the finite-free coefficient tower and identifies that specialization with the coefficient maps `alpha_h`.

`lem-coef-finite-free-compact-composition` vs `lem-coef-semilinear-derived-sections`: the latter supplies the enhanced semilinear localization and simultaneous operation models, while this item proves the finite-free compact-support composition square for a particular coefficient tower.

## What was wrong and what changed

The return correctly identified that the former Steps 2–4 cited single-level compact-support site coherence, single-level composition, and the finite-free extension lemma as if their statements lifted identities to semilinear systems. I removed that transported-evaluation argument. The repaired proof uses the strict-system compact-support realization from `lem-coef-finite-adjunction-diagram-realization`, and treats the normalized tower `(B_n)` as the second tensor input to the strict-system projection transformation of `lem-pur-system-level-projection-formula-coherence`. Under the finite-free tensor identifications, its evaluations are exactly the `alpha_h` maps defined in the item.

The desired equality is then the displayed strict-system projection composition identity, applied with `N=B_bullet`; the cited system node states that this equality holds in `D(\mathscr S_Z)` before total derived inverse limit. Thus no equality is inferred merely from level evaluations. The strict-system compactification/refinement node `lem-pur-system-compactification-pf-substitution` supplies the proper-refinement and cocycle compatibility needed to use the fixed compactifications in the item. The old unsupported uses of `lem-pur-compact-support-site-coherence` and the reduction clause of `lem-coef-finite-free-extension` were removed from the proof steps.

All four proof steps were rewritten with valid TeX delimiters and commands. In particular, the previous malformed `widetildealpha`/`quad` text and control characters are gone.

## Review by Q107

I read the item source `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/lem-coef-rational-operations.md` and its proof paragraph 8, the complete statements of `lem-pur-finite-free-compact-composition`, `lem-coef-finite-adjunction-diagram-realization`, `lem-coef-semilinear-derived-sections`, `lem-pur-system-level-projection-formula-coherence`, and `lem-pur-system-compactification-pf-substitution`, plus the chapter and unit records. The item statement, finite coefficient hypotheses, fixed-basis convention, and before-total-limit system clause were retained.

Step 1 uses only the reviewed Q57 statement. I checked that its `c_h` is the same proper counit-transpose followed by open-extension balancing used to define the item's `alpha_h`, and that its displayed equation has the same source and target after substituting `S=T_{-,n}` and `M=K`. Its ordinary-etale and pro-etale scope covers the finite-level witnesses.

Step 2 checks the missing system construction. The realization node explicitly says that the finite compact-support functors have functorial derived-coefficient-system realizations whose evaluations include quotient maps. The semilinear node supplies simultaneous tensor, open-extension, proper-direct-image, and mate models. I checked the strict-system projection node's statement: it forms the same `F_h` and composition comparison in those simultaneous models. The tower `B_n=S/pi^nS` is normalized over `A_n` because the fixed `R`-basis gives `B_m \otimes^L_{A_m} A_n \cong B_n`; finite freeness gives the tensor identifications. The Q57 definition of `c_h` then identifies the evaluated projection word with the item's `alpha_h`.

Step 3 applies the exact displayed strict-system projection identity from `lem-pur-system-level-projection-formula-coherence` with `M=K_bullet` and `N=B_bullet`. I checked the source and target under the canonical associativity identifications: the left side is the `B`-coefficient compositor after the two `alpha` maps, and the right side is the `gf` coefficient map after the `A`-coefficient compositor. The node explicitly says this is an equality in the system derived category before total inverse limit, so the return's possible `lim^1` objection does not arise.

Step 4 checks compactification dependence. The strict-system compactification node states the refinement intertwining equation and the identity/composition/cocycle laws before evaluation. I used that statement to transport the projection word to the fixed compactifications and the specified `gamma` maps. The semilinear-section statement confirms that evaluation and composition preserve the specified coherent constructions; evaluation is used only to identify the already-established system map with the finite map, never to prove the system equality.

I checked the edge cases `L=E`, identity morphisms, zero complexes, one-level systems, shifted complexes, and empty schemes: the coefficient tower becomes the identity tower or the relevant zero map, and the strict-system projection identity specializes accordingly. I ran the retained Mathlib search log only as inherited evidence; no new node was created, so no new Mathlib search was required. No Lean was written or compiled.

What could not be finished: nothing in this repaired stage-1 split.
