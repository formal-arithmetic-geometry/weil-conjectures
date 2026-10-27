# Q159: lem-sfb-fibre-regular-localization-universal-injection

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fibre-regular-localization-universal-injection.json`: existing statement, now split into five steps; Mathlib searches found no exact match. Statement and statement dependencies unchanged.
- `citations.json`: five verbatim statement extracts, one for every step/node citation.
- `report.md`: this report. `searches.jsonl` contains the search command's actual results.

No new nodes or new Mathlib leaves. An uncommitted draft for a separate localization lemma was dropped: it would duplicate an elementary consequence of the existing localization/tensor comparison and fraction-zero definition.

## Attachments

None. Searched the current project `lean/WeilConjectures/` for the blueprint id and for homothety, closed-fibre regularity and universal injectivity. No project declaration gives the entire item. The existing general algebra criterion is reused as a DAG dependency, not claimed as an attachment to this stronger conclusion.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Errors and changes

No statement dispute, source error, or route change. The item is Stacks Tag 05DF. Its source inherits Noetherian closed-fibre and finite closed-fibre-module assumptions from 05DE; those are automatic from the displayed finite presentations. More directly, the general criterion 046Y used in the proof does not assume Noetherianity of either base ring or closed fibre, so the proof below needs no additional Noetherianity lemma.

The proof now supplies the actual argument. The last sentence of 05DF describes localization as a directed colimit; the delivered steps expand that inference using the existing localization/tensor comparison and the explicit fraction-zero criterion. This is the same scalar-localization argument, not an alternate unit route. There is no assertion about the semilocal spectrum of 05DE, and none is needed.

The inherited blueprint ancestor is null, as confirmed by `tools/blueprint_refs.py ancestor`; its precise existing `from.place` and `via` chain are preserved. Searches of all imported blueprint nodes for the statement and for 05DF gave zero matches. I read the current latest unit proof's direct-image/compactification paragraph, rather than an older snapshot. This algebra prerequisite remains on its inherited flattening chain.

## Unfinished work

None in the one-level stage-1 split. No Lean files were written or compiler commands run. The maintainer's independent mathematical review remains part of the normal delivery process.

## Not duplicates

No new-node/existing-node pairs. Existing nodes reused: `lem-trf-valuation-general-mod-injective` (046Y), `lem-weil-pbc-flat-quotient-tensor-injective` (00HL), `lem-weil-pbc-localization-tensor-over-base` (00DK/00D2), and the tensor and localization definition nodes. The existing 05DF references in the two ancestor assassin-cover nodes invoke the present lemma; they do not replace it by an independent general statement.

## Mathlib search assessment

Retained all inherited searches and appended the actual Q159 searches from the command log. Ran LeanFinder, LeanSearch, Loogle and source grep; tried another phrasing targeting the general closed-fibre criterion, and a second source pattern targeting residue-field injectivity. The initial Loogle application without commas produced a parse/type error, recorded as unavailable, then the valid comma-separated query returned zero hits. No unavailable service was treated as a negative result.

Read `Flat/Basic.lean` around lines 628–635 and `Flat/TorsionFree.lean` around lines 51–79: these preserve existing scalar regularity under flat base change or require a regular base-ring scalar. They do not lift regularity from the closed fibre in the relative situation here. Read `LocalRing/Module.lean` around lines 314–340: the residue-field criterion assumes modules finite over the base and the target free over the base. The item only has finite presentation over S and flatness over R, so that result does not specialize to it. Localization and tensor facts are already Mathlib leaves in the DAG and are cited directly. No search was invented or repeated to replace an unavailable result silently.

## Review by Q159

I read the statement and proof of Stacks 05DF in `flat.tex`, including the 05DE assumptions it inherits. I also read Algebra 046Y at `lemma-mod-injective-general`, 00HL at `lemma-flat-tor-zero`, the fraction construction immediately before 07JZ in Section 00CM, the tensor universal property 00CX, tensor associativity with a bimodule 00D2, and tensor/localization 00DK. There are no new nodes needing further source review.

For Step 1, I checked multiplicative closure directly on the actual module N/m_R N: multiplication by st is multiplication by t followed by multiplication by s, so composition of their two injections is injective. This requires no associated-prime theorem or Noetherian hypothesis.

For Step 2, I opened the full statement of `lem-trf-valuation-general-mod-injective`. It asserts BOTH injection of the module map and flatness of the quotient, exactly what this step takes from it. Substituting M=N and u(n)=sn satisfies both finite-presentation hypotheses. Commutativity makes u S-linear; the displayed localization of the finitely presented algebra supplies essential finite presentation, and the given flatness is over the correct ring R. Its closed-fibre injectivity hypothesis is precisely membership in Sigma. The quotient is N/sN. The short exact sequence is then the kernel/image definition of the quotient, not a further flatness claim. This cross-unit citation is a generic algebra tool explicitly invoked by 05DF, and is declared in `split_report.tool_uses`; it does not replace any unit-level argument.

For Step 3, I read `lem-weil-pbc-flat-quotient-tensor-injective` itself. Its statement tensors with ANY R-module, with no flatness assumption on that module; the flat object is the quotient Q supplied by Step 2. It gives the required injection on L tensor N. I expanded the reversal to N tensor L instead of assuming a convention: the bilinear flip and its inverse come from the cited tensor definition, their compositions are identity on pure tensors, and the conjugated map sends n tensor x to sn tensor x. The definition explicitly says pure tensors generate, so this checks the entire map.

For Step 4, I opened `lem-weil-pbc-localization-tensor-over-base`. It permits an arbitrary ring map R to A and arbitrary multiplicative subset of A, not only a subset of R. With A=S, M=N and T=Sigma it gives exactly the displayed comparison and explicitly identifies the map from the unlocalized tensor product. Hence the localization is in S-scalars while universality is over R, as the item requires.

For Step 5, `def-weil-pbc-module-localization` explicitly states that z/1=0 iff some denominator kills z. Thus a single s in Sigma with sz=0 exists, and Step 3 applies to that same s and arbitrary L. Kernel zero implies injection by subtracting two inputs. This two-line argument is marked elementary; it is not made into a node restating the item's localization clause. Every citation has a verbatim extract in citations.json. No step exceeds 2000 characters, and the full proof has fewer than 3000 characters.

I tested N=0 and L=0 (all relevant maps have zero domain), s=1 and unit s (their multiplication is invertible), and the field-base case R=k, where fibre regularity is ordinary regularity and tensoring is exact. I also checked the potentially troublesome zero denominator: if 0 belongs to Sigma, Step 2 forces multiplication by 0 on N to be injective, hence N=0; localization at a set containing 0 therefore causes no counterexample. No assumption that Sigma avoids 0 is introduced. The argument never treats S as flat over R, never treats N as finite over R, and never assumes R Noetherian.

Against delivery-errors B–E: there are no statement-only new nodes with hidden proofs, duplicated elementary nodes, relabelled clauses, or missing definition references. The non-elementary claims are exactly the cited algebra criterion, tensor-injection theorem and localization comparison; I verified their hypotheses above. The elementary identifications are written explicitly. Sources use Stacks tags and labels; no SGA source is used. Statement and all five conclusions retain their original hypotheses and strength.
