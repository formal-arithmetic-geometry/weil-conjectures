# Repair report: lem-coef-finite-free-extension

Group Q151; stage 1 only; 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-finite-free-extension.json`: repaired the returned split; the statement, Lean audit and imported metadata are unchanged.
- `citations.json`: regenerated for the 19 repaired proof steps, with a verbatim statement quote for every cited node.
- No new node files were needed. The extracted arguments are already stated by `lem-sf-ringed-finite-free-hom-base-change`, `lem-weil-pbc-mate-pasting`, and the existing `lem-coef-finite-etale-descent` node.

## Attachments

None.

## WANTED

None.

## What was wrong and what changed

The human return identified the former steps 7, 10, and 11 as non-elementary inline arguments. I retained their route and conclusions, then replaced them with 13 shorter steps. The internal-Hom argument now has a separate tensor--Hom transpose step and a separate application of the existing finite-free Hom base-change node. The coefficient-reduction argument now separately records tensor reassociation, the five quotient comparisons and the mate-pasting argument. The constructibility/map argument now separately records finite-Tor typing and the internal-Hom/Verdier mate argument. The unchanged later steps still use the existing pro-etale transport and étale recovery node. No proof step exceeds 2000 characters, and no duplicate node was created.

## Review by Q151

I read the retained item source `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md`, its proof, the current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-free-extension.proof.md`, and the existing DAG statements cited below. The finite-free route agrees with the source: finite residue quotient plus completeness gives finiteness of `O_L` over `O_E`, torsion-free over a DVR gives a basis, and the basis gives the quotient freeness. I also checked that the current item’s explicit etale/pro-etale typing and cofinal `en` levels are retained exactly as required by its imported statement.

The first six steps are unchanged. Steps 1–2 use the absolute-value, DVR, completeness, finite-over-complete, and DVR-free-module statements with the hypotheses `E ⊂ L`, the chosen uniformizers, and the finite residue quotient checked. Step 3 uses the restriction/extension adjunction and K-flat tensor descent to establish exactness, derived adjunction, bounded constructibility and preservation of the Tor interval. Steps 4–5 use the canonical direct-image comparison and Nagata compactification; I checked that `f` is separated finite type and that all schemes are Noetherian over the finite field. Step 6 applies the two left/right adjunctions and identifies the counit transpose; the finite-sum matrix argument and reflection by restriction of scalars are exactly the cited statements’ inputs.

The repaired steps are as follows.

- Step 7 is only the derived tensor–Hom adjunction and its evaluation normalization, using `lem-pur-rhom-global-sections` and `lem-weil-pbc-ringed-internal-hom-exact-restriction`; those nodes state the global-Hom identification and currying used here.
- Step 8 applies the existing `lem-sf-ringed-finite-free-hom-base-change` to the finite-free constant extension proved in step 2. Its statement gives the evaluation-defined isomorphism without a perfectness assumption, so it supplies exactly the hidden internal-Hom lemma and does not restate the item.
- Step 9 is the retained Verdier comparison and double-dual transpose, using the duality-pairing node; the evaluation identity is checked with the displayed tensor balancing.
- Step 10 is the retained field-extension composition argument. The ideal factorization, tensor reassociation and equality of transposes are checked for `E ⊂ L ⊂ H`, including the identity extension.
- Step 11 records `B_n ⊗^L_{A_n} A_m = B_m` and the balanced reassociation. The cited K-flat descent statement says precisely that these tensor complexes and maps reassociate.
- Step 12 applies the five existing same-field quotient comparison nodes at `A_n → A_m` and `B_n → B_m`; step 3 supplies finite-Tor constructibility after extension, and `en ≥ em ≥ 1` supplies the quotient indices.
- Step 13 uses the existing mate-pasting node for the direct-image, closed-exceptional and dualizing reduction squares. The cited dualizing comparison supplies the compact-support counit, and `lem-weil-verdier-preservation-strata` supplies the required dualizing finite-Tor inputs. The intermediate units and counits cancel by the cited triangle identities.
- Step 14 checks the finite-Tor constructibility of the constant rank-one complexes and their dualizing objects using `lem-weil-verdier-preservation-strata`.
- Step 15 applies mate pasting to the tensor–Hom square, uses `thm-coef-finite-hom` for the evaluation transposes, and composes with `cor-coef-finite-verdier`; this is the complete internal-Hom/Verdier reduction argument formerly inline in the returned step 11.
- Step 16 is the retained pro-etale site comparison. I checked the hypotheses `f` qcqs, input bounded below, finite Tor input, and the transported exceptional functor. The cited canonical-mate and site-comparison nodes identify the pulled-back maps, evaluation and double-dual maps.
- Step 17 is the retained étale recovery step. The existing `lem-coef-finite-etale-descent` node states bounded constructible finite-Tor outputs, the counit-defined etale map, its pro-etale pullback, and faithfulness for equality of diagrams; it is applied at `(n,m)` over `E` and `(en,em)` over `L`.
- Step 18 is the retained scheme-isomorphism/Frobenius transport argument using the adjoint-mate uniqueness node and the geometric-Frobenius definition. The automorphism has an inverse, so the transported site equivalences are isomorphisms.
- Step 19 is the retained cofinality and uniformizer-unit argument: `e ≥ 1`, the multiples `en` form a nonempty directed tail, and `(varpi_E^n) O_L = (varpi_L^{en})`; no equal numerical indices for different uniformizers are identified.

I opened every cited node and checked that each quote in `citations.json` is copied verbatim from its statement. I searched the whole DAG for the finite-free Hom and étale descent statements before reusing them; the former is the existing finite-free evaluation comparison, while the latter is the existing same-field étale recovery lemma, so creating either again would be a duplicate. The finite-free Hom edge cases `S=R`, zero complexes, and rank-zero direct sums reduce to identity or zero maps; the étale descent edge cases `m=n`, identity closed immersion and empty schemes likewise give the identity or zero comparison. The coefficient extension is finite free only where claimed, while quotient reductions continue to use derived tensor and finite-Tor hypotheses.

The repair changes only the proof-step factorization and its dependency union. It does not change the item statement, imported source, Lean record, or any target statement.
