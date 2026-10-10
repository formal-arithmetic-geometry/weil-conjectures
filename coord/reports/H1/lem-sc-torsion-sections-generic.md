# Stage-1 delivery: lem-sc-torsion-sections-generic

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-torsion-sections-generic.json`: split into four steps; no new nodes and no new Mathlib leaves.

## Attachments

None. Search of `WeilConjectures/` and `Comparator/` for the item id, the 0AXR tag, torsion sections, and generic torsion found no declaration stating this item.

## Wanted

None. The cited `divisors.tex` and `schemes.tex` files are present in `literature/stacks-project/` in this checkout.

## Issues and limits

Stacks 0AXR explicitly omits its proof. The imported item had only the statement and no proof. I supplied the affine localization calculation and marked `proof_origin.by` as `agent`. The statement itself is unchanged. No mathematical gap remains in the four implications. The item did not have a `lean_audit` field, so the source search was done directly and no maintainer-owned audit field was added.

## Review by H1

I read Stacks Divisors, lemma-torsion-sections, Tag 0AXR, in `divisors.tex` lines 1649-1665 and confirmed its hypotheses and four clauses against the item: integral scheme, generic point, quasi-coherent module, nonempty open, and one section. I read Schemes, lemma-spec-sheaves, Tag 01HV, lines 691-727 for affine sections and stalks. I also read the item's parent `lem-sc-riemann-roch` blueprint proof text, specifically "The torsion part" sentence about an element of `F_x` dying in `F_eta`. The item is a generic form of exactly that sentence. No new node was made, so B1-B9 and the new-node small-case requirement do not arise; I nevertheless checked the existing nodes and the small cases below.

Step 1 uses `pqf-def-coherent` only for an affine `W` containing `x`; I then checked the elementary principal-open basis argument for `D(f) subseteq W cap U`. `lem-weil-pbc-spec-module-tilde-sections` supplies the denominator-clearing equation on `D(f)`, and the unit germs of `f` transfer torsion and vanishing back to the section represented on `W`. `lem-weil-pbc-spec-tilde-stalk-localization` identifies the two germs of `tau_W(m)` with localizations, while `lem-sc-integral-scheme-stalks-in-function-field` supplies the domain and fraction-field identifications. I verified each cited statement says precisely that much. Step 2 uses the zero criterion in the localization statement to obtain `a m=0`; `def-weil-pbc-module-stalk` gives multiplication on germs, and `s_x=f_x^{-k}(tau_W(m))_x` then shows `a_x` kills `s_x`. The integral-stalk node ensures `a_x` remains nonzero. Step 3 applies that node's injective map `O_{X,x} -> k(X)` to a nonzero annihilator and uses the field property of `def-sc-function-field`; invertibility in the field makes `s_eta=0`. Step 4 uses the integral scheme's generic point being in every nonempty open and the definition of direct image along `j` to identify the image on `U` with `s_eta`. The remaining arrows are immediate because `U` is nonempty. The source states all four implications but omits their argument, so these calculations are identified as agent-written in the node rather than attributed as a proof from Stacks.

For E1-E5, the only ring used as a domain is `A=O_X(V)` for a nonempty affine open of an integral scheme; the cited integral-stalk node gives its injection into the function field. The annihilator from Step 2 is nonzero before and after passage to `O_{X,x}`. In Step 3, an annihilator from `O_{X,x}` remains nonzero in the field by the cited injection. I tested `X=Spec k`, where all four clauses reduce to `s=0`; `X=Spec Z, F=O_X`, where a nonzero section satisfies none; `F=~(Z/n)` with `n>1`, where every section dies generically and is torsion at every point; and `F=~(Z + Z/n)`, where the four conditions hold exactly when the free coordinate of the section is zero. These also check the zero section and the generic point as the chosen `x`. There is no use of another node's proof, no cycle, and no reliance on an unstated hypothesis. I corrected Step 1 while reviewing it: the affine neighbourhood must be chosen from the quasi-coherence definition so that its presentation as `~M` is justified directly by the cited definition.
