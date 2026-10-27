# Stage-1 report: lem-sfb-generic-fibre-assassin-containment-spreads

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-generic-fibre-assassin-containment-spreads.json: item, statement unchanged, complete split following Stacks Tag 05KP.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-associated-points-primes.json: one new statement-only node, Tag 02OK, unsplit; no exact Mathlib match.
- citations.json: one verbatim statement quote for every cited node at each proof step.

One new node, zero Mathlib leaves. No Lean file was written, no compiler/build was run, and the shared repository was read only.

## Attachments

None. Searched WeilConjectures by the exact blueprint tag, assassin, associated points/primes, generic-fibre terminology, and affine associated-point terminology. There is no project declaration stating the item or the new general scheme comparison. The generic-flatness algebra declaration is only a partial ingredient, not an attachment. Mathlib associated-prime localization results likewise do not state the scheme comparison.

## WANTED

None: all literature needed is present.

## Audit and changes

The item is a new unsplit leaf of the 05KR constructibility argument. Its statement agrees with 05KP, including the absence of Noetherianity on the base and quasi-compactness of U. No statement dispute was found. Its inherited Mathlib searches and blueprint fields were retained. Fresh item searches were also run through msearch.py; the new node has both natural-language phrasings, LeanSearch, Loogle and grep, with actual logged answers. I read the returned associated-prime localization declarations in Mathlib/RingTheory/Ideal/AssociatedPrime/Localization.lean:76-141. They provide algebraic ingredients, not a theorem about sheaf associated points. The three grep hits in RingHomProperties concern arbitrary ring-hom properties and are unrelated.

The source proves generic multiplication injectivity through localization in principal opens and 0565. Step 5 instead applies the existing associated-prime localization detection theorem 0311 directly: at each associated prime some chosen principal element is a unit. This keeps the same generic-flatness proof and avoids creating a redundant module version of 0565. Flatness implies torsion-freeness by tensoring the injective scalar multiplication on A, exactly the proof of 0538; this two-line fact stays an elementary step. The localized cokernel is checked by the explicit fraction calculation, and the final assassin containment is checked by an element annihilator; neither is made into a redundant new node.

The ancestor command prints blueprint.from.node = None for this existing chain. I retained that inherited null root, the full via chain, and the detailed place; the new node adds the item in front of via. Searches of all imported blueprint nodes by associated/assassin, affine associated points, 02OK, 0565 and 05KP found no blueprint node stating the new comparison; same_as remains []. Read the current latest blueprint thm-sf-ctf-stability.proof.md, the chapter record and the unit record. This work is within the inherited algebraicity/flattening prerequisite chain of direct-image preservation; it changes no unit route or target.

## Not duplicates

lem-sfb-affine-associated-points-primes vs lem-trf-affine-minimal-prime-stalk-annihilator: the existing 02OK citation only gives a stalk annihilator for a minimal prime of a Noetherian affine ring and the structure sheaf. The new statement compares arbitrary quasi-coherent sheaves with their modules of sections and gives the converse for every finitely generated prime; neither minimality nor the structure-sheaf restriction is imposed.

The other associated-point nodes were also read: def-trf-relative-assassin only defines associatedness; lem-trf-flat-pullback-associated-points concerns a flat morphism and Bourbaki's formula; lem-sc-ass-weakass-* compares association with weak association; lem-sfb-noetherian-associated-points-finite only asserts finiteness. None states 02OK. The existing generic-flatness, localization detection and flat-quotient tensor nodes are reused instead of duplicated.

## Review by NY

I read the full proof and statement of Stacks more-morphisms.tex, Tag 05KP (lemma-good-case), and divisors.tex, Tag 02OK (lemma-associated-affine-open), including the finite-generation condition in its converse. I also read the proofs of Algebra 0565, the statement and beginning of the proof of 051T, the statement/proof of 00HL, and More on Algebra 0538. The new node is exactly 02OK: forward association needs no Noetherian assumption; the converse needs a finitely generated prime, and hence applies on every Noetherian fibre. Its proof is deliberately deferred, rather than hidden in its statement.

For Step 1 I opened the cited reduced-affine-base model: its statement explicitly gives the integral affine W, unchanged residue fields, identical fibres, and a homeomorphism onto an open of Y. The base-change containment node applies to any base change, with no flatness restriction, and gives the equivalence actually used. The two pullback nodes explicitly preserve quasi-coherence and finite type. This avoids silently replacing Y by an integral scheme without accounting for the coefficients and all fibres. The generic-flat model is stronger than needed, but is an existing generic tool; it supplies no part of the desired containment assertion.

Step 2 uses the finite-affine-cover clause of the finite-type definition, not an unstated separatedness assumption. Associatedness is local by its stalk definition, and the finite intersection contains the generic point; I wrote out both facts. Empty X gives the immediate V=Y case. In Step 3 the finite-generating-sections node explicitly says the section module is finitely generated, the tilde/Gamma counit reconstructs F, and the pullback-affine-sections node explicitly gives the tensor comparison and its naturality. The displayed maps prove the tensor reassociation. The finite-type algebra Noetherian node is used only over a residue field, where its hypotheses hold, never over A. This verifies the hypotheses for the new 02OK node at both ends of the argument.

Step 4 uses the basis statement of the basic-open node and the compact-subsets statement of the Noetherian-space node. The generic spectrum is Noetherian by the radical-ideal chain argument; only the generic-fibre open is made compact. Thus no quasi-compactness is added to U. In Step 5 the module-localizations node applies to an arbitrary module over a Noetherian ring, so it applies to N_K without another finiteness assumption. Its exact conclusion is injectivity into the product over associated primes. The affine comparison identifies precisely those primes with the points in the hypothesis, so the chosen g_j invert at each such prime.

In Step 6 the simultaneous-flatness node assumes only a finite-type algebra over a domain and a finite module. The finite module used is N direct sum C, so this one application flattens both source and quotient. I wrote out the split inclusion/projection argument making both summands flat from the definition. Step 7 tensors scalar multiplication on A, then uses the zero-fraction criterion; it does not assume the kernel I is finitely generated. Step 8 proves the localized quotient identification explicitly: h^e[v]=0 gives h^e v=mu(n), with the denominator exponent adjusted in the displayed preimage. Step 9 invokes the flat-quotient tensor node whose statement explicitly requires flatness of the cokernel, rather than merely flatness of N. It applies over A, as the generic-flatness node gives A-flatness. Its residue-field map is identified by the explicit inverse powers of h, so no comparison of unnamed maps is assumed.

Step 10 uses the new affine comparison in the reverse direction and the element-annihilator definition only. A point outside all the principal opens would give a nonzero vector killed by mu_kappa, which contradicts the proved injection. In Step 11 I checked the finite intersection and the pointwise descent equivalence back to the original possibly nonreduced base. Every cited statement was opened; citations.json uses literal text from those statements, not their proofs. The off-unit statements are declared individually in split_report.tool_uses as generic algebra or affine-sheaf tools. The main geometric route is still 05KP's generic-flatness route.

I checked B1--B10: the new node is statement-only and self-contained, its objects and associated notions are defined or cited, its source tag/label is correct, and its searches and blueprint provenance are real. No false Mathlib leaf or closed Lean attachment is asserted. For C1--C8 I checked the exact statements used at every step, removed the need for an uncited 0565 module generalization, included finite-type pullback explicitly, checked that no cited node depends on the item, and declared the generic tools. For D1--D5 the new 02OK comparison is a genuine smaller lemma, not a clause or renamed copy of the spreading conclusion; the steps themselves carry the construction of h and the fibre argument. For E1--E7 I checked the base may be non-Noetherian/nonreduced, source need not be separated, U need not be quasi-compact, and all tensor comparisons use residue-field fibres rather than an incorrect quotient by a prime.

Small cases: F=0 gives vacuous associatedness and zero multiplication maps; U=X gives the claim on the whole base; U_eta empty permits m=0 and generic N_K=0 (0311), then flatness makes N_h=0 so the same argument works; empty source is explicitly handled; B_kappa=0 has no prime/associated points; nilpotents in the base are removed with the unchanged-fibre comparison rather than discarded silently. For 02OK I tested a field, the zero module/ring, and k[epsilon]/epsilon^2: annihilators on the stalk match the corresponding associated prime without requiring reducedness. Every proof step is below 1100 characters, so no step exceeds the 2000-character review threshold.

## Unfinished work

Nothing required for this stage-1 split. The single new 02OK statement remains unsplit by design and joins the DAG queue. Delivery validation follows below.
