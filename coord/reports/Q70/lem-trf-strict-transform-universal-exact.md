# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-strict-transform-universal-exact.json`: statement item, split in seven steps; no Mathlib match for the global geometric assertion.
- No new DAG nodes and no new Mathlib leaves.
- `citations.json`: one literal statement quote for each of the 23 step/node citations.
- `searches.jsonl`: five searches actually run with msearch.py; the inherited item search records were retained. The sandbox scripts write JSON only; no Lean was written or compiled.

## Attachments

None for the item. I searched `WeilConjectures/` by the blueprint id and by strict-transform/universal-exactness concepts. `WeilConjectures/Mathlib/Algebra/Module/Torsion.lean` has the proved algebraic declarations `Submodule.torsion'QuotientMap_injective`, `Submodule.torsion'QuotientMap_surjective`, and `Submodule.torsion'QuotientMap_exact` (lines 190, 202, 215); they do not assert the global sheaf theorem. Its exactness lemma assumes a divisibility condition that this item's universal hypothesis must first supply. The existing power-torsion definition, submodule, and kernel-localization nodes already carry the corresponding project declarations; no attachment node was needed.

## WANTED

None. The item's complete source is available in `literature/stacks-project/divisors.tex`, Tag 080W, label `lemma-strict-transform-universally-injective`.

## Corrections and discrepancies

The item statement is unchanged. It agrees with 080W, restricted to the finite-type quasi-coherent centres already required by the supplied module-strict-transform definition. There is no added flatness, finite-presentation, Noetherian, separatedness, or nonzerodivisor hypothesis. I removed `def-pc-scheme-module-flat-over` and `def-weil-pbc-module-finite-type-presentation` from statement dependencies because their notions are not used, and added the fibre-product definition because the statement uses that construction.

The source's reduction to an identity blowup is compressed. I made its actual content explicit: after pulling back to the blowup, choose an affine neighbourhood where the exceptional ideal is principal; then apply the original universal hypothesis to the composite Spec(A/(a^n)) -> S. This is the same local exceptional-divisor/power-torsion route as 080W, rather than a different geometric theorem. The identity-of-pullback comparison is cited, not assumed to mean an arbitrary scalar functor.

### Source error

The last two sentences of the proof of 080W use `y` where they need `z` (or its image under the injection): from i(y)=a^n x and y=a^n z, the correct equation is a^n(x-i(z))=0, and the class of z maps to the class of x. Step 6 writes that equation. The proposition is correct and requires no statement correction.

I also found an unrelated statement discrepancy in the existing `lemma-nagata-power-torsion-localization`: its first displayed formula gives im(T -> N_s)=Gamma_a(N_s). As an ordinary module image this is false: for R=k[a,s] and N=R/(a), T=N, whereas 1/s in N_s=k[s,s^{-1}] is not in im(k[s] -> k[s,s^{-1}]). The true formula uses the image of T_s -> N_s (equivalently the localized submodule). The Lean declaration `Submodule.localized'_powTorsion` states this true version, and the node's displayed quotient isomorphism is also true. I did not edit that other worker's node and do not cite its faulty assertion. Step 4 instead proves the two fraction implications from `def-weil-pbc-module-localization-away`, including injectivity of T_s -> N_s.

## Unfinished work

None in this one-level split. The existing generic tool `lem-sc-tilde-preserves-finite-limits` and the existing quasi-coherent pullback theorem remain ordinary DAG dependencies; their proofs are not this item's work.

## Not duplicates

No new node was created. The whole-DAG/blueprint searches for strict transform, universally exact, torsion quotient, and power-torsion found the existing module strict-transform, affine pushforward, and Nagata power-torsion nodes. None states the global universal-exactness item except the item itself. I reused the available definitions, affine sheaf tools, and power-torsion facts. In particular, I did not turn the middle-exactness clause into a new lemma carrying the item unchanged.

## Review by Q70

I read the item, chapter `sec-trace-formula`, unit `sk-i-curve-zero`, the current main-20261015 ancestor proof `lem-trf-local-term-locality.proof.md`, the item's inherited ancestry, and the parent module-flattening proof. The item serves precisely the strict-transform sequence in Stacks 0815 paragraph 3 on that existing branch. It is not the unit's statement node, so no unit realization file is changed. I read the full statement and proof of Stacks 080W and the definition 080D with its preceding exceptional-divisor notation. For the affine inputs I read schemes.tex labels `lemma-spec-sheaves` (01HV), `lemma-widetilde-pullback` (01I9), `lemma-quasi-coherent-affine` (01IA), `lemma-equivalence-quasi-coherent` (01IB), and `lemma-kernel-cokernel-quasi-coherent` (01IC), and the blueprint principalization and power-torsion statements. Every cited DAG statement was opened and matched to its use; the literal quotes in citations.json include the appropriate clauses.

Step 1 uses the pullback-quasi-coherence node only for ordinary tensor pullback, the principalization theorem only for local generators of the exceptional ideal, affine-opens-basis for the cover, and affine-tilde-gamma-adjunction clause (3) for canonical affine representatives. The ideal is finite type as principalization requires. Its generator may become a zero divisor on C; the proof never assumes otherwise. Exactness of H comes directly from the hypothesis with T=S^b.

Step 2 uses the module-kernel statement's sectionwise kernel and the cokernel-image statement's clause (3), whose affine-sections conclusion is actually written in that statement. The source terms are quasi-coherent by Step 1. This is an elementary application of those two facts to the given short exact sequence, not a claim that sections of arbitrary sheaves preserve epimorphisms.

Step 3 uses fibre-product universality and affine-fibre-product coordinates, open-immersion base-change for the restricted open Z_n, the composition clause of module pullback, naturality in the affine-tilde-pullback theorem, and the affine-tilde unit isomorphism for sections. The base-change scheme Spec(A/(a^n)) has a morphism to S through V and S^b, so it is covered by the actual hypothesis. The elementary ring and module tensor/quotient isomorphisms are written with both inverse formulas. This proves injectivity modulo a^n, rather than trying to infer it from ordinary exactness.

Step 4 uses the definition of strict transform for its actual support kernel, principal-open sections for the restriction/localization maps, and the power-torsion kernel statement. It uses the definition and submodule node for T. The equality with the localized torsion submodule is proved by fractions: a^n m/s^r=0 supplies a denominator power s^k killing a^n m, then s^k m is a torsion numerator for the same fraction. Injectivity is checked by the same fraction relation. Affine-tilde-gamma-adjunction clause (4) gives the quotient sheaf. The initial draft cited the incorrect ordinary-image formula described above; I replaced that citation and calculation before delivery.

Steps 5 and 6 are the explicit elementary element chase from the torsion definition and the results already proved in Steps 2 and 3. Injectivity and surjectivity of the original module maps give the endpoints. At the middle, i(y)=a^n x and y=a^n z imply a^n(x-i(z))=0. This is exactly where universal injectivity modulo a^n is used. It is not a flatness argument or an appeal to an unnamed theorem.

Step 7 uses the full finite-limit-preservation statement to preserve the kernel and the colimit clause of affine-tilde-gamma-adjunction to preserve the cokernel. These imply the associated sheaf sequence is short exact; Step 4 identifies its actual morphisms. The final local-to-global argument spells out vanishing of the composite, local lifts, and injectivity by restriction. No new comparison lemma is hidden there. I declared the two off-unit generic tools in split_report.tool_uses; the other off-unit results are existing Mathlib leaves or project-closed tools.

I tested the construction on a=0 (all elements are power torsion, all quotients vanish), a a unit (no torsion, the original sequence), N_i=0, n=0 (the quotient base is empty and the divisibility implication is tautological), and a nilpotent exceptional image in C (all the N_i are torsion, so the quotient sequence is zero). No finite generation of modules or Noetherian assumption is needed. The non-universal sequence 0 -> Z --2--> Z -> Z/2 -> 0 demonstrates the need for Step 3: its torsion quotients fail middle exactness. All seven steps are below 2000 characters; they contain the item's local argument rather than relocating its clauses to children. The statement has no dispute, there are no new-node self-containment/Mathlib-leaf issues, no SGA source is used, and the report explicitly flags the two corrected source/DAG calculations.
