## What changed

Proved `Algebra.exists_etale_popescu_quotient_map` in
`Sheaf.RingTheory.PopescuEtaleQuotientMap`, keeping its signature and public imports
unchanged. The map is constructed explicitly by polynomial evaluation, localization,
and quotient descent. A private proved helper `Algebra.flat_quotient_map` transfers
flatness through quotient base change. The main proof descends flatness through the
admissible inclusion, contracts the equality of maximal-ideal images, proves vanishing
of relative residue differentials from the spanning hypothesis, obtains finite
presentation by Hopkins–Levitzki, and applies Mathlib's flat unramified étale criterion.

Added proof-only imports of `Mathlib.RingTheory.Smooth.Fiber`,
`Mathlib.RingTheory.Unramified.LocalRing`, `Mathlib.RingTheory.HopkinsLevitzki`,
and the already proved `Sheaf.RingTheory.FlatPermanence`.
Updated the existing DAG node's proof, proof dependencies, and proof origin to match.
The blueprint unit's realized statements and proof steps are preserved.

## Proved and sorry left

Closed the one original hole: `Algebra.exists_etale_popescu_quotient_map`
(node `lem-weil-pbc-popescu-etale-quotient-map`). No holes added or left in this delivery.
The module compiles cleanly using the mandated local compiler (final compile: 23.9 s).
The private helper `Algebra.flat_quotient_map` is also proved. No new data definition,
axiom, or choice from an unproved existence statement is introduced.

## No longer needed

Pruned `lem-weil-pbc-noetherian-local-quotient-artinian-local` from this node's proof
requirements: the base quotient needs only to be local and Noetherian, and the ambient
quotient needs only to be local. Target Artinianity comes directly from admissibility.
This leaf has a Mathlib realization, so no separate Sheaf module is removed.
The final step does not need an étale-locus argument or uniqueness of the target prime.

No original import was removed: the public imports support the unchanged statement.
Removed trial proof imports `Mathlib.Algebra.MvPolynomial.Eval`,
`Mathlib.RingTheory.Ideal.Quotient.Nilpotent`, `Mathlib.RingTheory.LocalRing.Quotient`,
`Mathlib.RingTheory.TensorProduct.Quotient`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, `Mathlib.RingTheory.MvPolynomial.Basic`,
and `Mathlib.RingTheory.Localization.Submodule`; the needed declarations are already
available through the retained imports.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The planned Artinianity of the source
quotient and the final prime-by-prime argument are unnecessary for Mathlib's criterion.
The DAG omitted the quotient/tensor equivalence used for flatness; added the existing
Mathlib leaf `lem-weil-pbc-tensor-quotient-base-change` to the proof dependencies.
The recorded local source file `literature/stacks-project/smoothing.tex` is absent on
this machine; read the proof directly at https://stacks.math.columbia.edu/tag/07FH.
The cases m=0 and n=1 require no extra assumptions or exceptional proof branches:
the same span and positive-power arguments handle them.

The required dry run with
`python3 /home/ubuntu/weil-launcher/deliver3.py B4
Sheaf.RingTheory.PopescuEtaleQuotientMap --no-push` succeeds with `OK`:
the commit compiles and passes maintainer preflight (apart from the second
reading, which is written by the second reader). Nothing was pushed.

## Second reading by B4

1. **Interface and accidental changes — pass.** I compared the delivered module
   with the repository version. The existing theorem signature and all existing
   declarations are byte for byte unchanged; only proof-only imports, a private
   helper, and the target proof were added. The DAG node changes only record the
   route and dependencies used by that proof.

2. **Proof validity — pass.** The module compiles with the mandated local compiler,
   contains no `sorry`, axiom, unsafe, opaque, extern, or implemented-by construct,
   and the target's axioms are exactly `propext`, `Classical.choice`, and
   `Quot.sound`. The helper `flat_quotient_map` is private and proved.

3. **Statements and nodes — pass.** No statement was split off or changed. The
   target remains the original theorem, and its DAG proof dependencies match the
   declarations and Mathlib results actually used. No duplicate library theorem or
   false intermediate statement was introduced.

4. **Pruning and route — pass.** The proof uses the shorter Mathlib route through
   quotient tensor base change, faithfully-flat contraction, Hopkins–Levitzki, and
   the flat formally-unramified étale criterion. The obsolete Artinian quotient
   dependency is removed from `proof_deps`; the unit's realized route is preserved.
   Imports removed by the first worker are genuinely unnecessary, while all added
   plain imports are proof-only.

5. **Source and edge cases — pass.** The construction is explicit and introduces
   no data chosen from an unproved existence theorem. The localization and quotient
   arguments cover `m = 0` and `n = 1`; the hypotheses are used at their stated
   strength. The source is recorded as Stacks Project Tag 07FH, and the report
   records the unavailable local source file.

I changed only this report section; no Lean code or DAG statements required repair.
