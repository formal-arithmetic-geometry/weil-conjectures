# Stage-1 report: lem-trf-strict-transform-different-centers

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-strict-transform-different-centers.json`: item, statement-only proof split, status `split`.
- `dag/nodes/sec-trace-formula/lem-trf-strict-transform-affine-torsion-comparison.json`: new statement node, status `unsplit`, Mathlib verdict no match.
- `citations.json`: verbatim statement excerpts for every proof-step citation.

## Attachments

None. I found no sorry-free declaration tagged `(blueprint: lem-trf-strict-transform-different-centers)` or stating Tag 080H clause (2) in `WeilConjectures/` of the slopmaster2 or upstream source trees.

## WANTED

None.

## What was wrong or incomplete

The imported item had an empty proof and did not expose the affine algebra lemma used by the source proof. I added that strictly smaller lemma as `lem-trf-strict-transform-affine-torsion-comparison`; it is statement-only because this is a one-level stage-1 split. I did not change the imported mathematical statement. The source's clause (1) is represented by the existing `lemma-nagata-blowup-invertible-factor` dependency and the item’s fixed isomorphism `varphi`.

## Not duplicates

- `lem-trf-strict-transform-affine-torsion-comparison` vs `lem-trf-strict-transform-different-centers`: the new node is only the affine ring/module torsion equality used in the proof; the item is the global sheaf strict-transform same-kernel assertion with blow-up and Cartier hypotheses.
- `lem-trf-strict-transform-affine-torsion-comparison` vs `def-nagata-strict-transform-chart-ring`: the existing node defines a strict-transform chart as a torsion quotient, while the new node proves equality of the two different torsion submodules for a Cartier factor.

## Review by Q27

I read the complete Stacks source at `literature/stacks-project/divisors.tex`, Tag 080H, including clause (1), the clause (2) hypothesis on sections supported over `f^{-1}D`, and the algebra paragraph reducing the assertion to equality of `a`-power and `xa`-power torsion. I also read the imported item and every node cited by its proof: `lemma-nagata-blowup-invertible-factor` supplies the fixed comparison of the two blow-ups; `def-trf-module-strict-transform` says each transform is the quotient of the pullback by sections vanishing off the preserved open; `def-pc-fibre-product` supplies the identified ambient fibre products; `def-nagata-blowup-chart-ring`, `prop-nagata-affine-blowup-chart-cover`, `def-nagata-strict-transform-basechange-chart-ring`, and `def-nagata-strict-transform-chart-ring` supply the standard affine charts, pullback tensor module, and torsion quotient. The new node's statement was checked directly against the algebra assertion in Tag 080H and against the definitions of `A[I/a]` and `Gamma_(a)`.

Step 1 uses exactly the existing blow-up-isomorphism, fibre-product, and strict-transform quotient statements to transport both quotient maps to one ambient pullback. Step 2 checks the hypotheses locally: `x` is a local nonzerodivisor generating the effective Cartier ideal, `a` is a generator of the finite-type centre on a standard chart, and the chart cover and chart-ring definitions give the two quotient kernels. Step 3 translates “no nonzero local sections supported on `f^{-1}D`” to `Gamma_(x)(M)=0` on the affine module and applies the new torsion-comparison statement; the cited quotient definition then identifies this equality with equality of kernels. Step 4 glues the local equalities over the standard chart cover and uses the fibre-product identification. The final step is the only elementary step: equality of quasi-coherent kernel subsheaves can be checked on a covering family.

I searched the whole DAG and blueprint for Tag 080H, strict-transform torsion, and the affine torsion wording before creating the new node. The required LeanFinder, Loogle, grep, and LeanSearch searches for both the item and the new node were run and their hits were read; they found only generic ideal/order/localization or torsion declarations and no statement of either node. I checked small cases of the new statement: if `I=(a)` then `A[I/a]=A` and both torsion submodules reduce to the expected equality; if `x` is a unit then `a` and `xa` generate the same powers; if `M=A` and `A` is a domain both torsion submodules are zero. No source or statement error was found, and no proof step relies on a fact absent from its cited node statement.
