## What changed

Proved `Algebra.IsQuasiFiniteAtPrime.of_restrictScalars` in
`Sheaf.RingTheory.QuasiFiniteAtPrimePermanence`, keeping its complete signature and visibility.
The only import remains `public import Sheaf.RingTheory.QuasiFiniteAtPrime`, required by
its statement. Updated the declaration docstring and the node's proof, proof_deps and
proof_origin to match the compiled proof.

The proof uses the fibre homeomorphism already available in Mathlib to view both fibres
as subspaces of `PrimeSpectrum C`. The scalar-tower equation constructs the continuous
inclusion of the B-fibre into the A-fibre. Its inverse image of the open singleton at r
is the singleton at r; the B-fibre homeomorphism gives the conclusion. Finite type over B
comes from `Algebra.FiniteType.of_restrictScalars_finiteType`.

Source checked: [Stacks 0C6H](https://stacks.math.columbia.edu/tag/0C6H), whose proof uses
containment of the sets of primes in the two fibres, and
[Stacks 00E6](https://stacks.math.columbia.edu/tag/00E6), the fibre homeomorphism.
The local literature/stacks-project/algebra.tex is absent on this machine, so the
corresponding tag pages were read. Searches used leanfinder, loogle, launcher grep and rg
across Mathlib, WeilConjectures and Sheaf. The proof uses the existing homeomorphism,
without a bridge to Mathlib's different `QuasiFiniteAt` predicate.

## Proved and sorry left

Closed the sole original hole: `Algebra.IsQuasiFiniteAtPrime.of_restrictScalars`
(node `lem-weil-pbc-quasi-finite-at-prime-permanence`). One of one sorries proved;
zero holes added, zero split off, no sorries left in this delivery. This is a complete
proof from Mathlib and the existing definition, not a decomposition through unproved lemmas.
Local compilation passed with no warnings.

## No longer needed

No imports removed and no modules removed from this module's import closure.
Removed the direct proof dependency `def-weil-pbc-localization-at-prime`: the explicit
localization/residue-field construction and comparison homomorphism of fibre rings
are unnecessary. The fibre construction itself remains implicit in the existing
quasi-finiteness definition and Mathlib's homeomorphism; no claim is made that the
localization node is globally unreachable.

Kept `def-weil-pbc-finite-type-algebra`, `lem-weil-pbc-fibre-ring-primes-bijection`
(via its topological Mathlib realization), `def-weil-affine-spectrum`, and
`def-weil-pbc-ring-map-quasi-finite-at-prime`. No unit statement or realized proof step
is bypassed: this item and its pruned direct dependency are below the unit level.

## Where the brief, the DAG or earlier work was wrong

The original DAG route was valid but needlessly constructed a fibre-ring comparison
homomorphism. Mathlib already supplies the homeomorphisms needed to formalize the
source's subset argument directly. No statement or definition correction was needed.

## Second reading by J2

1. **Statements and visibility.** Compared the delivered module with the repository version. The theorem signature and visibility are byte for byte unchanged; only its docstring and proof body differ. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it passes without warnings or `sorry`. The proof uses Mathlib's fibre homeomorphisms and scalar-tower identity, and introduces no axioms, unsafe declarations, or hollow definitions. Verdict: pass.
3. **Split-off statements.** No new statements or nodes were added. The sole target theorem is proved directly, and searches recorded in the node found no stronger existing pointwise theorem applicable to this definition. Verdict: pass.
4. **Pruning and route.** The proof avoids the unnecessary fibre-ring comparison construction while retaining the unit's fibre-isolation route. The direct localization node is no longer a proof dependency; imports remain minimal because the needed Mathlib declarations are re-exported by `QuasiFiniteAtPrime`. Verdict: pass.
5. **DAG agreement.** The node's proof, dependencies, and origin describe the compiled homeomorphism/subspace proof and the unchanged target statement. Verdict: pass.

Changed during second reading: added this review section only; no Lean or DAG repairs were needed.
