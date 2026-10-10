1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-principal-open-dense-of-nonzerodivisor.json`: split statement, three proof steps.
- `dag/nodes/sec-picard-framework/lem-pc-dense-range-comap-minimal-primes.json`: statement-only Mathlib leaf; exact match `PrimeSpectrum.denseRange_comap_iff_minimalPrimes`.
- `dag/nodes/sec-picard-framework/lem-pc-minimal-prime-avoids-nonzerodivisor.json`: statement-only Mathlib leaf; exact match `Ideal.notMem_nonZeroDivisors_of_mem_mem_minimalPrimes`.

2. Attachments: none.

3. WANTED: `literature/stacks-project/divisors.tex`, Tag 07ZU, for `lem-pc-principal-open-dense-of-nonzerodivisor`; the Stacks source checkout is absent on this machine. I used the existing DAG source references and the pinned Mathlib declarations for the proof.

4. The imported item was unsplit and had no Lean declaration. The existing affine complement node cites this item, so citing that node would create a cycle. I retained the item statement and routed the proof through localization, dense range on minimal primes, and avoidance of nonzerodivisors by minimal primes. Both new nodes are strictly smaller statement-only Mathlib leaves and were checked against their source declarations.

## Review by F1

The local Stacks source file is absent, so I checked the target's Tag 07ZU citation against the already reviewed affine-complement node and used the pinned Mathlib declarations to supply the argument. The hypotheses are exactly that `A` is commutative and `a` is a non-zero-divisor. I read the existing localization leaf, whose statement explicitly identifies `Spec(A_f)` with `D(f)`, so step 1 uses its image/homeomorphism conclusion. For step 2 I read `PrimeSpectrum.denseRange_comap_iff_minimalPrimes` at Mathlib `Topology.lean` lines 948-958; the new leaf states its dense-range criterion in the same terms. For step 3 I read `Ideal.notMem_nonZeroDivisors_of_mem_mem_minimalPrimes` at Mathlib `MinimalPrime/Localization.lean` lines 97-101; the new leaf states precisely that a nonzerodivisor is outside every minimal prime. The localization leaf supplies the prime-correspondence consequence used after this exclusion. I tested the statement on `k[t]` with `a=t` (the usual dense complement of the origin), `a=1` (the whole spectrum), and the excluded zero-divisor case `k[x,y]/(xy)` with `a=x` (where density fails), confirming the nonzerodivisor hypothesis is necessary. I filled blueprint ancestry and citations with verbatim node statements. Preflight first rejected missing spectrum citations and Mathlib line fields; I added both and reran it successfully.

5. Unfinished: none.
