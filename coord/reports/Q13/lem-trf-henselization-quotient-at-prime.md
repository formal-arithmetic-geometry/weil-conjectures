1. Files written:
   - `dag/nodes/sec-trace-formula/lem-trf-henselization-quasi-finite-ring.json` — new statement-only predecessor for the ordinary quasi-finite henselization comparison; Mathlib searches found no match.
   - `dag/nodes/sec-trace-formula/lem-trf-henselization-quotient-at-prime.json` — repaired two-step split, with Step 1 using the predecessor and the finite-map quasi-finiteness node.
   - `citations.json` — verbatim citations for both statements used by Step 1.
2. Attachments: none.
3. WANTED: none; `literature/stacks-project/algebra.tex` contains Tags 05WR and 05WQ.
4. The returned split was circular because Step 1 invoked Tag 05WQ (the item itself) while citing only the henselization definition. I repaired it by adding `lem-trf-henselization-quasi-finite-ring`, the preceding ordinary comparison statement of Tag 05WR, and by applying that node to the finite quotient map $R\to R/I$ at the maximal primes. The existing finite-ring-map node supplies the required finite-type and quasi-finite hypotheses. The tensor quotient and localization at the maximal prime are then the elementary specialization yielding $R^h/IR^h$. The second step remains the elementary verification of surjectivity, locality, and factorization of the structure map.

## Not duplicates

`lem-trf-henselization-quasi-finite-ring` vs `lem-trf-strict-henselization-quasi-finite-ring`: the new node concerns ordinary henselizations and gives finite-locality plus the tensor-localization description; the existing node concerns strict henselizations, compatible geometric points, residue-field pure inseparability, and a different tensor localization.

`lem-trf-henselization-quasi-finite-ring` vs `lem-trf-closed-immersion-strict-localization-cartesian`: the new node is a general ring-level ordinary-henselization comparison for any quasi-finite map at a prime; the existing node is a scheme-level strict-henselization fibre-product theorem specialized to a closed immersion, retaining nilpotents.

`lem-trf-henselization-quasi-finite-ring` vs `lem-trf-finite-base-strict-localization`: the new node describes ordinary henselizations for one quasi-finite ring map and a tensor localization; the existing node describes a coproduct decomposition and arbitrary base-change cartesian square for strict localizations under a finite scheme morphism.

`lem-trf-henselization-quasi-finite-ring` vs `lem-trf-ind-etale-strict-local-invariance`: the new node handles ordinary henselizations under quasi-finite maps and proves finiteness; the existing node states invariance of strict localizations under ind-etale scheme maps and base change.

`lem-trf-henselization-quotient-at-prime` vs `lem-trf-henselizations-common-normal-cover`: the common-normal-cover node uses quotient compatibility as one step to construct surjections between henselizations at two primes; this item states the underlying local quotient theorem itself, with arbitrary local $R$ and ideal $I$.

## Review by Q13

I read the item source in `literature/stacks-project/algebra.tex`, Tag 05WQ, and the full preceding Tag 05WR proof (the ordinary quasi-finite henselization lemma). I also read the statements of `def-weil-pbc-henselization-at-prime` and `lem-weil-pbc-finite-ring-map-quasi-finite`. Step 1 now cites the new predecessor for exactly its finite-local tensor-localization conclusion and cites the finite-map node for the fact that the quotient map is finite type and quasi-finite at the maximal quotient prime. I checked the hypotheses: $R/I$ is local with maximal ideal $\mathfrak m/I$, the localizations at $\mathfrak m$ and $\mathfrak m/I$ are the rings themselves, and $R^h\otimes_R(R/I)=R^h/IR^h$; the corresponding prime is maximal, so its localization is the quotient ring. Step 2 uses only the ideal-quotient definition and the local structure map: the quotient is surjective, $IR^h$ lies in the maximal ideal, and the composite factors through $R/I$. I checked edge cases $I=0$ and $I=\mathfrak m$. I reran the Mathlib searches for the new predecessor in LeanFinder, Loogle, grep, and LeanSearch; they returned only general quasi-finite or henselian declarations and no ordinary henselization comparison. The prior circular citation and the missing predecessor citation are corrected, and `citations.json` now quotes each cited statement verbatim.
