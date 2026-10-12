## What changed

Proved `AdjoinRoot.radicial_prime_unique_degree_p` in the sandbox module. Added the proof-only import `Mathlib.RingTheory.Spectrum.Prime.Homeomorph`. The proof uses the monic AdjoinRoot finite module API, finite-module integrality, explicit Frobenius polynomial induction, and `PrimeSpectrum.isHomeomorph_comap`.

## Proved and sorry left

The declaration `AdjoinRoot.radicial_prime_unique_degree_p` is fully proved. Closed one hole, `AdjoinRoot.radicial_prime_unique_degree_p`; added zero holes. No `sorry` remains. This is a complete proof, not a decomposition.

## No longer needed

The planned Sheaf dependencies `lem-weil-pbc-monic-quotient-free`, `lem-weil-pbc-finite-algebra-is-integral`, `def-weil-pbc-integral-closure`, and `lem-weil-pbc-integral-injective-lying-over` are not imported: their roles are discharged directly by Mathlib APIs. The fifth old proof dependency, `def-weil-polynomial-ring`, is also no longer a proof dependency: the polynomial construction and induction are Mathlib APIs. All five old proof dependencies are removed from this node's `proof_deps`; the two `stmt_deps` are preserved. No import from the repository version was removed, so no newly unreachable module is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was valid but unnecessarily split the finite-module, integrality, and lying-over steps; Mathlib already provides these. The statement itself is unchanged.

## Second reading by R1

1. Compared the sole delivered module with the repository using `diff`, and checked the existing theorem signature byte for byte. Only its proof and one plain, proof-only Mathlib import differ. No definition, statement, visibility, or target changed; no change record is required. Verdict: pass.
2. Read the polynomial induction, characteristic-p instances, degree argument, and the conversion between prime-spectrum points and ideals. Compiled the repaired file without errors or warnings. A scratch copy with `#print axioms AdjoinRoot.radicial_prime_unique_degree_p` reports only `propext`, `Classical.choice`, and `Quot.sound`. No sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition is present. Verdict: pass.
3. No statement was split off and no new declaration or node was introduced. The Frobenius witnesses are explicit, not chosen from an unproved existence result. The monomial argument covers degree zero, zero coefficients, and p = 2; p = 0 and p = 1 are excluded by primality. If f is already a p-th power, the quotient-domain hypothesis can fail, which does not invalidate the theorem. Verdict: pass.
4. Read the Mathlib definitions and proof of `PrimeSpectrum.isHomeomorph_comap`, and the monic finite-module and injectivity APIs in AdjoinRoot; searched the library for this quotient and theorem. The existing proof already uses the short Mathlib route for integrality and unique primes and leaves only the needed elementary polynomial induction. No Sheaf proof dependency is used. The existing public imports supply the statement's AdjoinRoot and IsIntegral vocabulary, and the added Homeomorph import is private to the proof. Checked `dag/units/sk-thm-p1.json`: neither the item nor any pruned dependency realizes a unit statement or step, so the shortening is below the unit level. The complete old proof-dependency list is accounted for above; the unit route is kept. Verdict: pass.
5. The first worker supplied no node update. Added the existing item's node to the sandbox with only `proof`, `proof_deps`, and `proof_origin` changed: its three steps now describe the finite monic quotient, explicit Frobenius induction, and Mathlib spectrum homeomorphism, with no project-node proof dependencies. Statement dependencies and all other fields are unchanged. No new-node fields are needed. Verdict: pass after repair.

Changes made in this second reading: replaced three `letI` declarations by `let`, removed the three unused simp arguments `map_natCast`, `map_C`, and `map_X`, supplied the missing proof-route node update, and completed the report's fifth pruned dependency and hole accounting. The mathematical argument was retained.
