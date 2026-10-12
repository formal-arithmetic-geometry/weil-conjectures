## What changed

Proved `PrimeSpectrum.exists_disjoint_basicConstructibleSetData_diff` by induction on the number of defining equations of the second basic set. Added a private membership lemma by unfolding `BasicConstructibleSetData.toSet`. The proof uses only the existing Mathlib import; no proof imports were added.

## Proved and sorry left

The target theorem `PrimeSpectrum.exists_disjoint_basicConstructibleSetData_diff` is proved. No `sorry` remains in the delivered module, and no new holes were added.

## No longer needed

No imports or DAG nodes were removed. The proof does not require any additional Sheaf modules.

## Where the brief, the DAG or earlier work was wrong

The planned four set-theoretic steps are correct, but the direct least-index construction is cumbersome in Lean. A finite induction on the second tuple gives the same pieces incrementally and is the route implemented here.

## Second reading by K2

1. Compared the sole delivered Lean module against the repository with `diff` and
   checked the complete existing theorem signature byte for byte. It is unchanged:
   arbitrary `A : Type u` with `CommRing A`, arbitrary `f,h,r,s,g,k`, and both the
   pairwise-disjointness clause and exact set-difference union equality are kept.
   There are no definition changes or change records. The only added declaration
   is the proved private membership helper, which exposes no new public API.
   Verdict: pass.

2. Compiled the complete module locally using `lcompile.py`: no errors or warnings.
   Compiled a scratch copy with `#print axioms` for both declarations. The private
   `PrimeSpectrum.mem_basic` uses only `propext` and `Quot.sound`; the existing
   `PrimeSpectrum.exists_disjoint_basicConstructibleSetData_diff` uses only
   `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or forbidden declaration
   mechanism remains, and no data is chosen from an unproved existence theorem.
   Closed holes: `PrimeSpectrum.exists_disjoint_basicConstructibleSetData_diff` (1).
   Added holes: none (0). Verdict: pass, a proof rather than a decomposition.

3. No statements were split off. Checked the helper directly against Mathlib's
   `BasicConstructibleSetData.toSet` and `mem_zeroLocus`: all equation coordinates
   belong to the prime ideal and the distinguished coordinate does not. Checked
   the empty tuple cases `r=0` and `s=0`, the zero ring (no prime points), `f=0`
   (empty B), `h=0` (empty C), and zero/unit final equations. Empty basic pieces
   remain valid members of a pairwise-disjoint family. The base case is exactly
   `D(f) ∩ V(g,h)`; if the final equation is zero, the added piece is empty; if it
   is a unit, the added piece covers `B ∩ C_prefix`. Verdict: pass.

4. Re-read Mathlib's `ConstructibleSet.lean`, especially `toSet` and
   `exists_constructibleSetData_iff`, and searched the repository and upstream
   with `rg` for basic-set difference and disjointness. Ran LeanFinder with
   “finite mutually disjoint decomposition of difference of principal locally
   closed subsets of prime spectrum”; results concern clopen/basic-open sets,
   not this disjoint difference. The general constructibility representation
   does not supply disjointness. The existing direct induction is appropriate.
   The sole public Mathlib import is required by the theorem signature; there
   are no proof-only public imports or unused imports. Old `proof_deps` contains
   only `def-weil-affine-spectrum`, which is still used through Mathlib's prime
   spectrum definitions. No nodes/modules are newly unneeded. Read
   `dag/units/sk-thm-p1.json`: this item is not a realized unit statement or step;
   the induction changes only its elementary set calculation and preserves
   every unit route. Verdict: pass.

5. Read the item's node and `def-weil-affine-spectrum`. The node's unchanged
   statement matches the Lean theorem in every hypothesis and conclusion.
   Read the source pages [Stacks 03S0](https://stacks.math.columbia.edu/tag/03S0)
   (common refinement in the proof) and
   [Stacks 0G1P](https://stacks.math.columbia.edu/tag/0G1P)
   (basic sets `D(f) ∩ V(g)`). The source does not give this induction: it is
   correctly recorded as an elementary argument by the agent. The Lean proof
   uses only the definitions, finite indexing, elementary set logic, and prime
   ideal primality. Its successor piece is
   `E = B ∩ C_prefix ∩ D(k_last)`; the old pieces cover `B \\ C_prefix`.
   Consequently E is disjoint from every old piece, and splitting on membership
   in `C_prefix` proves the union equality. `proof_deps` remains exactly the
   union of the steps' uses. Only `proof` and `proof_origin` change in the node;
   there are no new nodes to check. Verdict: pass.

Changes made during the second reading: restored the original theorem docstring
(the first worker had appended an explanation); preserved the correct Lean proof;
restored the original source citations on the DAG proof steps and clarified the
successor construction, disjointness, and pointwise union argument. Added this
review and the explicit closed/added-hole accounting. No statements, definitions,
imports, or unit records were changed.
