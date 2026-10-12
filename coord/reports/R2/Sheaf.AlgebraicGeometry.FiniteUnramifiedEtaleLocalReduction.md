## What changed

Proved both declarations in `Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocalReduction`,
without changing either signature or any public import. Added the proof-only import
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` for finite-fibre enumeration.

`finite_decomposition_input` enumerates the actual finite fibre and applies the existing
unramified-local decomposition theorem. `finite_coproduct_of_unramified_decomposition`
applies that same theorem to a fresh exhaustive enumeration, removes the closed image
of the remainder, pulls back all pieces, proves their closed immersion properties by
pasting pullback squares, and uses Mathlib's disjoint-open-cover coproduct criterion.
`ULift` puts the finite index family in the required universe. The two node copies now
record these proofs and their dependencies.

Source read: Stacks Project `etale.tex`, Lemma 04HJ
(`lemma-finite-unramified-etale-local`) and its proof, using the local copy at
`/home/ubuntu/c1-stacks-review/etale.tex`. This is the existing blueprint route; none of
the unit's realized statements or steps is bypassed.

Searches: Lean Finder for finite unramified morphisms as etale-local disjoint unions of
closed immersions; Loogle for the finite-fibre lemma; msearch grep and direct rg over
Mathlib, Sheaf, and WeilConjectures. No direct theorem for the whole conclusion was found.
Mathlib supplies fibre finiteness, formal-unramified restriction, closed-map/base-change
properties, and `nonempty_isColimit_cofanMk_of`.

## Proved and sorry left

Proved `AlgebraicGeometry.finite_decomposition_input`
(node `lem-weil-pbc-finite-unramified-etale-local-input`).
Proved `AlgebraicGeometry.finite_coproduct_of_unramified_decomposition`
(node `lem-weil-pbc-finite-unramified-etale-local-reduction`).

No sorry remains in the delivered module; no new theorem, module, or sorry was added.
Both proofs use the existing unfinished declaration
`AlgebraicGeometry.exists_etale_closed_immersion_decomposition_of_unramified_at_points`
(node `lem-weil-pbc-unramified-etale-local-decomposition`), which remains the next
geometric proof obligation. This delivery does not claim that dependency is sorry-free.

The argument handles an empty fibre and empty family: Fin enumeration and sigma indexing
permit zero, and Mathlib's coproduct criterion permits an empty covering of the empty
pullback. No residue-field identification or nonempty-fibre assumption is introduced.

## No longer needed

No original import or dependency node was removed. The existing decomposition theorem
remains needed. Redundant trial imports of
`Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, and `Mathlib.AlgebraicGeometry.Limits`
were removed: their required declarations are already available through the retained
imports. No additional Sheaf shrinking, open-base-change, or coproduct bookkeeping
lemmas are required, and no new nodes were split off.

## Where the brief, the DAG or earlier work was wrong

The supplied decomposition input does not require its finite list `pts` to exhaust the
fibre. Consequently the proposed step of removing that input's remainder is unjustified:
for the empty list, a remainder equal to the entire pullback is permitted. The second
statement itself is true because finite unramifiedness already implies its conclusion.
Its proof therefore rebuilds the decomposition using the whole fibre, verifies
exhaustivity, and uses the final implication in the existing decomposition theorem.
The original `hpts` and `h` assumptions and all signatures are preserved; explicit
anonymous local facts acknowledge these unused interface assumptions to avoid warnings.

The original node proofs were generic one-step descriptions. They have been replaced by
steps identifying the actual finite enumeration, shrinking, pullback pasting, and
coproduct construction. No statement or definition correction was needed.

## Second reading by R2

1. **Statements unchanged.** Compared the delivered module with the repository version; both declaration signatures are byte-for-byte unchanged. Verdict: pass.
2. **Proof validity.** Compiled the module with `lcompile.py`; no errors, no new `sorry`, forbidden declarations, or hollow definitions. The only `sorryAx` in axiom output comes from the imported decomposition theorem explicitly listed in the report. Verdict: pass.
3. **Split statements.** No statements were split off and no new nodes were added. The two existing node statements remain true and exactly as strong as their Lean declarations. Verdict: pass.
4. **Pruning and route.** The proof uses the existing decomposition route, re-enumerates the complete finite fibre, and retains the unit's realized decomposition step. The proof-only QuasiFinite import is necessary; no prior import or proof dependency was removed. Verdict: pass.
5. **DAG agreement.** Updated node proof steps, origins, and proof dependencies match the delivered Lean proofs; signatures and unit route remain unchanged. Verdict: pass.

I changed only this report section after the first reading; no Lean declarations, statements, definitions, or DAG node statements were changed.
