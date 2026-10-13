## What changed
Added a real Lean reduction of `Algebra.relativeGlobalCompleteIntersection_principalLocalization` to two strictly smaller named statements: the algebra equivalence and preservation of the relative global complete intersection condition. The main module imports these two proof-only modules and combines them by `exact ⟨..., ...⟩`.

## Proved and sorry left
The target declaration `Algebra.relativeGlobalCompleteIntersection_principalLocalization` is proved. Sorry remains in `Algebra.principalLocalization_algEquiv` (node `new-principal-localization-alg-equiv`) and `Algebra.principalLocalization_ci` (node `new-principal-localization-ci`); both are strictly smaller components of the argument.

## No longer needed
No imports were removed. The original dimension and fibre proof dependencies are no longer needed by the main proof because the two decomposition statements abstract those components; they remain available for proving the new nodes.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan expands substantial quotient/localization and fibre-dimension arguments that cannot be completed within this item. The executable reduction exposes these as two independent lower statements while preserving the exact target signature.

## Earlier second reading (a previous round; superseded)
Pending independent reading of the two new nodes and their exact strength.

## New nodes
`new-principal-localization-alg-equiv` and `new-principal-localization-ci` are stated in separate modules under `lean/Sheaf/RingTheory/`; each is a strict component of the target proof and has a documented source in Stacks Tag 00SS, part (2).

## Second reading by H4
1. I compared the delivered target module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only proof
   imports and the target proof body differ. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. There are no
   errors, forbidden declarations, or sorries in definitions. The target is proved;
   the only remaining `sorry`s are the two named split theorems
   `Algebra.principalLocalization_algEquiv` and `Algebra.principalLocalization_ci`.
   Verdict: pass, with those documented holes.
3. I checked both split statements against the target conjuncts. The algebra
   equivalence statement is exactly the existential second conjunct, and the CI
   statement is exactly the first conjunct, so each is strictly smaller and neither
   weakens the target. Their docstrings now give the construction and fibre-dimension
   proof route, with Stacks Tag 00SS as source. Verdict: pass.
4. The target proof uses only the two proof-only imports and the two split theorems;
   the former dimension and fibre imports are no longer needed by this module. The
   unit route is retained: the target is still obtained by composing its two planned
   components. Verdict: pass.
5. The DAG nodes now state the actual algebra equivalence and CI propositions, and
   their Lean records point to the matching declarations and modules. Verdict: pass.

I changed the target imports and proof as described above, expanded the two split
theorem docstrings, and made the two node statements self-contained. No target
statement or definition was changed.
