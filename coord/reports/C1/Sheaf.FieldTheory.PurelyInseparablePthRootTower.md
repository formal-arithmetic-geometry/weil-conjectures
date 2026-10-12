## What changed

Proved `IsPurelyInseparable.exists_pth_root_tower` in
`Sheaf.FieldTheory.PurelyInseparablePthRootTower`, preserving its complete signature,
universes, visibility, and all clauses. Added only private proved helpers:
`first_root`, `cons_range`, `tower_aux`, and `exists_pth_root_generators`.
The proof follows Stacks Tag 09HI, read on the official Stacks page:
https://stacks.math.columbia.edu/tag/09HI . The local literature source was absent.

The first helper uses the least exponent entering the base, Frobenius injectivity,
irreducibility of X^p-C b, and `IntermediateField.adjoin.finrank`. Strong induction on
`Module.finrank K E` for intermediate fields K keeps recursive base fields in a fixed
universe. Degree multiplicativity decreases the induction measure. The explicit
range equality for a prepended sequence and `adjoin_adjoin_left` concatenate towers.
The final field and generator are taken from the tower; their degree, strictness,
finiteness, and inseparability are proved. The quotient presentation follows from
`minpoly.equivAdjoin`, with the coefficient constructed as the subtype of beta^p.
No definition or data object was chosen from an unproved existence theorem.

Added proof-only imports `Mathlib.FieldTheory.KummerPolynomial` and
`Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed`. Updated the existing node's proof
and proof origin to describe the Lean implementation; its statement, dependencies,
and the blueprint unit route are unchanged.

## Proved and sorry left

Closed the sole original hole:
`IsPurelyInseparable.exists_pth_root_tower`
(node `lem-weil-pbc-purely-inseparable-pth-root-tower`).
One hole closed, zero holes added. No sorry remains in the delivered module and
no new module or intermediate unproved theorem is delivered. This is a full proof,
not a decomposition. All private helpers are proved from Mathlib.

The module compiles without warnings. `#print axioms` was checked on the completed
proof; only `propext`, `Classical.choice`, and `Quot.sound` occur.
The empty tower handles degree one, and the nontrivial branch proves n > 0 before
using n - 1. Primality supplies p > 1; no extra hypothesis is imposed.

## No longer needed

None of the original imports, nodes, or dependency modules is pruned. The original
six proof dependencies remain relevant: finite pure inseparability, algebraicity,
polynomials, the simple-extension power basis, X^p-C b irreducibility, and degree
multiplicativity. A trial explicit `Mathlib.Algebra.CharP.Reduced` import was removed
because the existing imports already expose Frobenius injectivity; it was not a
baseline proof dependency. The temporary generators module was folded into private
helpers and is not delivered.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The elementary concatenation step needs
care with scalar restriction in Lean: induction over all intermediate fields of the
fixed ambient extension avoids changing universes, and the prefix equality is stated
using the actual simple adjoin before restriction. The official Stacks Tag 09HI was
read because `literature/stacks-project/fields.tex` is not present on this machine.

Searches were run through msearch.py: LeanFinder for a finite purely inseparable
tower of pth roots, Loogle for `IsPurelyInseparable, Module.finrank`, and grep for
`exists.*pth.*tower|adjoin.*finrank|quotient.*minpoly`. They found single-element,
tower permanence, and degree ingredients, but no existing full tower theorem.
Local searches in both library roots likewise found no full tower proof.

## Second reading by C1

1. **Visible changes.** Compared the delivered module and node with the repository versions. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports, proofs, and the node's proof metadata changed.

2. **Proof and axioms.** Compiled the module and `scratch/Axioms.lean` with `lcompile.py`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. `#print axioms IsPurelyInseparable.exists_pth_root_tower` reports only `propext`, `Classical.choice`, and `Quot.sound`.

3. **Statements and split-offs.** No statements were split off and no new public declarations were added. The private helpers are proved, use no hollow data, and the edge cases (empty tower and prime degree greater than one) are handled explicitly. Searches found no duplicate library theorem.

4. **Pruning and route.** The proof uses the shortest available Mathlib route for irreducibility, minimal polynomials, finrank, and quotient equivalences, while preserving the unit's induction and concatenation route. Both added imports are proof-only and all original public imports remain needed; no proof-dependency node or module can be pruned.

5. **DAG agreement.** Updated node proof text and proof origin describe the actual Lean route; statement, statement dependencies, unit, and blueprint remain unchanged. The unit's realized route is preserved.

**Changes made by this second reading:** no mathematical or Lean repair was necessary; only this required review section was added to the report.
