## What changed

Replaced the proof hole in `RingTheory.powerSeriesSubringFiniteBasis` by a complete
Lean reduction to the two steps of its explicit monomial argument. The coefficient
step gives a kJ-basis indexed by `J → Fin p`. The exponent-residue step works for
any finite coefficient-field basis and any positive integer p, without a p-basis
or characteristic assumption. The item combines these results, proves that the
three zero functions index the vector 1, and reindexes the finite product by `Fin d`.
The existing signature and all existing public imports are unchanged. The two new
proof dependencies and `Mathlib.Data.Fintype.EquivFin` are private imports.

All three modules compile without warnings using lcompile.py. The dry run also
runs the declaration axiom probe. No definition or existing statement was changed.

## Proved and sorry left

Closed: `RingTheory.powerSeriesSubringFiniteBasis`
(node `lem-weil-pbc-power-series-subring-finite-basis`), one of one original holes.

Added and still sorry:
- `RingTheory.pBasisComplementMonomialBasis`
  (`lem-weil-pbc-p-basis-complement-monomial-basis`).
- `RingTheory.powerSeriesResidueMonomialBasis`
  (`lem-weil-pbc-power-series-residue-monomial-basis`).

This is a decomposition, not a sorry-free proof. One hole was closed and two were
added, so net progress (closed minus added) is -1 and there is one additional hole. The item theorem still depends on
these two unproved results.

## No longer needed

None of the original modules or dependency nodes is pruned. The original imports
are needed by the unchanged statement. The original proof dependency definitions
of free modules, polynomials, and series remain statement dependencies or are used
by the two intermediate arguments. Removed unnecessary proposed imports of
`Mathlib.Data.Fintype.Pi` from both new modules. The generic residue theorem uses
`Mathlib.Algebra.Field.Subfield.Basic`, rather than IntermediateField.Basic.

## Where the brief, the DAG or earlier work was wrong

The two original non-elementary proof steps cite only definition nodes. They do
not supply intermediate Lean theorems implementing either basis construction.
This delivery gives those steps separate, strictly smaller statements and writes
the combination in Lean. It keeps the unit's route and changes no unit records.

The repository's local Stacks tex file is absent. Read the source directly at
https://stacks.math.columbia.edu/tag/07P5 and the p-basis background at
https://stacks.math.columbia.edu/tag/07P2. The explicit basis argument is the
parent node's expansion of the source's finiteness paragraph, not an assertion
that Stacks itself states an explicit finite basis containing 1.

LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable.
LeanFinder, Loogle and Mathlib grep searches were actually run; none gave a match.
The full blueprint searches for p-basis, 07P5 and monomial produced no duplicate.
The ancestor script returned None for this recently created item's ancestry; the
new nodes retain the ancestor of the parent PowerSeriesRingSubfields node,
`thm-weil-pbc-finite-etale-lifting`, and explain the intervening nodes.

## New nodes

`lem-weil-pbc-p-basis-complement-monomial-basis`:
`lean/Sheaf/RingTheory/PBasisComplementMonomialBasis.lean` states the bounded
J-monomial basis of k over kJ. Its proof in words identifies the complementary
monomial span with kJ, then groups coordinates and uses original p-basis
independence. The case J empty has a singleton basis containing 1. No series or
polynomial variables appear in this statement.

`lem-weil-pbc-power-series-residue-monomial-basis`:
`lean/Sheaf/RingTheory/PowerSeriesResidueMonomialBasis.lean` states the explicit
residue-monomial basis from any finite coefficient-field basis. Its proof in
words constructs the coefficient columns and checks finite polynomial support,
spanning, and independence coefficientwise. It includes p=1, n=0, and m=0.
It does not assert existence of a coefficient-field basis, and it does not assert
that any prescribed vector of that basis is 1. Those facts are combined in the
item's complete Lean proof.

Both new nodes include self-contained statements, verbatim Lean signatures,
actual search records, sources, proof steps, and the inherited chapter and unit.
No change record is needed because no existing interface changes.

## Second reading by H3

1. I compared the delivered item module with the repository version. The existing
   `powerSeriesSubringFiniteBasis` signature is byte-for-byte unchanged; only its
   proof and private imports were added. The two new declarations are separate
   strictly smaller statements, and their signatures match their DAG nodes.
2. I compiled all three modules with `lcompile.py --all`. They compile without
   errors or warnings. The only remaining `sorry`s are the two named split-off
   theorems listed above; no definition contains `sorry`, and no forbidden
   declaration (`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`) was
   introduced. The target's axiom probe has `sorryAx` only through those open
   dependencies, in addition to the permitted axioms.
3. I checked the two split-off statements against the edge cases described in
   their proofs: empty J, zero variables, zero-dimensional coefficient index,
   and p = 1 where applicable. They are true construction lemmas, strictly
   weaker than the parent target, and neither duplicates a declaration already
   present in the library.
4. The proof follows the DAG route: the complementary p-basis monomial basis is
   used first, then the residue-monomial lifting theorem, and finally finite
   reindexing with the all-zero vector. The unit route and its realized node are
   unchanged. The private imports are exactly the declarations used by the proof.
5. The DAG records for the item and both split-off nodes agree with the Lean
   declarations, including `proof`, `proof_deps`, `proof_origin`, source, and
   blueprint metadata. No existing target or definition was changed.

I changed only this report section; no proof or interface repair was needed.
