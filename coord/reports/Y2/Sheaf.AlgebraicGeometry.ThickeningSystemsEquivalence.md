## What changed

Replaced the one hole in `Sheaf.AlgebraicGeometry.ThickeningSystemsEquivalence` by a
complete Lean assembly of an explicitly constructed functor, full faithfulness, an
adic object assertion, and object lifting. The original theorem signature and all
original public imports are unchanged. The construction works for any closed tower
whose projections have the prescribed kernels, rather than using the affine-base
presentation to construct the transition maps.

Added `Sheaf.AlgebraicGeometry.ThickeningSystemPushforward`. It explicitly constructs
the transition using the supplied adjunction, pushforward composition, and `hi`, then
uses Mathlib's `Functor.ofOpSequence` and `NatTrans.ofOpSequence`. Functor laws,
evaluation comparisons, the adjacent transition formula, detection of compatibility,
and full faithfulness are proved. Fullness uniquely lifts each component through
closed pushforward and proves comparison compatibility by cancelling the composition
isomorphism and applying injectivity of the adjunction hom equivalence. Faithfulness
is equality of component families. No definition chooses module data from a holed
existence theorem, and no public definition uses a private helper.

Added two modules with one remaining theorem each:
`ThickeningSystemPushforwardAdic` states the three object conditions for this explicit
system, and `ThickeningSystemPushforwardLifting` states only existence of a preimage
for an individual adic object. The parent restricts the actual functor with
`ObjectProperty.lift`, obtains essential surjectivity with `ObjectProperty.isoMk`,
uses Mathlib's equivalence criterion, and verifies the displayed beta equation with
the proved transition formula. Updated the parent DAG route and added three nodes.

Validation: the four delivered modules compile in dependency order without warnings
through `lcompile.py`. A sandbox-only geometry check proves from Mathlib and the source library that
`i ≫ j = k` with closed `j` and `k` gives a closed `i` with kernel `k.ker.comap j`.
This validates removing the quotient-base-change detour. The dry run performs the
additional declaration, signature, sorry, axiom and delivery checks.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.thickeningSystems_pushforward_equivalence`
(node `lem-weil-pbc-thickening-systems-pushforward-equivalence`) by decomposition.
Its proof is complete Lean, but this is not a claim that the geometric equivalence
has been fully proved: two strictly smaller object assertions remain.

New proved declarations in `ThickeningSystemPushforward` include
`AlgebraicGeometry.thickeningPushforwardTransition_naturality`,
`AlgebraicGeometry.thickeningSystemPushforward_transition`,
`AlgebraicGeometry.thickeningPushforward_compatibility`, and
`AlgebraicGeometry.thickeningSystemPushforward_fullyFaithful`. All newly defined data
are explicit and sorry-free. Their previously existing library dependencies retain
their own proof obligations; those files are not modified by this delivery.

Exactly two new holes, each a public theorem with its full proof in words:

- `AlgebraicGeometry.thickeningSystemPushforward_isAdic`, node
  `lem-weil-pbc-thickening-system-pushforward-adic`, in
  `Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardAdic`.
- `AlgebraicGeometry.thickeningSystemPushforward_lifting`, node
  `lem-weil-pbc-thickening-system-pushforward-lifting`, in
  `Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardLifting`.

The original module has no remaining sorry. Holes closed: 1. Holes added: 2.
This is a decomposition with ledger net -1, not a net closure improvement.
The new object assertions are independent: adic preservation does not assert
lifting, and lifting does not assert functoriality, full faithfulness or equivalence.

Edge cases checked mathematically: level zero corresponds to the first power J;
J = 0 gives isomorphic projections and invertible adjacent transitions; J = 1 gives
empty closed sources and zero adic terms; the empty scheme causes no exception.
The adjunctions may be arbitrary: their comparison with the chosen adjunction changes
the quotient identification by an isomorphism and preserves the quotient condition.
The generic geometry check confirms that no second pullback projection identity is
needed for these two assertions.

## No longer needed

Removed these six direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`.
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful`.
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers`.
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`.
- `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`.

The first four and Noetherian module are retained where needed by the new proof or
by the stated proofs of the remaining geometric steps; they are relocated dependencies,
not claims of global pruning. `QuotientBaseChangeIdeal` is not used anywhere in this
new route. Its node `lem-weil-pbc-quotient-base-change-closed-immersion-ideal` is pruned
from this equivalence argument. No claim is made that other target paths cease to
reach it. All original statement imports remain.

The parent no longer directly depends on
`def-pc-module-pullback`, `lem-weil-pbc-closed-immersion-coherent-equivalence`,
`lem-weil-pbc-closed-immersion-pushforward-fully-faithful`,
`lem-weil-pbc-closed-immersion-pushforward-ideal-powers`,
`lem-weil-pbc-closed-immersion-unit-quotient`, or `pqf-lem-locnoeth-lft`;
these appear in the new subarguments as appropriate. The parent keeps
`def-weil-pbc-coherent-formal-module` and depends on the three new nodes.
The second projection hypothesis `hi₂` and pushforward adjunctions `aj` are not
mathematically needed by this construction but remain in the unchanged signature.
No blueprint unit statement or realized proof step was removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The original planned use of `quotientBaseChange_nestedIdeals` is unnecessary under
`hgeom`. Mathlib's closed-composite formula and the source library's ideal kernel formulas already give the closed
transition and its kernel. This is a shorter route below the unit level, not a dispute
with the original statement.

The local repository does not contain the Stacks source at its recorded relative
path. Read the read-only source at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/coherent.tex`, including
`lemma-i-star-equivalence` and `remark-reformulate-existence-theorem`.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, direct Mathlib
source search, local library search and full blueprint search were used. Mathlib's
sequence constructors supply the categorical construction, but no earlier standalone
geometric adic verification or lifting theorem was found.

## New nodes

`lem-weil-pbc-thickening-system-pushforward-functor` records the explicit sequence
construction, natural evaluation and transition identifications, and the proved
full-faithfulness argument. Its module has no sorry.

`lem-weil-pbc-thickening-system-pushforward-adic` records the object assertion that the
explicit pushed sequence is coherent, annihilated by the prescribed powers, and has
quotient transitions. It contains one sorry with the source and complete proof in words.

`lem-weil-pbc-thickening-system-pushforward-lifting` records existence of an upstairs
coherent thickening system for a given adic object and its inverse-system isomorphism.
It contains one sorry with the source and complete proof in words. The choices are
inside a proposition asserting existence; no definition selects arbitrary module data
from this unproved theorem.

No statement, definition or existing interface was changed; no change record or
forced adaptation is needed.

## Second reading by Y2

1. **Visible declarations.** Compared the delivered parent module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof text and proof-only imports changed. The three added modules and DAG nodes are the declared split-off additions.

2. **Compilation and axioms.** Compiled all four modules with `lcompile.py --all`; each compiled without errors or warnings. The target and helper declarations use only the permitted foundational axioms together with `sorryAx` inherited from the two explicitly split-off theorems and their open dependencies. No forbidden `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition occurs.

3. **Statements and split holes.** Read the statements of the functor, adic assertion, and lifting assertion against their node records and source references. The functor and full-faithfulness declarations are proved; the adic and lifting declarations are strictly smaller object assertions, each has a named node and a complete proof sketch in its docstring. No statement duplicates an existing library declaration or weakens the parent target.

4. **Pruning and imports.** Checked each import against its use. The parent’s removed imports are no longer needed by its explicit categorical proof; proof-only imports in the new modules are plain imports. The parent DAG proof dependencies and the three new node records follow the declarations used by the Lean proof, and the quotient-base-change node is pruned from this route.

5. **Route and edge cases.** The unit route remains realized through the explicit pushforward construction, adic object assertion, and lifting assertion. Checked the edge cases recorded above (zero and unit ideals, level zero, and empty schemes); the statements remain meaningful and unchanged.

Changed only the report by adding this second-reading record. No Lean statement or definition required repair.
