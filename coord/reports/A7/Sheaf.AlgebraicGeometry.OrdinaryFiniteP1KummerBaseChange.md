## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerBaseChange` with a complete proof
from existing normalized Chern naturality, tensor evaluation, and adjunction-mate
identities. The item's public statement, public import and existing docstrings
are unchanged. No other existing module is changed.

`ordinaryFiniteClass_bijective_arbitraryBase` realizes the specified Kummer class
on the new base. Its specification feeds `ordinaryFiniteP1_chern_map_baseChange`.
The new proved `ordinaryFiniteP1_evaluationRecipe_baseChange` combines that square
with signed-twist composition, shifted degree-zero comparisons, preservation of
tensor evaluation, and inverse-right-unit naturality. The item's private generic
adjunct-square calculation transposes this equality. The constant component uses
the existing native adjunct square on identity maps.

Two proved helper modules keep concrete normalization within the per-file limit:
`OrdinaryFiniteSingleUnitNaturality` and `OrdinaryFiniteP1EvaluationRecipeBaseChange`.
The latter contains the private generic pasting calculations and signed-twist
square. The former specializes the existing inverse-right-unit natural
transformation to the exact constant objects used here. Both have full proofs.

The item adds proof imports of `FiniteP1ChernAdjunctMate` (including its proved
private mate and native-unit helpers), `FiniteP1ChernMapBaseChange`,
`OrdinaryFiniteClassArbitraryBase`, `FiniteTwistShiftedFactorComparisons`
(its canonical positive transport), and `OrdinaryFiniteP1EvaluationRecipeBaseChange`.
The evaluation helper imports `FiniteP1TwistedUnitBaseChange`,
`FiniteTwistDerivedEvaluationPullback`, `FiniteTwistShiftedFactorComparisons`,
`OrdinaryFiniteSingleUnitNaturality`, `LeftDerivedUpperStarSingle`, and
`LowerShriekBaseChangeShift`. The unit-naturality helper imports
`OrdinaryFiniteDerivedRightUnitPullback` and `ProjectionFormula.Unit` for their
existing constructions. All fully qualified paths are in the Lean headers.
The corresponding DAG proof dependencies describe this route.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.ordinaryFiniteP1_components_baseChange`
(node `lem-asd-ordinary-finite-p1-kummer-base-change`), the item's one original hole.
Added holes: zero. Remaining holes in all delivered Lean: zero.

The two new helper theorems are proved:
`AlgebraicGeometry.Etale.ordinaryFiniteSingleUnit_naturality` and
`AlgebraicGeometry.Etale.ordinaryFiniteP1_evaluationRecipe_baseChange`.
No unfinished statements were split off.

Validation: `lcompile.py --all` accepted all three modules in import order,
with no proof errors or code warnings. Temporary profiler-option warnings were
removed from the final sources. `deliver3.py` performs the final compile and
preflight for the packet.

## No longer needed

No original import was removed and no existing module is withdrawn.
The proof no longer directly needs `lem-asd-ordinary-supported-kummer`
(`Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`): the existing arbitrary-base
Chern-map naturality and class comparison supply the Chern square and specified
class. The separate hyperplane Cartier construction in the old proof plan is
therefore unnecessary here. This does not request removal of the supported
theorem or its module.

The separate `lem-amb-mate-unit-counit` dependency is unnecessary here:
`adjunct_mate` derives the required transposition directly from naturality and
`unit_mateEquiv`. The exchange definition remains needed. Signed-twist and
evaluation dependencies now occur in the proved evaluation helper rather than
directly in the item; those dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The old DAG plan did not mention the now-proved
`ordinaryFiniteClass_bijective_arbitraryBase` or
`ordinaryFiniteP1_chern_map_baseChange`; these remove the need to reconstruct the
infinity divisor here. The statement and its edge cases are unchanged. The unit's
`realized` lists are empty, so no realized unit step is bypassed. The proof uses
neither exchange invertibility nor Noetherianity, nonzero coefficients, flatness
over Z/N, or nonempty bases.

The original direct concrete proof normalized large derived constructions many
times. After replacing these calculations with generic pasting lemmas, cached
instances and existing normalized transport, a complete error-free proof still
exceeded the per-file limit (86 seconds). The two self-contained proved parts
were therefore extracted. No shared definition, interface or timeout was changed.

LeanFinder, Loogle, the search wrapper's grep, and local `rg` over both library
roots were used before proving. The new nodes record their three searches.
Existing declaration signatures and public imports stay unchanged, so no change
record or downstream adaptation is needed.

## New nodes

`lem-asd-ordinary-finite-single-unit-naturality`, realized by
`Sheaf.AlgebraicGeometry.OrdinaryFiniteSingleUnitNaturality` and the proved theorem
`AlgebraicGeometry.Etale.ordinaryFiniteSingleUnit_naturality`. It states naturality
of the prescribed inverse tensor right unit for an arbitrary derived morphism.
Its source, complete proof in words, edge cases and searches are recorded.

`lem-asd-ordinary-finite-p1-evaluation-recipe-base-change`, realized by
`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1EvaluationRecipeBaseChange` and the proved
theorem `AlgebraicGeometry.Etale.ordinaryFiniteP1_evaluationRecipe_baseChange`.
It gives the equality before adjunction, assuming the Chern-map pullback square.
It has no Kummer specification, existential class, unit-component conclusion or
exchange morphism. It is a proved part of the argument, with its source, full
proof in words, edge cases and searches recorded.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
