## What changed

Proved `AlgebraicGeometry.Scheme.purTwistZlAction_existsUnique` in
`Sheaf.Paper.PurTwistSheafLocallyFree`, retaining its exact signature and all definitions.
Two proved private helpers establish automatic linearity over constant finite coefficient
sheaves and semilinearity of the root transition maps. The proof constructs each scalar
endomorphism by the evaluated root tower's limit property, verifies module laws and
restriction compatibility after projecting to every finite level, and uses joint
injectivity of those projections to prove uniqueness. This implements the coordinate-action
portion of step 4 of `lem-pur-twist-sheaf-locally-free` without changing the node's route.

The retained sandbox also contains proved private helpers `purTwistIntegers_basis`,
`purTwistUnitsPower_locallySurjective`, and `purTwistTransition_epi`. They establish a
finite integral basis and locally surjective root transitions, for use in the main theorem.
Proof imports were added for `Sheaf.Paper.SiteSheafificationSectionsLocal`,
`Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp`, and
`Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`. The existing
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` import is retained.
Public signatures, definitions, and other modules are unchanged.

## Proved and sorry left

Closed one of the three existing holes:
`AlgebraicGeometry.Scheme.purTwistZlAction_existsUnique`.
Added zero holes; split off zero statements.

The two remaining holes, unchanged, both belong to
`lem-pur-twist-sheaf-locally-free`:

- `AlgebraicGeometry.Scheme.purTwistIntegralAction_existsUnique`: the completed action on
  the prescribed ordinary integral tensor still needs the coefficient-comparison and
  sheafified tensor-action argument.
- `AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free`: the finite root trivializations,
  compatible local generators, integral comparison, finite reductions, and derived
  completeness assertions remain to be proved.

The automatic-linearity helper uses the existing
`CategoryTheory.torsionSheaf_hom_linear`; its upstream remaining proof obligations are
unchanged. The new limit-action proof contains no additional intermediate holes.

## No longer needed

None. No existing imports were removed. The completed-action construction uses the
existing root modules and Mathlib's evaluated-limit API. The remaining two holes still
need their recorded routes, so no node or module is claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The integral action is not merely another instance of
the coordinatewise root-limit construction: it requires the comparison with the completed
integral coefficient sheaf and extension of the action to the sheafified ordinary tensor.
This delivery leaves that existing obligation unchanged.

On resumption, several validation attempts received no answer from the compile server.
A subsequent direct compile passed in 7.8 seconds, and the required delivery dry run
passed compilation and server preflight with review class AUTO. The finite-root
trivialization experiments remain in `scratchpad/`; they are not delivery modules and
introduce no library holes or declarations.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
