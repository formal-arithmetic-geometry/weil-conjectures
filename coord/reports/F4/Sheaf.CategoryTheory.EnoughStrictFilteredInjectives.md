## What changed

Proved `CategoryTheory.FilteredObject.enough_strict_filtered_injectives` in
`Sheaf.CategoryTheory.EnoughStrictFilteredInjectives`, keeping its mathematical statement
and public imports unchanged, including the original binder names. The unused-variable
linter is disabled only for the final theorem: its explicit finite-filtration hypotheses
are retained even though the extension proof needs finiteness only of the target.

The extension proof uses `injective_graded_filtration_splits`, turns strictness into a
pullback square, obtains monic quotient maps with Mathlib's
`Abelian.mono_cokernel_map_of_isPullback`, extends each component by `Injective.factors`,
and assembles the filtered extension. The existence proof explicitly constructs the finite
biproduct of injective presentations of `X/F^(n+1)X`, with filtration given by images of tail
inclusions. Component vanishing proves preservation and strictness. Each tail is injective;
splitting the successive short exact sequence makes its graded quotient an injective retract.
The final coordinate proves monicity. The bounded result supplies the unbounded result.
All supporting helpers are private and fully proved; no data is chosen from an unproved
existence theorem. The only choices of injective objects use Mathlib's proved presentation API.

Recorded the added command-level proof helpers and consumer audit in
`coord/changes/F4-enough-strict-filtered-injectives-proof-commands.md`; all 78 transitive
importers keep their statements without adaptation. The original theorem signature and
public imports are unchanged. Added proof imports of `Mathlib.Algebra.Homology.ShortComplex.ShortExact` and
`Mathlib.CategoryTheory.Abelian.CommSq`. Updated the existing node's proof to describe the
pullback and retract calculations. The unit route is unchanged.

Validation: resumed-session remote single-file compilation passes in 2.4 seconds without
errors or warnings. An exact textual comparison confirms that the final theorem signature
matches the current library source, including all binders. All lines meet the 100-character
limit, and the only changed existing-node fields are `proof` and `proof_origin`. The proof
handles arbitrary finite bounds, `a = b`, the zero object, and indices on either side of the
interval. No consumer requires adaptation because the public interface is unchanged.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.FilteredObject.enough_strict_filtered_injectives`
(node `lem-trf-enough-strict-filtered-injectives`). All three clauses are proved.

There are zero `sorry`s left in the delivered module and zero holes added or split off.
The extension proof uses the existing declared dependency
`CategoryTheory.FilteredObject.injective_graded_filtration_splits`
(node `lem-trf-injective-graded-filtration-splits`), which remains a `sorry` in its own,
undelivered module. The embedding clauses use Mathlib and the real filtration definitions.
This delivery does not claim to close that transitive dependency.

## No longer needed

No imports or mathematical dependency nodes or modules are pruned. Every declared dependency is used:
the compatible splitting lemma, abelian-category operations, filtrations, and injectivity.
The proof does not need a separate identification of each graded quotient of the split
filtration with a particular summand; the injective-retract argument suffices.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned quotient and finite-biproduct proof works.
An initial delivery compile timed out at 60 seconds; the same complete module subsequently
compiled in 20.1 seconds. A profiled compile completed in 42.2 seconds, with the final
theorem elaborating in 0.195 seconds. The axiom audit prints only `propext`,
`Classical.choice`, `Quot.sound`, and the existing splitting dependency's `sorryAx`.
The existing finite-biproduct construction needs an explicit local
`HasBiproduct.of_hasProduct` instance in this universe configuration. This is supplied
as a private proved theorem with a local instance registration, as in the dependency's
explicit biproduct arguments. It exports no global instance.

Earlier-attempt delivery infrastructure failure: the first dry run reached temporary-worktree creation
and crashed with `subprocess.TimeoutExpired`: `git checkout -q --detach origin/sheaf-dag`
timed out after 600 seconds. A second dry run was attempted once and was killed with exit
code 137 and no further diagnostic. Neither dry run pushed anything. This resumed session retains that proof and node update and reruns the required delivery
checks against the current sources. The
last source adjustment preserves all original theorem binder names and uses a local
unused-variable linter setting; it introduces no mathematical change.

The resumed dry run compiled the file and requested a change record for command-level
additions. Added that record and made finiteBiproduct a private proved theorem registered
only as a local instance. No mathematical interface repair was needed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
