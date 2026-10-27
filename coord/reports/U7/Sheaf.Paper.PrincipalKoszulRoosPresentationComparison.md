## What changed

Replaced the proof hole in `CategoryTheory.principalKoszulRoos_presentation_comparison`
by the normalized derived-limit assembly from a strict singleton tensor tower comparison.
The theorem statement and both existing unit definitions are unchanged.

The proof transports the actual ordinary-limit augmentation along the strict tower
isomorphism, using joint monicity of the limit projections in each cochain degree.
The Roos naturality and augmentation formulas then give the actual unit, rather than
an arbitrary isomorphism of objects. Uniqueness of right derived functors compares
the Roos derivation with the specified `D.inverseLimit`; `D.tensorFactors` supplies
the prescribed target. The existing localization lemma `unit_app_Q` identifies
`D.unit` on the representative with its defining ordinary-limit composite.

Added `Sheaf.Paper.PrincipalKoszulDualTowerComparison`, isolating the finite chain
calculation in the original proof step 1. It asserts an augmentation-compatible
strict isomorphism of the two tensor towers. Unlike the original item, its statement
has no derived categories, inverse limits, exact-products hypothesis or arbitrary
limit presentation. The proof remaining in that module is the signed rank-one Hom
calculation and tensor symmetry, including the strict transition equations.

The new modules were checked on the cases a=0, a invertible, P=0, the zero ring and
empty sites in the natural-language calculation. No regularity or K-flatness is used.
The unit `sk-def-sf-operations` has no realized proof steps bypassed here.

## Proved and sorry left

One original hole closed syntactically:
`CategoryTheory.principalKoszulRoos_presentation_comparison`, node
`lem-pur-principal-koszul-roos-presentation-comparison`.

One hole added:
`CategoryTheory.principalKoszul_dual_tower_comparison`, node
`lem-pur-principal-koszul-dual-tower-comparison`.

This is a decomposition, not a net hole reduction: the derived-limit comparison,
normalization, representative-unit equality and their combination are proved; the
strict finite tower identification remains. The item has zero textual holes and
the delivery has one. No definition or private helper contains a hole.

Server validation: the finite-comparison module compiles on the server. An initial
assembly proof compiled in 47.1 seconds but a later check took 63 seconds. Profiling
identified expensive concrete tower unfolding in map composition. The map calculation
is now a proved generic helper in the same file, instantiated by the main proof;
no file was split to avoid the limit. Profiling options have been removed.
The delivery tool performs the final compile and preflight checks.

## No longer needed

No existing module is withdrawn and no existing public import is removed.
The original proof-dependency node
`lem-weil-pbc-ringed-cech-koszul-dual-kflat`, module
`Sheaf.CategoryTheory.RingedCechKoszulDualKFlat`, is not needed on this proof route:
the actual strict isomorphism is applied to P before any localization, so no
K-flatness or tensor preservation of quasi-isomorphisms is required here.
That module remains a transitive import through the reused scalar-comparison
unit API; its removal from this node's direct proof plan is not claimed as
pruning it from the targets' import closure.

The large statement `lem-weil-strict-roos-comparison` is not invoked directly.
The proof uses its proved derivation component `lem-weil-strict-roos-derivation`
and the existing canonical termwise-limit comparison from
`lem-sf-strict-roos-derived-limit-comparison`. The latter module still imports
the full comparison, so this is not claimed as pruning its import closure.
The private `unit_app_Q` API of
`lem-weil-pbc-flat-scalar-koszul-tower-comparison` is reused by `import all`;
no declaration is duplicated or changed there.

## Where the brief, the DAG or earlier work was wrong

The earlier plan calls the entire finite dual, transition, augmentation and tensor
symmetry calculation elementary, but no existing declaration states that strict
identification. The new node exposes exactly this missing step. The two declared
proof dependencies alone do not state it. The normalized derived comparison and
localization unit transport are available and have now been combined in Lean.
No statement was found false and no target, source-library declaration, existing
signature or definition was changed.

## New nodes

`lem-pur-principal-koszul-dual-tower-comparison` is the strict finite calculation
from step 1 of the original node, sourced to Stacks Tag 0A0E. It is strictly simpler
than the parent: it concerns actual complexes and tower maps only. Its docstring
and node provide the complete calculation of supported degrees, differential,
transitions, augmentation, tensor symmetry and edge cases. LeanSearch, LeanFinder,
Loogle and Mathlib grep were tried; local library and blueprint searches found no
existing exact comparison. There are no change records because all existing
public interfaces and definitions are unchanged.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
