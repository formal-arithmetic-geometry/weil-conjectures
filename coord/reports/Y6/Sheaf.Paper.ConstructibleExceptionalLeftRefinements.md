## What changed

The item now assembles the four coefficient cases from ring geometry, raw rational
localization, and a proved common-field descent argument. The original theorem's
signature and all public imports are preserved. Two private proof imports supply
strictly smaller, named ring and rational obligations, each in its own new module.

The closed comparison is constructed explicitly. Its component at a literal pair
is the rational component conjugated by the two common q isomorphisms. The scalar
square and commonTransitionNatural prove compatibility with transition arrows.
StageSystem.exists_stage_representation then reduces naturality of an arbitrary
arrow to a stage arrow and two transitions. A separate categorical cancellation
argument proves that shift compatibility can be checked after the stage inclusions.
This uses the supplied equal common shift structures rather than asserting that
an arbitrary chosen structure is the canonical one. No right refinement or
adjunction compatibility equation is assumed or split off.

Only the item module, its node, two new modules and their nodes are changed.
Remote compilation passed for both new modules (48.0 and 51.2 seconds) and the
item (33.1 seconds). Profiling options were removed before delivery; delivery
checks recompile the final sources. The original signature and public imports
were also compared directly with the shared source and are identical.

## Proved and sorry left

The old hole in
WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_left_refinements
is closed by decomposition. The item has zero holes remaining. Two holes are added:

- WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_left_refinement,
  node lem-sf-constructible-ring-left-refinement.
- WeilConjectures.ConstructibleExceptionalCoefficients.exists_rational_left_refinement,
  node lem-sf-constructible-rational-left-refinement.

This is one upper hole replaced by two smaller holes, not a net proof. The ring
statement constructs finite and integral maps and their integral scalar square;
it asserts no field-stage comparison. The rational statement assumes the
integral maps and constructs only their localization and rational scalar square;
it asserts no ring construction or closed-stage comparison. The closed descent
and four-case assembly are proved in the item.

The existential choices do not select arbitrary geometric data. The open
adjunction transpose uniquely fixes the proper/open comparison in
RingRefinementNormalized; canceling the left realizations and using faithfulness
of the full inclusions uniquely fixes each ring component. The rational component
equation likewise fixes every component, since residue-Tor equality identifies
the integral finite-Tor category with the intrinsic integral category and raw
localization has the same objects. The closed maps are explicit composites.

Edge cases checked in the statements: identity refinements use identity
proper/open words; zero objects and the empty source use the same zero maps;
repeated common fields and identity transition maps are included in all the
universally quantified equations. Neither endpoint scheme is required to be
separated over the ground field.

## No longer needed

The planned direct dependency lem-sf-exceptional-refinement-mates, module
Sheaf.Paper.ExceptionalRefinementMates, is not used by this proof and is removed
from this item's proof_deps. That theorem also constructs right comparisons and
whole-system witnesses that this item does not need. Its lower geometric and
scalar ingredients remain in the ring lemma's proof plan; no adopted source
module or public declaration is removed. No existing Lean import is removed.

## Where the brief, the DAG or earlier work was wrong

The supplied DAG step suggests immediately taking the left part of
exceptional_refinement_mates. Its Transport input requires the chosen localization
shifts to have prescribed canonical components and the common inclusion shifts
to equal the canonical choices. The present normalization only says that the
choices for different compactifications agree. Those equalities do not imply
canonical normalization. The new route uses precisely the equalities actually
supplied. It also explicitly uses commonTransitionNatural in the closed-stage
naturality proof rather than treating stage inclusions as jointly full.

## New nodes

lem-sf-constructible-ring-left-refinement is the finite/integral proper/open step
with the integral coefficient-field scalar square. Its proof plan follows Stacks
0F7B/0F7I, Zheng 5.13--5.15, actual strict-system realization and the proper/open
scalar square. This is strictly below the all-stage item.

lem-sf-constructible-rational-left-refinement is localization of a given integral
family on the fixed rational functors, including shifts and the localized scalar
square. It uses residue-Tor equality and unique raw localization of natural
isomorphisms. This is a descent step and contains no geometric construction or
closed comparison. Both nodes inherit the item's chapter and unit. There are no
shared interface changes or change records.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
