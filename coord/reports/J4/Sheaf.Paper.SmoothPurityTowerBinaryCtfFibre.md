## What changed

Replaced `AlgebraicGeometry.ProEtale.SpTowerBinaryCtfFibre.binary_ctf_fibre`'s
unfinished proof by an explicit distinguished fibre construction. The proof defines
the prescribed difference of adjunction mates, takes a distinguished cocone,
packages the counit projections as restriction isomorphisms, and proves their
overlap equation from the triangle's zero composite using adjunction naturality.
It derives Noetherianness from the existing finite-type hypotheses and evaluates
the selected restriction isomorphisms before applying finite-level locality.
Every existing declaration signature and public import is unchanged.
The remote compiler accepted all three modules (9.1, 41.3 and 58.4 seconds).

Two new modules isolate genuine separate steps: arbitrary-fibre local projection
invertibility in `SmoothPurityTowerFibreProjections`, and finite-coefficient bounds
for an already existing object in `ProEtaleBinaryCtfLocalModels`. Neither new
statement is the original existence theorem under another name. The first needs
no cover or finiteness predicates; the second involves no tower, triangle,
overlap map or global-object existence. Both have a source, complete proof in
words, and corresponding nodes. The parent node records the actual assembly.

## Proved and sorry left

Decomposition, not an unconditional proof: one original hole is closed and two
strictly simpler holes are added (net minus one).

Closed: `AlgebraicGeometry.ProEtale.SpTowerBinaryCtfFibre.binary_ctf_fibre`
(node `lem-sp-tower-binary-ctf-fibre`). Its fibre construction and compatibility
proof are complete Lean. The two private categorical helper theorems
`restriction_mate` and `fibre_compatibility` are proved without new holes.

Added and remaining:

- `AlgebraicGeometry.ProEtale.SpTowerShriek.tower_fibre_projections`
  (`lem-sp-tower-fibre-projections`), the pro-etale sequence-site transport of
  the existing abstract fibre-projection theorem.
- `AlgebraicGeometry.Scheme.proEtale_binary_ctf_of_local_models`
  (`lem-sp-proetale-binary-ctf-local-models`), finite-level locality in the
  exact fixed-module and all-resolution Tor predicates used by this item.

There are zero remaining holes in the item module and two in the new modules.
No definitions contain holes. No existing statement or definition changes.

## No longer needed

Removed private imports from the item:
`Sheaf.CategoryTheory.RingedToposBinaryDescent`,
`Sheaf.Paper.SequenceSiteOpenExtension`,
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.SixFunctors.GeometricInverseImageConstantModule`, and
`Mathlib.Topology.Constructible`.
The concrete proof only imports its two new interfaces. Public imports stay verbatim.

The parent's former direct proof dependencies
`lem-pur-sequence-site-open-extension`,
`lem-weil-proetale-weakly-etale-localization`,
`det-sp-coefficient-towers-abelian`,
`lem-sp-ringed-topos-binary-descent`,
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`def-weil-proetale-tor-amplitude`,
`def-weil-proetale-constructible-sheaf`,
`def-weil-constructible-subset`,
`def-weil-proetale-inverse-image`,
`lem-sfb-geometric-inverse-image-constant-module`, and
`sk-def-sp-normalized-towers` are no longer direct proof dependencies.
The applicable geometry, tensor and constructibility facts remain dependencies
of the two new steps or of the unchanged statements. This delivery claims no
whole module withdrawn or pruned. In particular the unit route stays intact.
The parent no longer uses the entire binary-descent existence theorem: ordinary
triangulated completion plus the smaller fibre-projection assertion suffices.
Its obsolete top-level tool approvals are removed; the new nodes declare their
own intended generic tool uses for independent review.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the assigned statement was found. The original proof
plan did not provide the concrete sequence-site-to-geometric-operations
transport required to apply the abstract ringed-topos theorem directly. Its
steps 3--6 also require explicit transport between intrinsic scalar realization,
fixed-module constructibility and the all-resolution Tor predicate.

The library already proves `Scheme.finiteCoverCTFLocality`; it supplies much of
the locality argument, but its public conclusion gives finite support rather
than the specified cohomological interval, uses intrinsic ringed-module
constructibility, and tests its chosen derived tensor. The new finite-level
lemma records precisely the remaining presentation and interval assembly,
with that existing theorem in its proof plan. No duplicate general
finite-cover theorem is asserted and no etale-origin condition is added.

## New nodes

`lem-sp-tower-fibre-projections`: the counit projections from any distinguished
binary direct-image fibre are invertible on the respective opens. Its proof
transports the actual sequence-site restrictions to the published geometric
operations and uses `lem-sp-ringed-topos-fibre-restriction`.

`lem-sp-proetale-binary-ctf-local-models`: given an existing finite-coefficient
complex and its two selected local models, descend constructibility and the
same two intervals. It is the uniformity portion only; it constructs no glued
object and asserts no fibre data. Empty schemes and zero coefficients are
included in the proof plan. Mathlib semantic, natural-language and source
searches found no exact match.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
