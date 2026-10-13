## What changed

Replaced the original hole in `resolution_open_scalar_comparison` by a proof using the
explicitly constructed `resolutionOpenComparison`, a composition of the right-derived
resolution comparison, the pinned section-complex isomorphism, and exact evaluation's
homology comparison. No definition contains a hole or chooses arbitrary data from an
unproved existence theorem. All existing public signatures and public imports are unchanged.

Five new modules supply the constructed comparison, the proved restricted-resolution
construction, general restriction naturality, its nonvanishing-open specialization,
and scalar compatibility. The second reader closed the draft restriction-naturality hole
by adapting the existing private `rawOpenIso_restriction` argument from
`SectionCohomologyUntwistedComparisons` to the arbitrary pinned resolution R. This directly
computes U-open sections on Y and avoids restricting injectives a second time.

Change record: `coord/changes/resolution-open-comparison-map.md` (new declarations only;
no existing statement, definition, or visibility changes and no forced adaptations).

## Proved and sorry left

Closed original hole:
- `AlgebraicGeometry.Scheme.Modules.resolution_open_scalar_comparison`
  (`lem-pc-resolution-open-scalar-comparison`).

Added holes: none. Sorries left in delivered modules: none.
The second reader also closed the first draft's additional hole
`AlgebraicGeometry.Scheme.Modules.resolution_open_restriction_natural`
(`lem-pc-resolution-open-restriction-natural`). The final delivery is a proof, not a
zero-net decomposition: one original hole closed, zero lower holes added. Ledger figures
for the entire targets' import closure remain the maintainer's measurement.

Constructed without sorry:
- `AlgebraicGeometry.Scheme.Modules.resolutionOpenComparison`
  (`def-pc-resolution-open-comparison-map`).

New proved theorems, all in `AlgebraicGeometry.Scheme.Modules`:
- `restrictedResolutionSections_exists` (`lem-pc-restricted-resolution-sections-exist`);
- `resolution_open_restriction_natural` (`lem-pc-resolution-open-restriction-natural`);
- `resolution_open_restriction_core` (`lem-pc-resolution-open-restriction-core`);
- `resolution_open_scalar_core` (`lem-pc-resolution-open-scalar-core`).

The private `unit_nonvanishing_basicOpen` and `homology_restriction_transport` helpers
are also proved. The scalar theorem uses the existing proved
`resolutionSectionsHomology_scalar` and Mathlib's derived/homology naturality.

## No longer needed

No original public import was removed. The new proof imports are plain `import`.
The proof of `resolution_open_restriction_natural` needs only the comparison module;
it does not import `RestrictInjectiveResolution` or another restriction-exactness module.

Of the original node's proof dependencies,
`lem-sc-ringed-space-restrict-injective-resolution` is no longer used by this proof.
The initial construction instead uses the existing
`lem-weil-pbc-module-open-restriction-injectives`; subsequent restriction naturality
computes both opens from R.resolution on Y. The other old dependencies remain used:
`def-weil-pbc-flat-base-change-open-choices` and `def-sc-open-module-cohomology` supply
actual constructions/definitions, while `lem-sc-nonvanishing-iff-generates-at` and
`lem-pc-resolution-sections-homology-scalar` are used in the two proved cores.
The top node's direct proof edges now name those cores and the constructed comparison
and restricted-resolution existence theorem; their nodes record the underlying uses.

Removed unused draft imports of `Ample` and `TensorSection` from the scalar core and
`Cohomology.Defs` from the comparison map. `Cohomology.Defs` remains public in the scalar
core because its statement uses `smulHom`.
The proof does not use `SectionCohomologyUnitComparisons` or
`ResolutionUnitTwistComparison`. No module is claimed to be globally unreachable:
pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The draft report said the general restriction computation was unavailable and had to
remain open. An existing proved private argument in
`SectionCohomologyUntwistedComparisons` supplies the needed calculation after adaptation
to R.comparison and R.components. Its public existential comparison theorem does not
pin the comparison to resolutionOpenComparison, so it cannot replace the fixed-map
statement by a direct application. The restricted-resolution construction likewise
already exists privately in `FlatBaseChangeOpenChoicesExist`, and the delivery reuses
that construction rather than introducing an arbitrary chosen witness.

An arbitrary additive equivalence need not preserve scalars. Both compatibility
proofs concern the same genuinely constructed comparison. There is no weakening of
the target. The sources are Stacks [01E1](https://stacks.math.columbia.edu/tag/01E1),
[01E2](https://stacks.math.columbia.edu/tag/01E2), and
[01E4](https://stacks.math.columbia.edu/tag/01E4).

## New nodes

`def-pc-resolution-open-comparison-map`: constructs the actual comparison from
specified isomorphisms. `lem-pc-restricted-resolution-sections-exist`: records the
proved restricted resolution with pinned sections. `lem-pc-resolution-open-restriction-natural`:
proves restriction naturality for inverse-image opens from R's actual section maps.
`lem-pc-resolution-open-restriction-core`: identifies the tensor-unit scalar
nonvanishing locus with the inverse image of the principal open and applies naturality.
`lem-pc-resolution-open-scalar-core`: transports the existing section-homology scalar
identity through the right-derived comparison. None of these nodes adds a hole.

Change record: `coord/changes/resolution-open-comparison-map.md`.

## Second reading by E4

1. Compared every delivered module with its repository counterpart. Only the item's
   module existed; its theorem signature and original public imports are byte-identical.
   The five other modules are new. No target or existing definition changed. Restored
   the original node's exact `lean` record and made new node signatures verbatim.
   Verdict: pass.
2. Read the complete construction and both compatibility arguments, and compiled the
   original six-file delivery successfully. Closed its sole new hole and compiled the
   complete restriction proof without errors or warnings. No forbidden declaration or
   sorry in a definition exists. Final module compilation and axiom evidence are
   recorded below. Verdict: pass.
3. Checked every new statement against its actual argument. Considered q=0, n=0,
   zero coefficients, empty opens, V=W, a=0, and unit a: the same section functors,
   naturality squares and invertible comparison cancellation apply without any new
   hypotheses. Searched by the concepts of derived section restriction and fixed
   resolution naturality using leanfinder, loogle, grep, and local/upstream rg.
   Found and adapted the existing private argument rather than retaining a hole.
   The public existential theorem does not assert compatibility of this fixed map.
   There are no remaining split-off sorry statements or restatements. Verdict: pass.
4. Verified the proof descends from the original target into its separate genuine
   restriction and scalar computations. The imports distinguish statement/definition
   needs from proof-only needs. The old restriction-resolution dependency replaced by
   the new route is explicitly listed above. Checked
   `dag/units/sk-thm-picard-coherence.json`: its realized statement list and sole step
   list are empty; this item realizes none of them. The unit record and route are
   unchanged. No globally pruned module is claimed. Verdict: pass.
5. Compared Lean bodies with every node's proof and proof_deps, checked each proof_deps
   is exactly the union of its steps' uses, and verified the new nodes' sources,
   creation/blueprint/chapter/unit/Lean/search fields. Updated the naturality node to
   describe the proved direct computation and its source in the existing library.
   Verdict: pass.

Second reading changed: closed `resolution_open_restriction_natural`, corrected its
proof docstring and node, restored/matched node signatures, corrected dependency-pruning
and hole counts in this report, and made the new-declaration record match actual
signatures and private visibility. The original combining proof, comparison construction,
restricted-resolution construction, scalar proof, and nonvanishing reduction were kept.

Final verification: `lcompile.py --all` compiled all six final modules without errors
or warnings (6.4, 8.1, 22.3, 49.5, 3.9, and 4.2 seconds). A scratch copy of the
item with `#print axioms` for the target and all five new public declarations compiled
successfully. Every printed axiom list was exactly `propext`, `Classical.choice`,
`Quot.sound`; none contained `sorryAx`. The scratch file is outside the delivered set.
Logs: `scratchpad/second-final-compile.log` and `scratchpad/second-axioms.log`.
