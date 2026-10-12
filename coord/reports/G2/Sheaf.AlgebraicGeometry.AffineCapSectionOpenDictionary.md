## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_cap_section_open_dictionary` with its
original signature. The private, fully proved `invertible_global_sections` transports the
existing affine invertible-sections result from the global section ring to `R`. Mathlib
supplies finiteness, projectivity, and a rank-one equivalence at each prime. The existing
`Module.prime_mem_localized_iff` gives prime membership. The final locus equality is proved
by transporting the extended-ideal membership through the counit stalk isomorphism and the
canonical tilde localization, using `Submodule.restrictScalars_map_smul_eq`.

Added proof imports of `WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections`,
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`,
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`,
`Mathlib.RingTheory.Localization.Module`, and `Mathlib.RingTheory.Ideal.Maps`.
The original public imports and all existing signatures and visibility are preserved.
No other existing module is adapted. Updated the item's DAG proof and dependencies.

The module compiles cleanly with lcompile.py. The statement works without a nonzero-ring
hypothesis: the zero ring has no prime points, and the affine invertible-sections theorem
still applies. No arbitrary witness is used to define an object; the stalk equivalence
comes from the canonical localization map and its bijectivity.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.affine_cap_section_open_dictionary`
(`lem-sc-affine-cap-section-open-dictionary`). There are no sorries left in the delivered
module, and no holes added or split off. This is a proof from existing declarations,
not a decomposition. The private `invertible_global_sections` is fully proved.

The unchanged dependency `Module.prime_mem_localized_iff`
(`lem-sc-affine-finite-projective-prime-membership`,
`Sheaf.RingTheory.AffineFiniteProjectivePrimeMembership`) still has a sorry in the base
library. It is used as the stated stage-3 dependency, not re-proved in this delivery.
All the affine invertible-sections and stalk-localization constructions used here are
existing source-library or Mathlib declarations.

## No longer needed

Removed proof imports:
- `Sheaf.Paper.NonvanishingSectionTrivializes`.
- `Sheaf.RingTheory.FiniteProjectiveOfStandardCover`.

The item's proof no longer uses `lem-weil-pbc-nonvanishing-section-trivializes` or
`lem-sc-affine-standard-cover-finite-projective`, nor their two modules above.
The latter module's proof-specific subtree
`Sheaf.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover`
(`lem-sc-affine-standard-cover-finite-presentation-flat`) is also unnecessary on this
branch. This does not assert that these modules are unreachable from all other targets.

The direct parent step no longer requires
`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` or the explicit standard-open
finite-cover construction. `lem-weil-pbc-spec-module-tilde-sections` is still recorded
inside the closed affine invertible-sections source proof, and the tilde module remains
needed for the statement and the stalk argument. The node
`lem-pc-finite-flat-affine-sections-projective` records a closed source theorem used
inside that existing affine invertible-sections proof.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The original planned finite-cover argument was
unnecessarily long for this module: the public, sorry-free source theorem
`AlgebraicGeometry.Scheme.Modules.invertible_sections_of_isAffineOpen` already proves
the needed affine module invertibility. It had no DAG node recording its declaration,
so this delivery adds a node for the existing theorem rather than restating it in Lean.
The source proof was read in `Modules/InvertibleSections.lean`, together with
`Modules/LocallyFreeAffine.lean` and the Mathlib tilde/stalk and ideal-map APIs.
The unit `sk-thm-curveestimate` realizes its statement only at `thm-sc-proper-cohomology`
and has no realized steps here; no unit statement or route is bypassed.

## New nodes

`lem-sc-affine-invertible-sections` records the existing public theorem
`AlgebraicGeometry.Scheme.Modules.invertible_sections_of_isAffineOpen` in
`WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections`. It states invertibility
of the sections over an affine open as bijectivity of dual-tensor evaluation, exactly
Mathlib's `Module.Invertible`. It is an existing closed source declaration, with no new
Lean module and no new sorry. The node records its finite-presentation and basic-open
localization argument. LeanSearch was unavailable; the actual search results and the
source-library match are recorded. No change record is needed: no public interface changes.

## Second reading by G2

1. Compared the delivered module with the repository version. Existing declaration
   signatures and visibility are unchanged; only proof imports, the private helper, and
   the target proof differ. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked for forbidden constructs and
   unlisted `sorry`s. The target has no local sorry; its reported `sorryAx` comes only
   from the pre-existing `Module.prime_mem_localized_iff` dependency. Verdict: pass.
3. Checked the target and the added existing-theorem node against their source statements.
   No new split-off theorem was added, and the affine invertible-sections declaration is
   already present in the source library. Verdict: pass.
4. Re-read the proof from the target downward. The route uses the existing affine
   sections theorem and canonical tilde/stalk localization APIs, and removes the unused
   standard-cover and nonvanishing imports and dependencies. Verdict: pass.
5. Checked that the DAG proof, `proof_deps`, `proof_origin`, and unit metadata match the
   Lean proof. The unit route remains recorded and no definition or statement changed.
   Verdict: pass.

Changed after second reading: no mathematical or interface changes; this section records
the comparison, compilation, axiom, pruning, and DAG checks.
