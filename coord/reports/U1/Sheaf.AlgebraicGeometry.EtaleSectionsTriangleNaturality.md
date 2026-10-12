## What changed

Replaced the rejected composite-specialization split with a genuine reduction of
`AlgebraicGeometry.Etale.sectionsComparison_triangle_naturality`. Its signature and
visibility are unchanged. The target proof now combines the one-morphism restriction
square with proved localization, sections-unit naturality, transport along `q.inv`,
and homology functoriality.

Added `Sheaf.AlgebraicGeometry.EtaleSectionsRestrictionSquare`, containing exactly
one public intermediate theorem. Added a proof-only import of that module. The private
`sectionsUnit` is the explicit composite of existing comparison maps, with no choice or
proof hole; its naturality and `triangle_localization` are fully proved. Updated the
original DAG proof and added the restriction-square node. No existing definition,
statement, universe or visibility changed, and no adaptation is required.

Both modules compile cleanly through lcompile.py. The unit record `sk-prop-h2` has
empty realized statement/step lists; this changes only the categorical detail below it.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.sectionsComparison_triangle_naturality`.
The private helpers `sectionsUnit_naturality` and `triangle_localization` are proved
without holes. Added one hole:
`AlgebraicGeometry.Etale.sectionsComparison_restriction_square`, node
`lem-weil-pbc-sections-comparison-restriction-square`.

This is a decomposition (one upper hole closed, one lower hole added), not a net hole
reduction. The remaining statement has one morphism and one complex and stops before
triangle composition, change of representation and homology. The target proof performs
all three of those steps in Lean, so the intermediate is strictly part of the argument.
There are no other delivered sorries and none inside definitions or private helpers.

## No longer needed

Removed the proof-only imports:
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`;
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.

The last two are redundant direct imports: their declarations remain publicly available
through GlobalSections and are used. This does not claim they leave the target closure.
The bounded-below PlusAdjunction module is not used by this proof. Removed
`lem-weil-pbc-right-derived-plus-injective` from this node's proof dependencies: neither
the restriction square nor its triangle transport uses injectivity, boundedness, or
inversion of a sections unit. The original inverse-image, cohomology and adjunction
nodes remain needed for the constructions. Removed the sandbox's rejected circular
`EtaleSectionsTriangleNaturalityCore` module and its node; neither is imported.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery merely specialized `h` to `a ≫ g` and handed the original
identity to another name. Its report incorrectly called this a strictly smaller
reduction, and its node depended back on the target. Both have been replaced.
The existing plan's bounded-below injective-unit dependency is unnecessary for this
unbounded statement; only ordinary naturality and exact-localization isomorphisms
are cancelled.

Read the final paragraph of Stacks Tag 03Q9 at
https://stacks.math.columbia.edu/tag/03Q9. It constructs the maps of sections complexes;
the categorical naturality detail here is agent-written using the existing Lean
adjunction and derived-composition factorization infrastructure. LeanFinder, Loogle
and source searches found that infrastructure but no combined restriction square.
LeanSearch returned an Internal Server Error, recorded as unavailable.

Edge cases: the restriction square uses no inverse of a sections comparison and no
hypothesis of etaleness, injectivity or boundedness. Zero and unbounded complexes,
empty schemes and arbitrary scheme morphisms are included. Negative homology degrees
appear only in the proved final application of the homology functor.

An attempt to prove the restriction square in the homotopy category established the
adjunction and Leray-unit factorizations, but elaborating their final combination
exceeded the single-file compiler limit. That exploratory proof is only in scratchpad;
the delivered remaining theorem is exactly `:= by sorry`, with the complete mathematical
argument in its docstring and node. No timeout workaround or shared dependency change
is included.

## New nodes

`lem-weil-pbc-sections-comparison-restriction-square` records the one-morphism,
pre-homology restriction square, with its exact Lean signature, source, independent
proof plan, edge cases and searches. Its module is
`Sheaf.AlgebraicGeometry.EtaleSectionsRestrictionSquare`. It depends only on the
existing inverse-image, cohomology and adjunction infrastructure and has no dependency
back to the triangle theorem. No change record is needed.

## Second reading by U1

1. **Visible changes and statements.** Compared both delivered Lean modules and the triangle node with the repository versions. The target theorem signature is byte for byte unchanged; the only new public statement is the restriction square, recorded by its new node. No existing definitions or interfaces changed. Verdict: pass.
2. **Compilation and proof status.** Compiled both modules with `lcompile.py --all`; both compile without errors or warnings. The triangle theorem and its private helper lemmas are proved; the restriction square is the one explicitly documented split-off `sorry`, with no `sorry` in a definition and no forbidden declarations. Verdict: pass.
3. **Split-off statement.** Checked the restriction-square statement against the one-morphism reduction used by the triangle proof. It is strictly smaller than the target (one morphism, before homology and transport), has a complete source/proof docstring and a matching DAG node, and does not duplicate an existing declaration. Edge cases in the docstring cover arbitrary morphisms and complexes. Verdict: pass.
4. **Pruning and route.** Verified the target proof uses the restriction square, localization factorization, sections-unit naturality, and homology transport. The removed imports and removed injective-unit dependency are unused; the target's remaining route is preserved. Verdict: pass.
5. **DAG agreement.** Checked the target node's proof steps, dependencies, origin, and the new restriction-square node against the Lean proof and module declarations. The unit route remains represented and no circular dependency remains. Verdict: pass.

I changed only this report section during second reading; no Lean proof or statement required repair.
