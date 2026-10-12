## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.exists_affineEtale_baseChange_geometry`
by a compiling reduction, keeping its signature, the data structure, and the geometry
predicate unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.AffineEtaleNormalizedCartesianSystem` and the Mathlib import
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` for the affine limit projections.
The other Mathlib facts are already exposed by the public statement imports; redundant direct
imports were removed after recompiling the full set.

The new module `AffineEtaleNormalizedCartesianSystem` constructs the normalized cartesian
pullback functors and their first projections. It applies a smaller statement in the new module
`AffineEtaleNormalizedCartesianComparisons` for the normalized comparison isomorphisms and
their first-projection equations. It assumes any preorder diagram and a cone with affine
projections; it needs neither directedness nor a limiting cone nor qcqs stages. It does not
assert either cocycle or any site property. Its construction follows the base-change system
underlying Stacks 0EYL, with the diagonal normalization made explicit. The functor construction
uses `ObjectProperty.lift` of ordinary étale pullback, actual first projections, and the identity
functor on repeated indices. Functors and their projection/square witnesses are constructed
together to avoid mismatched dependent casts. No data is chosen from an unproved existence
theorem: `normalizedPair` is proved using those explicit constructions.

In the item's module, the proved private helper `cartesian_hom_ext` tests equality using
pullback projections. The proof writes both cocycle calculations using the supplied comparison
projection equations and naturality. The proved private helper `cartesian_site_geometry`
cancels cartesian object squares to obtain cartesian arrow squares, proves preservation of
finite étale covers by lifting points, identifies the functor after affine inclusion with
ordinary étale pullback, reflects pullback preservation, and proves continuity through the
pretopology sheaf criterion. These facts supply all eight clauses omitted from the helper.
The existing node's proof and dependency list follow this reduction.

## Proved and sorry left

Closed the item's sole direct hole:
`AlgebraicGeometry.Scheme.exists_affineEtale_baseChange_geometry`
(node `lem-weil-pbc-affine-etale-base-change-geometry`). No `sorry` remains in the item.
Both new private helpers are proved.

Also proved the new declaration
`AlgebraicGeometry.Scheme.exists_affineEtale_normalized_cartesian_system`
(node `lem-weil-pbc-affine-etale-normalized-cartesian-system`) from actual pullback functor
constructions and the comparison statement. Its private `normalizedSquare` and `normalizedPair`
lemmas and the proofs inside its concrete definitions are complete.

Added one direct hole:
`AlgebraicGeometry.Scheme.exists_affineEtale_normalized_cartesian_comparisons`
(node `lem-weil-pbc-affine-etale-normalized-cartesian-comparisons`), in
`Sheaf.AlgebraicGeometry.AffineEtaleNormalizedCartesianComparisons`. Its proof is exactly
`by sorry`; its docstring supplies the construction, source, and complete proof in words.
It assumes the already constructed functors, projections, cartesian squares, and diagonal
identity projections, and asserts only the comparison isomorphisms with five normalization
and first-projection clauses.

This is a decomposition, not a complete proof independent of holes: one hole closed and one
strictly smaller hole added, with net zero holes. The two cocycles and all six site properties
are proved in Lean rather than transferred into the new hole. The helper covers the empty
preorder, one-stage diagrams, repeated indices, and arbitrary affine cone projections.
The covering argument retains `Fin n`, including `Fin 0`, without a nonempty-cover assumption.

All three delivered modules compile without warnings with `lcompile.py --all` (approximately
3–5 seconds per module). The required dry run checks their axioms and delivery preflight.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.LimitAffineTransition`: the supplied limiting cone's affine
  projections follow directly from Mathlib `AlgebraicGeometry.isAffineHom_π_app`; no
  relative-spectrum or quasi-coherent-algebra limit construction is needed here.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: continuity on the full affine site
  follows directly from cover preservation, pullback preservation, and the sheaf criterion.
  No sheaf adjunction, Kan extension, or six-functor construction is needed here.

Consequently `lem-weil-pbc-limit-affine-transition` and
`lem-weil-pbc-etale-base-change-continuous` are removed from this node's proof dependencies.
This is pruning of this proof's imports and edges, not a claim that other target branches
no longer need those modules. The affine-morphism permanence, ordinary étale base-change,
and pullback-pasting nodes remain needed, directly or in the remaining construction node.
No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan is usable, but its limit-existence dependency is unnecessary when the
statement already supplies a limiting cone. Its six-functor continuity declaration concerns
the full small site; the affine-site continuity clause is proved directly here.

The existing docstring cites 00X1 for continuity. That tag defines a morphism of sites;
the actual continuity proof here uses Mathlib's pretopology sheaf criterion. The existing
signature and docstring have been kept unchanged. Stacks 0EYL and its discussion were read at
https://stacks.math.columbia.edu/tag/0EYL; the diagonal normalization is the explicit
construction needed to make that discussion precise.

LeanFinder, Loogle, and source grep were run for the new construction. Ordinary
`MorphismProperty.Over.pullbackComp` exists and supplies the comparison machinery, but does
not state the normalized full affine system. LeanSearch returned Internal Server Error;
this is recorded as unavailable, not as a no-match verdict. Blueprint searches for affine
étale base change, base-change, and 0EYL found no duplicate normalized construction statement.

## New nodes

`lem-weil-pbc-affine-etale-normalized-cartesian-system` states the cartesian construction and
normalized comparison data only, in `Sheaf.AlgebraicGeometry.AffineEtaleNormalizedCartesianSystem`.
The functors, projections, and cartesian squares are constructed and proved in Lean. Its
first-projection equations are used to prove the parent's cocycles; its cartesian object
squares are used to prove all site properties.

`lem-weil-pbc-affine-etale-normalized-cartesian-comparisons`, in
`Sheaf.AlgebraicGeometry.AffineEtaleNormalizedCartesianComparisons`, isolates only the remaining
comparison construction for supplied cartesian functors with identity diagonal projections.
The isomorphisms are uniquely determined by their projection equations. This is smaller than
the system theorem, and omits its functor construction as well as the parent's cocycles and
site properties. Both nodes inherit chapter `sec-proper-base-change`, unit `sk-thm-p1`, and the
same nearest blueprint ancestor as the item's node. Statements, proof steps, actual search
records, sources, and verbatim Lean signatures are included. No existing statement or
definition changed; no change record is needed.

## Second reading by R3

1. **Statements and interfaces.** Compared the delivered target module with the repository
version. The target declaration and all existing structure and predicate signatures are byte
for byte unchanged. The two new declarations match their DAG nodes; the comparison statement is
strictly smaller than the target because it assumes the functors, projections, and cartesian
squares and concludes only comparison isomorphisms and projection equations.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`.
The target has no `sorry`; the only remaining `sorry` is the named comparison theorem, and it
is a public theorem with a source, a complete proof sketch in its docstring, and a matching
split node. No forbidden declarations or hollow definitions occur.

3. **Search and truth of split statement.** Read Mathlib's `IsPullback.isoIsPullback`
construction and projection equations, and checked that the supplied hypotheses determine each
comparison uniquely. The statement handles empty and singleton preorders and repeated indices,
and does not assume unnecessary directedness, nonemptiness, affineness, or a limiting cone. No
duplicate library declaration was found.

4. **Pruning and imports.** The proof-only imports are the normalized construction module and
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`; the former supplies the realized unit route,
while the latter supplies affine limit projections. The former limit and six-functor imports
are no longer needed and are recorded above. The node proof and dependency records follow the
implemented reduction; no unit statement or realized step was bypassed.

5. **DAG and report consistency.** Checked the three node records against declarations, proof
dependencies, sources, and unit/chapter fields. The system node records the completed
construction and the comparison node records the sole split hole. The report lists the one hole
closed, one strictly smaller hole added, and all pruned imports and dependencies.

**Changes made during second reading:** added this review section only; no Lean declarations,
signatures, definitions, or DAG records required repair.
