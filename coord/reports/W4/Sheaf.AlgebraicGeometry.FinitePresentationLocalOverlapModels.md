## What changed

Replaced the upper hole in `AlgebraicGeometry.exists_finitePresentation_local_overlap_models`
with an explicit assembly from two strictly smaller steps: lifting natural overlap maps,
then imposing identity and cocycle equations on the canonical pullbacks of those same maps.
The existing theorem's signature and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.LocalOverlapTransitions`: a concrete structure of natural
maps before the identity and cocycle laws, its explicit base-change construction, a
coherence predicate, and a constructor for descent data. Every supporting definition is
constructed from supplied objects and maps; none chooses data from an unproved existence
theorem. Its component-comparison lemma proves coherence at the limit by cancellation.
The canonical chart-refinement maps and their projection identities are also proved.

Added the two theorem modules `FinitePresentationOverlapMapLifting` and
`FinitePresentationOverlapCoherence`. The first lifts maps and glues them on refinement
intersections, without asserting identity or cocycle laws. The second asserts eventual
identity and cocycle equations for the *specified canonical pullback* of the first maps;
it does not choose a replacement datum. Both retain the original finite-presentation,
quasi-coherence, finiteness, and quasi-separatedness hypotheses.

In the main proof, the local object isomorphisms are transported along the explicit chart
refinements and composed with `pullbackCompOfEq`. The descent datum is constructed field
by field from the natural maps and the coherence proof. Its comparison morphism has the
homs of the supplied component isomorphisms, with the actual commutation proof, and each
component is invertible. Only proof imports were added to the existing module.

The item's DAG proof now follows these two steps and the explicit assembly.
The complete main module and the categorical construction module compile through
`lcompile.py`; both lower statement modules also compile. A text comparison with the
repository confirms that every existing declaration and signature is unchanged.
The required `deliver3.py --no-push` dry run checks the complete set and its axiom probes.

## Proved and sorry left

Closed the upper hole of `AlgebraicGeometry.exists_finitePresentation_local_overlap_models`
(node `lem-pc-fp-local-overlap-models`) by decomposition. This is not a complete proof of
all underlying mathematics: one upper hole is closed and two lower holes are added, so
the net hole count of this delivery is -1.

The two remaining holes, each the entire proof of a named public theorem in its own module,
are:

- `AlgebraicGeometry.exists_finitePresentation_overlap_map_lifting`
  (`lem-pc-fp-overlap-map-lifting`): finite affine chart map lifting and gluing.
- `AlgebraicGeometry.exists_finitePresentation_overlap_eventual_coherence`
  (`lem-pc-fp-overlap-eventual-coherence`): eventual diagonal and triple equations for
  the fixed lifted maps, together with transport of their limit comparison.

No hole remains in the item's module. All declarations of `LocalOverlapTransitions`
are proved or concrete definitions. In particular its pullback naturality proof,
`Comparison.coherent`, and the chart projection identities are complete Lean proofs.

Edge cases checked for the new statements: an empty cover has empty families and vacuous
laws; zero modules have their unique maps; a constant diagram permits the identity stage;
a singleton cover still requires the diagonal identity, which the second lemma asserts.
No finite presentation of M is assumed or needed, because it is locally identified with
the prescribed finite models. The preorder need not be antisymmetric or globally nonempty:
the chosen j supplies the nonempty tail used in affine descent.

## No longer needed

Removed the main module's direct proof import of `Sheaf.Algebra.FinitePresentationColimit`.
That module and node `lem-pc-fp-module-map-descent-affine` remain needed by the two lower
steps and are imported there. The old direct proof dependency `lem-pc-fp-module-map-descent-affine` is no longer
used directly by the main theorem; it remains a dependency of both lower statements.
No transitive module or node is claimed pruned.

No inverse-map lifting is required in the split: natural transition maps with the
identity and composition laws have inverses given by the reversed transition. The
original plan's separately lifted inverses and inverse equations are subsumed by these
laws. The final proof needs no global module gluing, finite-presentation descent for
objects, or new finite-presentation conclusion about its components.

## Where the brief, the DAG or earlier work was wrong

The earlier abandonment correctly identified missing scheme-level gluing, but treated
that gap as a reason to stop. The gap can instead be separated into map lifting and
subsequent equations, with a real construction combining their outputs.

The original proof's elementary second step hid substantial Lean pseudofunctor and chart
refinement bookkeeping. This delivery proves that bookkeeping explicitly. It keeps the
unit route; the unit's realized fields do not require a different intermediate route.
No existing statement or definition was changed, and no forced adaptation is needed.

The local Stacks tex files are absent on this machine. The cited sources were read online
at https://stacks.math.columbia.edu/tag/01ZR (first proof) and
https://stacks.math.columbia.edu/tag/05N7 (map and equality clauses). LeanSearch returned
an Internal Server Error; each such search is recorded as unavailable, while actual
LeanFinder, Loogle and Mathlib-source searches supplied the other results. No existing
Mathlib theorem directly supplies either new scheme-level step.

## New nodes

`def-pc-local-overlap-transitions`: the concrete natural-map structure and its supporting
coherence, comparison, base-change and chart-refinement constructions, in
`Sheaf.AlgebraicGeometry.LocalOverlapTransitions`. This contains no holes.

`lem-pc-fp-overlap-map-lifting`: finite-stage natural overlap map lifting and compatibility
at the limit, in `Sheaf.AlgebraicGeometry.FinitePresentationOverlapMapLifting`.

`lem-pc-fp-overlap-eventual-coherence`: eventual identity and cocycle laws for the specific
canonical pullback of supplied transitions, in
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence`.

There are no change records: existing interfaces are unchanged.

## Second reading by W4

1. **Existing interfaces — pass.** Compared all four delivered modules with the
   repository: only the item's module existed there. Its diff changes three plain
   proof imports and the proof body only. Independently compared the complete existing
   theorem signature byte for byte; it and its docstring are unchanged. There are no
   changed definitions or signatures requiring a change record, and no forced adaptations.

2. **Proof and constructions — pass.** Independently compiled all four modules in
   import order through `lcompile.py`, with no errors or warnings. Read every field of
   `OverlapTransitions`, `Coherent`, `Comparison`, their pullback, and their assembly
   constructors. All data is constructed from supplied objects and morphisms; the
   existence witnesses are eliminated inside the main existential theorem's proof,
   never selected by a public definition. Cancellation proves limit coherence, and the
   refinement projection equations follow from the pullback lift. The only two sorries
   are the named theorem proofs listed above; there are no forbidden declarations or
   compiler escape mechanisms. Independent scratch `#print axioms` checks of all 19 listed declarations found
   only propext, Classical.choice, and Quot.sound in the construction module, and
   additionally sorryAx in precisely the main theorem and the two lower theorems.
   The delivery tool also runs its exhaustive declaration probes.

3. **Split statements — pass as a decomposition.** Read both full signatures and
   docstring arguments against Stacks Tags 01ZR (map and equality clauses and first
   proof) and 05N7. Map lifting omits finite-stage identity and cocycle equations;
   eventual coherence assumes specified natural maps and imposes equations on their
   canonical pullbacks. Thus neither simply renames the original theorem. Both are
   needed by the assembly. Naturality reduces the all-test-scheme conditions to the
   pairwise and triple fiber products, so finite affine covers suffice. Quasi-compactness
   and quasi-separatedness follow for the base-changed scheme and its finite open
   intersections. Checked empty covers, empty overlaps, zero modules, singleton covers,
   constant diagrams, and non-antisymmetric preorders. The chosen stage supplies a
   nonempty directed tail. The comparison identifies the limit objects locally with
   the finite models, so no extra finiteness hypothesis on M is needed.
   Independent LeanFinder search used “Morphisms between finitely presented quasi
   coherent sheaves descend along inverse limits of schemes and equality holds
   eventually”; Loogle used `"IsFinitePresentation", "IsColimit"`; Mathlib grep used
   `(descend|eventual).*(module|sheaf)|IsFinitePresentation.*[Hh]om`.
   None supplies the scheme-module statement. Searched both Lean source roots as well;
   the nearby `exists_finitePresentation_local_map_datum` concerns maps between global
   fixed models and remains sorry, so it does not close either overlap step. Neither
   lower theorem can be closed by a short application of an available result.

4. **Route and pruning — pass.** Read the main proof top downward: map lifting,
   eventual equations, then explicit assembly and transport. The direct old affine
   dependency is replaced by the two lower steps; it remains transitively required.
   `No longer needed` now explicitly names that old direct DAG dependency. The public
   imports supply signature or definition vocabulary; the new main imports and the
   lower affine imports are plain proof imports. The unit
   `dag/units/sk-thm-picard-semicon.json` has `realized.statement = []` and
   `realized.steps = [[]]`; none of its realized nodes is bypassed or changed. No
   transitive module is claimed pruned. This delivery closes one upper hole and adds
   two lower holes, for net -1; it does not prove the underlying theorem without sorry.

5. **DAG agreement — pass.** Compared the old node with its updated record: the
   proof, proof dependencies, and proof origin describe the actual assembly. The three
   new records have their source, complete statements, searches, creation metadata,
   blueprint ancestry, chapter, unit, and matching Lean declarations. Each holed
   theorem has its own module and node, and its Lean statement matches the record.
   The concrete construction node lists its supporting declarations and has no holes.

**Changes by the second reader:** clarified the old direct DAG dependency under
`No longer needed` and added this independent review. No Lean or node repair was
necessary. Remaining holes are deliberately retained as the two stated mathematical
steps, rather than counted as a complete proof.
