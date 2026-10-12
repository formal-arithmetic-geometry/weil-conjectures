## What changed

Proved `AlgebraicGeometry.Scheme.exists_irreducible_refinement_topological` in
`lean/Sheaf/AlgebraicGeometry/IrreducibleStratificationRefinement.lean` without changing its
statement or existing docstring. Added three fully proved private helpers in the same module.

The first helper enumerates the finite irreducible components of a Noetherian topological
space. It subtracts earlier components, proves local closedness and disjointness, and covers
the space by choosing the least component containing each point. Nonemptiness and
irreducibility follow from the open complement of all the other components:
`closure_sUnion_irreducibleComponents_sdiff_singleton` and
`IsPreirreducible.subset_irreducible`. This is the component argument of Stacks Tag 0052.

The second helper realizes any locally closed subset as a scheme immersed in the ambient
scheme: take its coborder open subscheme and the vanishing ideal of the closed preimage of
the subset there. `IdealSheafData.range_subschemeι` identifies its image. The third helper
combines these constructions, transporting irreducibility along the immersion's homeomorphism
onto its range.

The main proof applies the construction to every original stratum. Its underlying space is
Noetherian by the inducing map of the original immersion. A finite dependent sum, reindexed
by `Fin`, collects the new domains; their immersions are composites into X. The proof checks
coverage, disjointness within each original stratum by injectivity, disjointness between
original strata, constructibility, refinement, and irreducibility. Empty original strata
contribute no components; an empty scheme gives an empty dependent sum. No nonemptiness
assumption or scheme-theoretic factorization through an image is used.

The component-disjointification route is unchanged. The second reading updates the DAG's
proof record to name the Mathlib APIs actually used and removes its unused scheme-level edge.
Read Stacks Tags [0052](https://stacks.math.columbia.edu/tag/0052) and
[0BA8](https://stacks.math.columbia.edu/tag/0BA8), and the Mathlib implementations of the
component, subscheme, and homeomorphism lemmas. The unit route is retained.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.exists_irreducible_refinement_topological`
(node `lem-weil-pbc-irreducible-refinement-topological`), replacing the module's sole `sorry`.
The three private helpers `irreducible_partition`, `exists_immersion_locallyClosed`, and
`exists_irreducible_stratification` are fully proved. No `sorry` remains and none is split off.

Local compilation passes without warnings. `#print axioms` for the public theorem reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. The original public import `WeilConjectures.ConstructibleSheaf.Refinement` is required
by the statement and retained. Temporary proof imports
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `Mathlib.Topology.NoetherianSpace`
were removed after checking that the original import already supplies their declarations.
The old proof dependency `lem-weil-pbc-noetherian-finite-components` is no longer used:
the proof applies the more general topological Mathlib theorem directly to the underlying
strata, which need only have Noetherian topology. The node remains in the library; this
delivery removes only this proof edge. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The statement is true as written and the planned route
can be completed using existing Mathlib APIs. The local checkout has no Stacks source files;
the cited tags were read on the Stacks website. No statements, definitions, target signatures,
or public imports were changed.

## Second reading by J1

1. Compared the complete delivered module with the repository version. The sole existing
   theorem signature and its docstring are byte-for-byte unchanged. The public import is
   unchanged and required by `Stratification.Refines`. No definitions or public statements
   were altered, and no change record is required.
2. Independently compiled the module with `lcompile.py`, without errors or warnings.
   Inspected all three private helper proofs and the main proof: no `sorry`, axiom, unsafe,
   opaque, extern, or implementation override occurs. A scratch copy's `#print axioms`
   checks cover each helper and the public theorem; all use only `propext`,
   `Classical.choice`, and `Quot.sound`.
3. No statement was split off. Checked the helper statements and their arguments, including
   empty spaces, empty original strata, a single component, and overlapping components.
   The nonempty open core of each component is contained in its remainder, so irreducibility
   is valid even when earlier components intersect it. Coborder and vanishing ideal produce
   an immersion with exactly the prescribed range; the homeomorphism transfers
   irreducibility. Searched repository declarations and independently queried LeanFinder
   for locally closed subsets realized by immersions; found useful ingredients but no
   replacement for the whole construction. No new public theorem or node is needed.
4. The proof follows the existing finite-component disjointification route using proved
   Mathlib declarations throughout. Its single import is necessary for the statement.
   Read `dag/units/sk-prop-sf-cbc.json`: this item's helper route replaces no realized unit
   statement or step. Corrected `No longer needed` to list the unused scheme-level
   finite-components node; the stronger topological result is used directly instead.
5. Read the item's node and its old proof dependency. Updated only `proof` and
   `proof_deps` in the item's node to match the compiled proof and its Mathlib ingredients;
   the documented origin and the mathematical route remain valid. No new node or
   statement change is present.

Second reading changed only the DAG dependency bookkeeping and this report. The Lean proof
needed no repair.
