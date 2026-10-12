## What changed

Filled `AlgebraicGeometry.IsCurve.dense_open_integral_boundary_finiteness` with a
complete Lean proof. Its signature, existing docstring, and public imports are unchanged.
The private, proved helper `finite_constructible_stalk` extracts finite abelian stalks
from set-valued constructibility by lifting a geometric point into its stratum.

The proof establishes the complement dimension bound from
`exists_dense_irreducible_opens`, explicitly identifies the integral encoding's
underlying sheaf using the equivalence counit, and uses the module/abelian pullback
comparison. Degree zero is finite by the finite product of finite stalks; positive
degrees are subsingletons by zero-dimensional cohomology and the Ext/derived comparison.
The finite-morphism edge map transfers finiteness back to the boundary on the curve.
Updated the item's DAG proof, proof dependencies, and proof origin to match this route.

Added proof-only imports for DenseIrreducibleOpens, EtaleInverseImageAlgebraicStructures,
EtalePullbackForgetModules, UniversalHomeomorphism, UpperLowerStar.Stalk, and
CohomologyClopen. The unit route remains unchanged: this is a tool calculation below
its algebraically closed extension step.

`lem-weil-pbc-etale-inverse-image-algebraic-structures` belongs to `sk-def-exchange` and
is used as a general comparison tool for underlying sets of abelian inverse image.
The curve unit's definitions do not themselves supply that comparison. The existing
zero-dimensional cohomology and sections tools are retained as prescribed by the plan.

Local compilation succeeds without warnings. The searches actually run were LeanFinder
for zero-dimensional etale cohomology (eight unrelated cotangent/singular cohomology
results), Loogle for `Finite.of_equiv` (exact generic transport theorem), and launcher
grep for `subsingleton.*H|finite.*sheafFiber|closedComplement` (no boundary theorem).
Repository searches located the already proved finite edge map and dimension-bound
lemma. No new theorem with a hole was needed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.IsCurve.dense_open_integral_boundary_finiteness`
(node `lem-pbc-h2-dense-open-integral-boundary-finiteness`).

Added zero holes; split off zero statements. No `sorry` remains in the delivered module.
The private `finite_constructible_stalk` is proved. This is a proof from existing
recorded declarations, not a claim that every imported dependency is already closed.
In particular existing zero-dimensional cohomology and inverse-image comparison
modules retain their own dependencies; no such declaration is changed by this delivery.

## No longer needed

Removed direct proof imports:
- `Mathlib.AlgebraicGeometry.AlgClosed.Basic`;
- `Mathlib.AlgebraicGeometry.Noetherian`;
- `WeilConjectures.SixFunctors.Finite.Exact`;
- `Sheaf.AlgebraicGeometry.CurveCoefficientPair` (already publicly supplied by
  `ConstructibleTorsionCurveSheaf`);
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already supplied by
  the retained signature imports).

Removed direct DAG proof dependencies:
- `lem-weil-pbc-closed-point-residue-field-base`: no direct rational-point identification
  is needed, because both zero-dimensional tools accept arbitrary chosen geometric points;
- `lem-weil-pbc-finite-type-over-noetherian` and
  `lem-weil-pbc-noetherian-finitely-many-components`: the dimension argument is provided
  by the proved dense-irreducible-opens theorem;
- `lemma-weil-pbc-finite-direct-image-exact`: the proved finite-pushforward edge map
  supplies the cohomology comparison directly.

These are removals from this module's direct route. No whole-library unreachability is
claimed: the dense-open dimension lemma and finite edge-map module still use some of
these facts internally, and other targets may reach them independently.

## Where the brief, the DAG or earlier work was wrong

No statement correction was required. The original plan omitted explicit coefficient
and stalk comparison dependencies; these are now cited in the updated proof. The
integral encoding followed by forgetting is isomorphic to P.F through the equivalence
counit, rather than definitionally equal. The degree-zero terminal object must be
`Etale.mk (𝟙 Z)` with `MorphismProperty.Over.mkIdTerminal`, avoiding an opaque chosen
terminal object. These were elaboration issues resolved in the proof.

The helper is valid for any geometric point and any constructible abelian sheaf, without
torsion or a finite coefficient ring. Its point lifts along a stratum immersion because
that morphism is surjective on stalks, using the proved residue-field lifting theorem;
containment of images alone is not used as a scheme factorization assertion. Empty
schemes and empty complements are covered by the empty product, and dimension-zero
curves are included. No properness or ambient reducedness is assumed.


## Second reading by F1

1. Interface: PASS. Compared the sole delivered module with the repository using
   `diff -u`. The existing theorem signature and docstring are byte-for-byte unchanged;
   no definition, hypothesis, or conclusion changes. Public imports are unchanged.
   The only added declaration is the proved private stalk helper. There are no change
   records or additional delivered modules.
2. Proof: PASS. Independently compiled the module with `lcompile.py`: exit 0, no
   warnings. Read the complete proof, including the stratum point lift, equivalence
   counit, module pullback comparison, dimension embedding, product projections,
   degree-zero equivalence, positive-degree comparison, and finite edge map.
   No local `sorry`, forbidden declaration, or holed definition occurs. A scratch
   copy with `#print axioms` for the helper and main theorem reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx` from open
   imported statements; this closes the local hole, not the entire dependency closure.
3. Split statements: PASS, none added. The helper is proved and strictly smaller
   than the item. Reviewed constructibility's finite-stalk clause and the existing
   residue-field point-lifting proof: a stratum immersion supplies surjectivity on
   stalks, not an unjustified factorization from point containment. Repository searches
   for finite stalks, `IsFiniteSheaf`, and constructibility found no shorter direct
   finite-boundary assertion. The upstream finite-sheaf class expresses finite
   generation, so it is not a substitute for finite underlying abelian sets.
   Empty schemes, empty complements, zero-dimensional curves, and nonreduced
   complements are covered. Objects F, Z, and B are explicitly constructed; chosen
   comparison isomorphisms only transport finiteness between these fixed objects.
4. Route and pruning: PASS. Read `dag/units/sk-thm-p1.json`, including `realized`:
   this tool calculation is below its curve-calculation step and preserves its
   dense-open reduction. All new imports are proof-only. Each retained proof import
   supplies a declaration used in the argument; no unit step is bypassed. All four
   removed old proof dependencies were already reported. Two redundant direct imports
   had also been removed but omitted from the report; added their names above.
5. DAG: PASS. Compared the node with its repository version: only `proof`,
   `proof_deps`, and `proof_origin` change. Checked the recorded declaration for
   every dependency against its use. The union of the proof steps' `uses` is exactly
   `proof_deps`; the six steps match the Lean argument. No new node is required for
   an open theorem, since none is added.

Second-reading changes: completed the pruning report with the two omitted redundant
imports and added this independent review. No Lean proof repair was necessary.
