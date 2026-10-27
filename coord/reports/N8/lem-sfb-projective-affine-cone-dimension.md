## Worker report

Module: `Sheaf.AlgebraicGeometry.ProjectiveAffineConeDimension`.
Main declaration: `AlgebraicGeometry.ProjectiveSpace.exists_unique_affineConeProjection`.
The module supplies the full statement of lem-sfb-projective-affine-cone-dimension,
with exactly one postponed theorem and three definitions containing real data.
The definitions only name the punctured open, chart condition, and cone subset
introduced by this node; they do not introduce independent mathematical notions.
No node statement, dependency record, or proof plan was changed.

Source read: literature/stacks-project/varieties.tex, Tag 0B2R,
lemma-intersection-in-projective-space, proof, lines 6374–6404.
The node expands the projection and cone argument from that paragraph.
The nine-step natural-language proof in the declaration docstring preserves the
node's chart gluing, Laurent product, residue-field specialization, closure,
reduced closed subscheme, dimension, finite-cover, dense-open, and irreducibility
arguments and cites their DAG dependencies. Every already stated proof-dependency
module is imported, including the Mathlib modules for spectrum maps, gluing,
closed immersions, irreducibility, and polynomial-ring dimension. Some Mathlib
modules are already public imports of the explicit dependency modules.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary field is `(k : Type u) [Field k]`, without an algebraic-closure,
  characteristic, cardinality, or rational-point hypothesis.
- The integer `N ≥ 0` is `(N : ℕ)`. The homogeneous coordinates are indexed by
  `ULift.{u} (Fin (N + 1))`. ULift preserves exactly the N+1 coordinates while
  matching the universe of the scheme API; it imposes no size restriction on k.
- `P` is the recorded `ℙ(ULift (Fin (N+1)); Spec (CommRingCat.of k))`.
  `A` is Mathlib's `𝔸` with the same coordinate type and base. Both are precisely
  the base-change constructions in the dependency nodes.
- The functions `x_i` are `AffineSpace.coord (Spec (CommRingCat.of k)) i`.
  `A.basicOpen` of this section is exactly `D(x_i)`.
- `affineConePunctured k N` is the supremum of these N+1 basic opens.
  `AffineSpace.range_zeroSection` identifies its complement with the common
  zero locus of all coordinates. Over Spec k the zero-section image is a single
  point, the origin. No identification with just the k-rational points is used.
- The standard projective opens are the dependency's `standardOpen`.
  `standardOpenIso` identifies them with affine space on the other coordinates.
  Its affine coordinates are exactly the ratios `u_{j/i}`; this is stated in
  the Charts module's definition docstring and computation theorem
  `homOfSections_resLE_standardOpenIso_hom` (lines 214–232).
- `HasAffineConeCharts k N π` first requires the structural-map equality over
  Spec k. This is the constants clause in the specified k-algebra homomorphisms,
  rather than an extra hypothesis on a geometric object.
- Its next clause says `π ⁻¹ᵁ standardOpen ... i` equals the preimage of `D(x_i)`
  under the punctured open inclusion. These are equal opens on the punctured
  scheme, rendering the node's equality of preimages exactly.
- Its final clause applies `(π ∣_ standardOpen ... i).appTop` to the chart
  coordinate and requires the result times the restricted `x_i` to equal the
  restricted `x_j`, for every `j ≠ i`. The preimage clause makes `x_i` invertible
  on this open. Hence this is exactly `u_{j/i} ↦ x_j/x_i`. The structure-map
  equality fixes every coefficient from k, so polynomial generation determines
  precisely the node's spectrum map, not merely its underlying point function.
- The existential binds a scheme morphism π with `HasAffineConeCharts`.
  The following universal quantifier is over EVERY π' satisfying that chart
  condition alone and concludes `π' = π`. Thus it asserts exactly the unique
  prescribed projection, independently of subsequent cone properties.
- `affineConeSet k N π Z` is the union of the zero-section image with the
  image under the open inclusion of `π ⁻¹' Z`. Thus it is exactly `{o} ∪ π⁻¹(Z)`
  as a subset of the entire affine scheme, with its induced topology.
- The theorem quantifies over every `Z : Set P` and assumes only `IsClosed Z`.
  `IsClosed (affineConeSet k N π Z)` is the unconditional closedness conclusion,
  including empty Z.
- For each `d : ℕ`, the assumptions `Z.Nonempty` and
  `topologicalKrullDim Z = (d : WithBot ℕ∞)` render the nonempty finite-dimension
  hypothesis; ℕ is exactly the specified nonnegative integers.
- `topologicalKrullDim (affineConeSet ...) = ((d + 1 : ℕ) : WithBot ℕ∞)` is the
  dimension-shift conclusion. Both dimensions use the actual subset topologies,
  and the type retains minus infinity for empty spaces and infinity.
- Under these same hypotheses, `IsIrreducible Z → IsIrreducible (affineConeSet ...)`
  states the additional irreducibility conclusion. `IsIrreducible` is the exact
  nonempty closed-cover notion in the dependency's Mathlib match.
- The final equality says `affineConeSet k N π ∅` is the zero-section image,
  exactly the convention `C(∅) = {o}`. This clause does not apply the nonempty
  dimension shift to the empty set.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs (full class signature read).
- def-nagata-projective-space-base-change:
  `AlgebraicGeometry.ProjectiveSpace`,
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace, definition and docstring.
- lem-weil-pbc-projective-space-standard-charts:
  `AlgebraicGeometry.ProjectiveSpace.projectiveSpace_standardCharts`,
  Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts, full theorem and proof
  docstring read. `standardOpen` comes from the recorded module's upstream
  OfSections import. The canonical `standardOpenIso` in the additional Charts
  import realizes the same standard-chart ratios, without another chart choice.
- def-sbc-affine-space: `AlgebraicGeometry.AffineSpace`,
  Mathlib.AlgebraicGeometry.AffineSpace; also read `coord`, `SpecIso`,
  `SpecIso_inv_appTop_coord`, and the coordinate description over affine bases.
- def-kun-topological-krull-dimension: `topologicalKrullDim`,
  Mathlib.Topology.KrullDimension, complete signature and docstring.
- def-weil-irreducible-components: `IsIrreducible` and `irreducibleComponents`,
  Mathlib.Topology.Irreducible; the predicate is nonemptiness plus preirreducibility.
- Existing zero-section construction and its zero-locus characterization:
  `AffineSpace.zeroSection` and `AffineSpace.range_zeroSection`,
  WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace. The standard-chart module
  publicly imports this API. No second zero section or coordinate system is defined.

Edge cases checked mathematically before writing:

- `N = 0`: P is P^0, A is A^1, and the punctured open is G_m. The off-diagonal
  coordinate type is empty, so only the coefficient/structural-map clause remains.
  The sole nonempty closed subset has dimension zero; its cone is A^1 of dimension
  one. There is no spurious nonempty off-diagonal-coordinate hypothesis.
- Empty Z: the cone is only the origin and is closed; its dimension is zero,
  while dim Z is minus infinity. The theorem does not assert the shift here.
- `d = 0`: a closed point with a nontrivial residue extension still has a cone of
  dimension one. The proof uses its residue field, not a k-rational representative.
- Arbitrary positive characteristic and nonperfect fields are admitted.
- Reducible nonempty closed Z is admitted by the closedness and dimension clauses;
  irreducibility is used only for the additional conclusion.
- The full projective space gives all affine space as its cone, with the expected
  N to N+1 dimension shift. No dimension overflow is lost by using WithBot ℕ∞.

Searches actually performed on 2026-10-24:

- msearch.py leanfinder: "Affine cone of a closed projective subset is closed and
  has dimension one more and is irreducible". Eight results, led by
  `ProjectiveSpectrum.isClosed_zeroLocus`, `isClosed_iff_zeroLocus`, and Proj affine
  charts; none assert this projection, cone dimension shift, and irreducibility.
- msearch.py loogle: `"topologicalKrullDim", "ProjectiveSpectrum"`. Zero results.
- msearch.py grep: `cone.*[Dd]im|[Dd]im.*cone|punctured`, AlgebraicGeometry.
  One unrelated AffineTransitionLimit categorical-cone match.
- msearch.py leansearch: "The cone of a nonempty closed subset of projective space
  has Krull dimension one greater". Eight results: basic topologicalKrullDim facts,
  unrelated convex/asymptotic cones, and a categorical opensCone. No exact match.
- rg over lean/WeilConjectures and lean/Sheaf:
  `projective.affine.cone|affine.cone|cone.*[Dd]imension|[Dd]imension.*cone`.
  Found the already stated consumer ProjectiveClosedIntersectionDimension, normal
  cones, and triangulated-category affine cone models, none defining this cone.
- grep -rn of this node ID under lean/WeilConjectures returned no match.
- Read the relevant Mathlib AffineSpace, Field, KrullDimension and Irreducible
  definitions and the upstream projective-space chart definitions directly.

No STATEMENT-DISPUTED issue, missing prerequisite, new independent definition node,
or dependency-interface repair was found. The node already avoids the informal
source's punctured-versus-closed-cone shorthand by specifying the origin explicitly.

Validation: scompile.py N8 lem-sfb-projective-affine-cone-dimension with the delivered
module passed both sandbox and actual-library-path compilations (1.9 s and 2.0 s),
with no errors or unexpected warnings. All variables and the universe u are bound
explicitly; all source lines are at most 100 characters. The main theorem has only
`sorry` as its proof, and all three helper definitions have actual data.

## Second reading by N8

I reread the original node alongside the final module, including each definition.
This is a worker self-check; the assignment prohibits launching another agent and
reserves the independent review for the maintainer. No independent reader is claimed.
The structural-map equality is necessary because the node specifies k-algebra maps:
pointwise ratio relations alone would not fix endomorphisms of the coefficient field.
The ratio equations are on the scheme-theoretic preimage charts and multiply by a
coordinate invertible there, so they specify precisely the displayed local morphism.
The cone uses the open inclusion's image, not a subset of the punctured scheme treated
as if it were already in affine space. Uniqueness tests the chart predicate alone.
The dimension and irreducibility clauses retain the finite nonnegative d assumption,
while closedness and the empty-set convention remain unconditional for closed Z.
The N=0 coordinate subtype may be empty and the universe lift does not change its
cardinality. No mismatch requiring a statement correction was found or concealed.
