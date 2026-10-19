## Worker report

This is stage 2, not a resplit. The Q138 record is a stage-1 review: the current
item has no `lean` or `reviewed_lean`. Its previous worker's stale-assignment
explanation confused those stages. The retained sandbox contained only launcher
brief markers and no Lean delivery.

The item module states two theorems, each with exactly `by sorry`:
`AlgebraicGeometry.exists_normalizedNodalQuotientRefinement` for any selected
reduced dominant component, and
`AlgebraicGeometry.normalizedNodalQuotientRefinements_cover` for the finite
alteration covering clause. `MarkedNodalQuotientModel` packages the input data;
`NormalizedNodalQuotientRefinement` packages all the output data and comparisons.
These are helper records for this node, not independent alternative definitions
of nodality, Cartier divisors, normalization, quotients or covering families.
Every map in the output is either constructed directly or fixed uniquely by its
projection equations. No object is defined using a postponed existence theorem.

Hypothesis correspondence (Q denotes the input record):

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`. Finite ell-group: `(G : Type v)
  [Group G] [Finite G]` and `Q.ell_group : ∃ n, Nat.card G = ell ^ n`.
  The group universe v is independent of the scheme universe u.
- Integral Y prime: `[IsIntegral Y']`. Its excellence and Noetherianity are
  `excellent_cover`, `noetherian_cover`.
- The admissible base action is `aY`, `admissible_base`. Its quotient is b,
  characterized by `over_base` and the categorical universal property
  `quotient_base`. In particular b is not assumed finite to bypass Step 1.
- Y affine/integral/excellent/Noetherian is `affine_base`, `integral_base`,
  `excellent_base`, `noetherian_base`. Invertibility of ell is `ell_unit`,
  tested in every stalk, so it includes the stated global unit condition.
- The closed boundary on Y is `T : Closeds Y`. Its exact inverse image is
  T prime; `rare` gives its nowhere-density. Stable subsets of the orbit
  quotient are saturated, so this encodes T = T prime/G without replacing
  the given boundary by its closure.
- The finite etale torsor on the complement is `torsor : GaloisCoverAction`.
  `torsor_iso`, `torsor_map`, `torsor_action` identify its map and action with
  the actual inverse-image open under b. No connectedness of the original
  torsor is added. Closedness was made explicit by the recorded correction.
- The curve morphism is f; `aC`, `equivariant` encode its action.
  `projective`, `flat`, `finite_presentation` give projectivity, flatness and
  finite presentation. Projectivity supplies quasi-compactness and separatedness,
  so the locally finite presentation class gives full finite presentation here.
- C integral/excellent/separated/Noetherian is `integral_curve`,
  `excellent_curve`, `separated_curve`, `noetherian_curve`.
- Connected nonempty nodal geometric curve fibres are `nodal`, using the
  existing `HasNodalGeometricFibres`, including dimension one and the specified
  completed local rings. `smooth_off` gives smoothness away from T prime.
  `smooth_generic`, `integral_generic` concern the actual generic fibre of f.
- The marking is D; `marking_cartier`, `marking_stable`, `marking_finite`,
  `marking_etale`, `marking_smooth` give each marking hypothesis individually.
- X is the admissible categorical quotient of C through π: `admissible_curve`,
  `invariant_curve`, `quotient_curve`. The map p is the unique descended map,
  pinned by `square`; it is not an independent unconstrained morphism.
- The Cartier divisor E and its support inclusion are `boundary_cartier` and
  `boundary_support`. Its ideal is real quasi-coherent ideal-sheaf data.
- The new base is integral, affine, Noetherian by explicit instance binders,
  regular by `hregular`, excellent by `hexcellent`. The morphism u1 is dominant,
  locally finite type and quasi-compact, hence finite type as in the node.
- H1, `hsnc`, `hsupport` specify exactly an snc boundary with support u1 inverse T.
- Z, `hZ`, `hdominant` specify any irreducible component dominating Y1.
  F, j, `[IsIntegral F]`, `[IsClosedImmersion j]`, `hcomponent` represent its
  reduced induced subscheme. A reduced closed subscheme is determined by its
  closed support, so this permits every component and makes no extra choice
  of a thickening. F normalization is the existing canonical normalization.

Conclusion correspondence (R denotes the refinement record):

- `H`, `decomposition` say that H is exactly the subgroup stabilizing Z under
  the actual pullback action `baseChangeActionMap`.
- `R.model` has base Y1, cover F normalization, and curve exactly the pullback
  of Q.f along `normalizedNodalComponentMap`. It includes all the same nodal,
  generic geometry, integrality, excellence, separatedness, admissibility and
  marking conditions individually listed above, now for H.
- `base_map`, `curve_map` identify its structure maps with the canonical
  normalization and pullback projections. `boundary_set`, `marking` identify
  the exact pulled-back boundary and divisor.
- `lifted_base_action`, `lifted_curve_action` specify the restricted original
  action on the two projections. Together with the structure maps and
  equivariance, they fix the actions on the canonical pullback.
- `finite_base`, `normal_base`, `base_quotient` assert finite normalized cover
  and its exact quotient Y1. `connected_torsor` adds the required connectedness
  of this component's actual torsor on the complement.
- `function_field_algebra`, `field_map` pin the field structure to the map b1.
  `normalization_iso`, `normalization_map` identify the cover over Y1 with
  Y1 normalization in that very function field, rather than an unspecified
  normal finite model.
- X1 and `model.π` are the new quotient; `finite_quotient` gives its orbit
  quotient topology and invariant structure sheaf. `integral_quotient`,
  `noetherian_quotient`, `excellent_quotient` give all three asserted properties.
- `toOriginal`, `quotient_square`, `base_square` fix the actual quotient map
  to X and its map over Y. `boundary_pullback` identifies E1 with E.comap;
  the model's `boundary_cartier` and `boundary_support` give its Cartier
  property and exactly the requested support containment.
- `comparison` maps to the canonical reduced dominant subscheme of X times Y1.
  `comparison_original` and `comparison_base` pin both projections.
  `proper_comparison` and `birational_comparison` give properness and
  isomorphism on a dense open with dense preimage, including actual scheme
  structure rather than equality only of point sets or function field degrees.
- The covering theorem assumes a finite cover in the recorded alteration
  topology, integral members, regularity and snc supports, and one selected
  component/refinement per member. Its conclusion supplies objects in alt/X
  whose underlying maps are exactly `R i.toOriginal`, with a covering family
  of the same index set. X Noetherian is supplied existentially in the conclusion,
  not imposed as an extra hypothesis. Thus a single arbitrary dominant map is
  never asserted to be a covering.
- The final nodal-completion and invariant-sheaf conventions are precisely the
  existing predicates, not weakened placeholder properties.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms.
- Mathlib.AlgebraicGeometry.Properties: `IsIntegral`, `IsReduced`.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing` (scheme Noetherianity is
  the existing `IsNoetherian` from Mathlib.AlgebraicGeometry.Noetherian).
- Sheaf.RingTheory.ExcellentRing: `IsExcellent`, tested on every affine open.
- Sheaf.AlgebraicGeometry.IsRegularScheme: `IsRegularScheme`.
- Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary:
  `IsStrictNormalCrossingsBoundary` on the given quasi-coherent Cartier ideal.
- Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology:
  `PrimeToEllAlteration.Alt`, `IsCoveringFamily`, `topology`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper/FiniteType/Finite/Flat/FinitePresentation/
  Smooth/Etale: `IsProper`, `LocallyOfFiniteType`, `IsFinite`, `Flat`,
  `LocallyOfFinitePresentation`, `Smooth`, `Etale`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsHProjective`, read
  through scompile --source because this module is newer than the old checkout.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  `pullback`, its projections, and `pullback.map`, also for geometric fibres.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible:
  `Scheme.IdealSheafData.IsInvertible` and actual ideal-sheaf comaps/subschemes.
- Sheaf.AlgebraicGeometry.NormalScheme: `IsNormalScheme`, `Scheme.GaloisCoverAction`.
- WeilConjectures.Mathlib.AlgebraicGeometry.Normalization:
  `Scheme.normalization`, `fromNormalization`, `normalizationIn`,
  `fromNormalizationIn` with the specified function-field algebra.
- Mathlib.AlgebraicGeometry.Geometrically.Integral: `GeometricallyIntegral`.
- Added already-landed statement dependencies:
  def-per-admissible-finite-scheme-quotient, using
  `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient` /
  `IsAdmissibleFiniteSchemeQuotient`; and def-trf-nodal-geometric-fibres, using
  `Sheaf.AlgebraicGeometry.NodalGeometricFibres` / `HasNodalGeometricFibres`.
- The item imports the available recorded proof modules without `public`.
  Unrecorded proof nodes (the admissible affine quotient, projective finite-group
  quotient, alteration cover calculus) have no module to import. They are not
  missing notions used to type this statement and are not restated here.

Edge cases read against both the node and the actual record types: trivial G and
trivial decomposition subgroup; a split torsor with several components; a connected
torsor whose stabilizer is all G; empty T, D or E; a nonflat dominant base change;
reducible nodal special fibres; and finite covers with no arbitrarily fixed member.
ConnectedSpace in the nodal predicate includes nonemptiness. Integral F excludes
an empty selected component, exactly as irreducible components do. The empty
marking is an invertible unit ideal. No smoothness of the quotient total space,
normality of the original Y prime, flatness of the normalization, or equality
between normalization and ordinary base change was assumed. The original torsor
may be disconnected. All universes and variables are bound explicitly.

Searches were run through msearch.py, plus source/DAG rg and blueprint_refs.py:
LeanFinder query 'normalized base change of a finite group quotient of a marked
nodal curve with decomposition subgroup and proper birational quotient comparison'
returned elliptic-curve base change and normalization coproduct lemmas, no match.
Loogle query 'AlgebraicGeometry.Scheme.normalization, MulAction, IsPGroup' returned
unknown identifier for the project normalization (not a match). Mathlib grep
'Nodal|nodal|AdmissibleAction|decompositionSubgroup' in AlgebraicGeometry returned
zero. Source and side-library searches reused the landed nodal and finite-quotient
predicates and found no theorem stating this refinement; a source query through
scompile for the proposed item module reported unavailable, consistent with the
absent Lean record. The reduced-part searches and results are recorded in its new
node. No STATEMENT-DISPUTED flag remains: the only node fault found is the explicit
closed-boundary typing correction below.

## New nodes

`def-per-dominant-reduced-part` defines the actual vanishing ideal of the closure
of the union of irreducible components dominating an integral base, with its
subscheme and canonical inclusion supplied by existing IdealSheafData APIs.
For Noetherian X the union is finite and closed, exactly ILO II 1.2.5, pp. 25--26.
LeanSearch and LeanFinder returned the component, dominance, reducedness and
normalization ingredients; Mathlib grep returned only DominantPartialMap.
DAG, blueprint, upstream and side-library searches found no construction of this
part. Mathlib's `vanishingIdeal` is reused rather than copied. No postponed
existence assertion supplies data. This new node is cited directly by the item.

## Statement corrected

The old statement is retained verbatim in `statement_change.old_statement`.
Its boundary phrase was 'Let T prime subset Y prime be G-stable nowhere dense'.
The complement was then used as an open subscheme in a finite etale torsor.
Closedness had not been stated. ILO IX 1.2 and 1.4, printed pp. 131--133, use a
closed nowhere-dense boundary; the correction says 'G-stable closed nowhere dense'.
The added convention citations record the reused nodal/quotient predicates and
reduced dominant-part construction. No proof, proof dependency, or unit statement
is changed. The item is an auxiliary statement below the unit, not the unit itself.

The complete citer audit has one node:
`lem-per-uniformization-nodal-quotient-reduction` — holds true. Its induction starts
from the closed boundary T of ILO IX 1.4; T prime is its inverse image and is closed.
No citer was edited. The other grep matches were the item's own metadata and the
helper's created/blueprint ancestry, not statement/proof dependency citations.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
