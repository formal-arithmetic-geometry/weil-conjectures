## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalClosureComponentCriterion` states
`AlgebraicGeometry.Scheme.strictLocalClosure_component_criterion`, with one postponed
proof (`sorry`). The natural-language node is unchanged. Its source was read in the
local ILO PDF, Expose XIV, printed pp. 209–210: the reduction paragraph immediately
before Proposition 2.1.3 and the proposition's complete proof. The source's generic
point x and closed point y are named y and x respectively in this DAG node.
No mathematical correction or disputed statement was found.

The four auxiliary abbreviations are fully constructed specializations belonging to
this node, listed in `lean.declarations`. `reducedPointClosure X y` is the existing
vanishing-ideal subscheme of `closure {y}`; `reducedPointClosureι` is its existing
subscheme inclusion. `reducedLocalClosure X y w` is the spectrum of the actual stalk
of that subscheme, and `reducedLocalClosureMap` is `fromSpecStalk w` followed by the
inclusion. No scheme, ring, morphism, point, or identification is selected from an
unconstrained existence theorem. These helpers introduce no independent notion and
require no new node: they only name the specific constructions already prescribed by
the item's statement and its recorded dependencies.

Hypothesis and clause correspondence:

- A Noetherian scheme is `(X : Scheme.{u}) [IsNoetherian X]`, using Mathlib's actual
  Noetherian scheme class (locally Noetherian plus compact). The points are `(x y : X)`;
  their required specialization is exactly `(hxy : x ∈ closure {y})`.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `(barX : Spec (.of Ω) ⟶ X)`. The over-x condition is the explicit equality
  `barX (IsLocalRing.closedPoint Ω) = x`. No characteristic restriction is imposed.
- W is the reduced closure defined above. The theorem supplies `w : W` with
  `reducedPointClosureι X y w = x`; it does not assume a lift of x to W. Thus the
  actual ring in `reducedLocalClosure` is A = O_(W,w), and Z is Spec A.
- The phrase “generic point y and closed point x” is rendered by the existence of
  `η : Z` satisfying `IsGenericPoint η Set.univ` and `reducedLocalClosureMap ... η = y`,
  followed by the equality sending `IsLocalRing.closedPoint A` to x. These are point
  identifications under the canonical morphism, not equalities between different types.
- The theorem supplies `barZ : Spec Ω ⟶ Z` and the exact factorization equality
  `hbarZ : barZ ≫ reducedLocalClosureMap X y w = barX`. This is the induced geometric
  point at the closed point of Z. Because the canonical stalk-spectrum map and the
  closed immersion are injective on points, this factorization forces its image to be
  that closed point. It also retains exactly the specified residue-field embedding.
- The identification is an isomorphism `e : strictHenselizationScheme barZ ≅
  pullback (strictHenselizationStructuralMap barX) (reducedPointClosureι X y)`.
  Its first projection is required to be the *existing canonical*
  `strictHenselizationMap (reducedLocalClosureMap X y w) barZ`, transported by
  `eqToHom (congrArg strictHenselizationScheme hbarZ)` to the equal geometric point barX.
  Its second projection is exactly the strict-local structural map followed by
  `W.fromSpecStalk w`. These two equations characterize the isomorphism's forward
  map uniquely by the pullback universal property and imply compatibility over X.
  The isomorphism is consequently not an arbitrary map or a bare Nonempty iso.
- Put T = `strictHenselizationScheme barZ`. Identification of all points over y is
  `Set.BijOn (e.hom ≫ pullback.fst _ _)` between the two explicitly written fibres
  of `T ⟶ Z ⟶ X` and `X_(barX) ⟶ X`.
- For each `t : T` over y, the next clause supplies a homeomorphism `E` from
  `closure {t}` to `closure {(e.hom ≫ pullback.fst _ _) t}` in the ambient strict
  localization. Its equation `(E z).val = (e.hom ≫ pullback.fst _ _) z.val` requires
  the homeomorphism to be precisely the restricted comparison map. The following
  equality of `topologicalKrullDim` is the requested equality of closure dimensions.
- Every T-point over y is a component generic point is the next universal clause:
  `∃ C ∈ irreducibleComponents T, IsGenericPoint t C`.
- Every component's generic point is over y is the following universal clause:
  for each `C ∈ irreducibleComponents T`, there is `t : T` with
  `IsGenericPoint t C` and `(strictHenselizationStructuralMap barZ ≫
  reducedLocalClosureMap X y w) t = y`. Mathlib's scheme sobriety and T0 property
  ensure the uniqueness implicit in “its generic point”.
- The final `↔` compares an ambient strict-local point over y whose singleton closure
  has `topologicalKrullDim = 1` with a component `C` of T with
  `topologicalKrullDim C = 1`. Dimensions are those of the subspace types. No clause
  asserts that such a C is an irreducible component of the ambient strict localization.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`; these are the recorded scheme and affine-spectrum interfaces.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`; ring
  Noetherianity is the recorded `IsNoetherianRing` in `Mathlib.RingTheory.Noetherian.Defs`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; and
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.SpecToEquivOfField`. The latter confirms that
  the geometric-point morphisms retain the residue-field embeddings.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, with the actual
  `IdealSheafData.vanishingIdeal`, `.subscheme`, and `.subschemeι` constructors.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`,
  `Scheme.strictHenselizationScheme`, `Scheme.strictHenselization_properties`;
  `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`;
  `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`:
  `Scheme.strictHenselizationMap`, `.strictHenselizationMap_existsUnique`,
  `.strictHenselizationMap_over`, the canonical interface for the recorded
  `Sheaf.Paper.StrictHenselizationFunctoriality` theorem.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.pullback.fst`, `.pullback.snd`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Mathlib.Topology.Sober`: `IsGenericPoint`;
  `Mathlib.Topology.Irreducible`: `irreducibleComponents`. These are exactly the
  recorded definitions, not private copies.

The stated proof dependencies are imported: the closed-immersion cartesian comparison,
`affine_strict_local_ring_comparison`, `fromSpecStalk_local_properties`,
`strictHenselization_structural_ringHom_flat`, `StrictHenselizationPresentationIn`,
`Algebra.HasGoingDown.of_flat`, and Mathlib's scheme-fibre, affine-stalk, component-cover,
and scheme-sobriety interfaces (the last three are available through the imports).
`lem-per-strict-localization-discrete-fibres` presently has no Lean record or Mathlib
match and therefore no module to import; it is a proof-only dependency and is named
in the theorem's proof docstring. It is not assumed as an extra hypothesis.

Edge cases checked before writing:

- x = y: W localized at its generic point is a field. The strict localization is
  zero-dimensional; both sides of the dimension-one criterion are false. All preceding
  point/fibre and component clauses remain valid.
- X empty: the point binders cannot be inhabited; no global Nonempty X assumption
  was added. No unintroduced generic point is chosen for an empty scheme.
- A line inside a surface: the reduced local closure is a curve and gives a
  one-dimensional component even though the ambient strict localization has dimension
  two. This verifies that the theorem does not accidentally assert ambient maximality.
- A nodal integral curve at the node: strict localization may have multiple branches;
  all their generic points lie over y. The theorem never assumes irreducibility of T
  or uniqueness of the fibre over y.
- An integral local surface: its strict-local components have dimension two in the
  usual regular example, and both sides of the dimension-one criterion are false.
- Nilpotents of X are allowed and removed only in W via the actual vanishing ideal.
  Reducibility and arbitrary characteristic of X are allowed. The one common universe
  u is the recorded strict-local API's convention, and may be enlarged to contain both
  the scheme and the geometric field; there is no independent smaller test universe.

Searches made before writing (all via the prescribed Q11/item search wrapper unless
specified as direct rg):

- LeanFinder: “Strict localization of a reduced local closure identifies generic fibre
  points with generic points of irreducible components”. Eight results included
  `IsAffineOpen.primeIdealOf_genericPoint`, `genericPoint_eq_of_isOpenImmersion`,
  `genericPoints.component_ofComponent`, `Scheme.range_fromSpecStalk`,
  `genericPoints.ofComponent`, `StructureSheaf.localizationToStalk_stalkSpecializes_apply`,
  `genericPoints.isGenericPoint_ofComponent`, and `Scheme.germToFunctionField`.
  None states this strict-local reduced-closure comparison or component criterion.
- Loogle: `strictHenselization, irreducibleComponents`. Zero hits; the service reported
  unknown identifier strictHenselization. This was not treated as evidence of absence
  without the other searches.
- Mathlib grep: `strictHensel|strict.*local.*component`, subdirectory AlgebraicGeometry.
  Zero hits.
- LeanSearch: “Strict localization commutes with the reduced local closure and gives
  the irreducible component criterion”. Eight hits: `isReduced_localizationPreserves`,
  `irreducibleComponent_mem_irreducibleComponents`,
  `PrimeSpectrum.vanishingIdeal_mem_minimalPrimes`, `isClosed_irreducibleComponent`,
  `isReduced_ofLocalizationMaximal`, `IsLocalization.Away.integralClosure`,
  `PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents`, `IsIrreducible.closure`.
  None states the node.
- Direct rg of the upstream WeilConjectures and shared lean/Sheaf trees for the item id,
  `strict.*local.*component`, and `reducedLocalClosure`: only unrelated component and
  prose occurrences; no existing theorem or local-closure construction. The canonical
  strict-localization and closed-subscheme sources were then opened and reused.

Validation: prescribed `scompile.py` compiled this delivered file cleanly in both its
sandbox and library contexts (2.1 s and 2.0 s). All universes and variables are explicitly
bound; no warning was emitted. All theorem proofs remain sorry; all definitions have
real data. The only node field changed is lean. No new or dependency node is delivered.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
