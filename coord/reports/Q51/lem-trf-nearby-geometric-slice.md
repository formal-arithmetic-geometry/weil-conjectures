## Worker report

The delivery states `AlgebraicGeometry.OrientedNearbyCycles.nearby_geometric_slice`
in `Sheaf.Paper.NearbyGeometricSlice`. Every postponed proof is the whole `sorry`
proof of a public named theorem of this node. Definitions have actual data.
There is no change to the mathematical statement and no disputed statement.

Source read: Illusie, *Around the Thom--Sebastiani theorem*, author PDF,
https://www.imo.universite-paris-saclay.fr/~luc.illusie/Illusie-nearby-cycles28.pdf,
§1.3, especially (1.3.1)--(1.3.4), printed p. 7, and §1.4,
(1.4.1)--(1.4.3), printed p. 8. The source's full generic strict localization
and the node's geometric generic point are different objects; the node's proof
supplies the additional field-extension comparison. The delivered generic fibre
is the geometric fibre requested by the node, not the full strict-local tube.

Hypotheses, objects, and clauses matched with Lean:

- A DVR is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The Mathlib class extends the local and principal
  ideal ring conditions and excludes a field. The base is `Spec (.of R)`.
- A finite-type source morphism is `f : T ⟶ Spec (.of R)` with
  `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded definition.
- Coefficients are `(Λ : Type v) [CommRing Λ] [Finite Λ]`, with independent
  coefficient universe. The annihilator is `(m : ℕ)` with
  `hmΛ : ∀ a : Λ, m • a = 0` and `hmR : IsUnit (m : R)`.
  Writing an integer by its nonnegative absolute value loses no annihilator:
  sign affects neither annihilation nor invertibility. No positivity assumption
  is imposed; `m = 0` is ruled out by invertibility in the nonzero DVR itself.
- A bounded input is an object of `sliceBoundedInclusion T Λ`, the full
  subcategory of the already recorded derived category cut out by `IsBounded`.
  The same predicate appears explicitly on the ordinary and tensor inputs.
  The conclusion supplies a `NatIso` on this full subcategory, not just
  objectwise isomorphisms of cohomology groups.
- The geometric closed point is `b : Spec (.of Ω) ⟶ Spec (.of R)` with
  `[Field Ω] [IsAlgClosed Ω]` and
  `hb : b (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R`.
- Its strict localization is the dependency's
  `Scheme.strictHenselizationScheme b`, and its map to the base is
  `Scheme.strictHenselizationStructuralMap b`. No replacement ring is introduced.
- The chosen geometric generic point is
  `t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b`, with
  `[Field Ξ] [IsAlgClosed Ξ]` and
  `ht : IsGenericPoint (t (IsLocalRing.closedPoint Ξ)) Set.univ`.
  Its chosen map to the strict localization encodes the geometric specialization.
  There is no algebraicity restriction on either geometric field.
- `geometricSliceTube f b` is `T ×_B B_(b)`;
  `geometricSliceFibre f b` is `T ×_B Spec Ω`;
  `geometricSliceGeneric f b t` is the nested product
  `(T ×_B B_(b)) ×_(B_(b)) Spec Ξ`.
  `geometricSliceI` uses the recorded closed lift/evaluation,
  `geometricSliceJ` is the first projection of the latter product, and
  `geometricSliceR` is its composite to `T`.
- `GeometricNearbySliceData.morphism` is the requested `e_f`.
  Its `first` field identifies `p₁ e_f` with the geometric fibre map;
  its `second` field identifies `p₂ e_f` with `geometricSliceSecond`.
  That second leg is the actual constant GENERIC point, through the
  constant-sheaf/global-sections adjunction and the given generic stalk point.
  `specialization : IsGeometricNearbySlice ...` records the compatible lifts
  of every triple at every geometric point of the closed fibre. It includes
  naturality under every triple arrow. The equations use `t ≫ l` for the
  generic leg and the distinguished closed lift for the special leg.
- `geometricSliceModules` reuses `moduleMorphism` for constant coefficients;
  it does not introduce another module inverse-image functor.
- `geometricSliceClassical` is literally `r* ⋙ Rj* ⋙ i*`, using the dependency's
  exact inverse images and K-injective derived direct images.
- `GeometricSliceComparisonFamily` retains the comparison as a natural
  transformation of these functors. The theorem existentially supplies this
  family together with the normalized geometric morphisms. Its first conjunct
  supplies `η`, a natural isomorphism on bounded inputs, and identifies
  `η.hom` with the restriction of that transformation. No definition chooses
  an unconstrained map from an existence theorem.
- Arbitrary `B`-morphisms are parametrized by `(T' : Scheme.{u}) (h : T' ⟶ T)`;
  their structure morphism is `h ≫ f`. This is equivalent to specifying `f'`
  and the over-`B` equation and omits no source morphism. No finite-type,
  properness, flatness, or smoothness condition is imposed on `T'` or `h`.
- `geometricSliceFibreMap`, `geometricSliceTubeMap`, and
  `geometricSliceGenericMap` are the actual base changes of `h`.
  `geometricSliceMap_squares` gives their `i`, `j`, and restriction squares.
- `γ` identifies `v e_f'` and `e_f h_b`. BOTH projection equations in the
  ordinary conjunct fix its normalization. `geometricSliceSquare` then uses
  the existing generator-normalized `derivedSquare` to obtain its inverse
  image comparison. The source of the displayed square is
  `e_f'^* v^* RΨ_f L`, canonically identified with `h_b^* e_f^* RΨ_f L`;
  it is not an incorrectly typed pullback along `e_f` alone.
- The ordinary equation uses the dependency's literal `baseChange` on its
  right side. On its left side `geometricSliceOrdinary` is independently
  defined by the `i` pullback square, the transpose of the `j` counit, and
  the input-restriction square. The comparison on `h*L` is asserted invertible;
  the ordinary comparison itself has no `IsIso` assumption or conclusion.
- The final conjunct is the tensor square. Its first route uses the inverse
  of `pullTensor` for `e_f`, then `e_f^*(laxTensor f Λ L M)`, then the sliced
  comparison on `L ⊗ᴸ M`. Its second route tensors the two slice comparisons
  and applies `geometricSliceTensor`. The latter is independently constructed
  using `pullTensor` for `i` and `r` and `geometricSliceJLax`, the transpose of
  the tensor of the `j` counits. Neither lax tensor map is asserted invertible.
  There is no hypothesis that `L ⊗ᴸ M` is bounded: the transformation is
  retained on unbounded objects precisely so that this term is legitimate
  for finite coefficient rings with infinite Tor dimension.

Dependency declarations read and reused:

- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleSite`, `etaleTopology`,
  `etaleBaseChange`, `etaleMorphism`, `VanishingSite`, `vanishingTopology`,
  `VanishingTopos`, `p₁`, `p₂`, `squareLift`, `squareMorphism`, `squareDirect`,
  `moduleMorphism`, `etaleModules`, `squareModules`, `Coeff`, `EtaleDerived`,
  `nearbyCycles`, `IsBounded`, `derivedTensor`, `pullTensor`, and `laxTensor`.
  These use the existing K-injective and K-flat constructions and preserve
  the independent coefficient universe.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`;
  geometric points are the prescribed inline scheme maps from such fields.
  Read `Scheme.SpecToEquivOfField` and its docstring in
  `Mathlib.AlgebraicGeometry.ResidueField` to check the residue-field meaning.
- `Sheaf.AlgebraicGeometry.StrictHenselization`,
  `Scheme.strictHenselizationScheme`, and its recorded coordinate-ring
  colimit construction; structural and distinguished-point maps are reused
  through `StrictHenselizationClosedLift`, particularly
  `Scheme.strictHenselizationClosedLift_over`.
- Added the already landed `lem-trf-general-nearby-slice-test` to `stmt_deps`
  solely to reuse its `sliceStalk`, `sliceBoundedInclusion`, and
  `slicePullSquare`, rather than copy these definitions. Its statement and
  complete module were read. Its full strict-local formula is not used as
  the geometric-fibre formula.
- Added the already landed `lem-trf-oriented-product-points-conservative`
  to `stmt_deps` to reuse `geometricEtalePoint` and `punctualEquivalence`.
  The helper `geometricSliceBasePoint` is precisely transport of that recorded
  point to sets through the punctual-site equivalence; it does not rebuild
  its stalk or adjunction. Its statement and module
  were read, including the stalk/skyscraper point construction.
  Both added nodes were checked transitively against statement/proof edges:
  neither reaches this item, so these additions create no cycle.
- Every proof dependency with a recorded module is imported, either publicly
  through the statement dependencies or as an ordinary proof import.
  The mate dependency is Mathlib's `CategoryTheory.mateEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Mates`; the separable/purely-inseparable
  dependency is `separableClosure.isPurelyInseparable` in
  `Mathlib.FieldTheory.PurelyInseparable.Basic`. These are Mathlib matches,
  not missing interfaces. The module docstring and main theorem docstring
  carry all six proof steps and the node names supporting them.

Edge cases checked before stating:

- Empty `T`, empty special fibre, and empty `T'` are admitted. The morphisms
  and adjunction comparisons still exist; stalk normalization can be vacuous
  on a degenerate fibre without imposing any false nonemptiness hypothesis.
- The zero ring of coefficients is allowed (`CommRing`, not `Nontrivial`).
  For `m = 1` the annihilation hypothesis forces this case, which is harmless.
  For `m = 0` the unit condition fails on a DVR, as it should.
- Identity `h` and arbitrary non-finite-type `h` are both admitted.
  The identity direct-image comparison is normalized by the actual
  `pullback.fst` isomorphism, not an arbitrary identification with the identity.
- Both geometric points may have fields transcendental over their residue
  fields; no `Algebra.IsAlgebraic` assumption was introduced.
- Scheme and coefficient universes are independent. The common sheaf universe
  remains `max (u + 1) v`; the module coefficients remain the dependency's
  `Coeff.{u, v} Λ`. No equality of site/coefficient universes is imposed.
- Input complexes need not be constructible, perfect, connective, or of finite
  Tor dimension. In particular the tensor compatibility is well typed even
  when a tensor of two bounded complexes is unbounded below.

Searches made (all through the prescribed tools or read-only text searches):

- LeanFinder: “Restrict oriented nearby cycles to a geometric specialization
  of a trait as i star R j star”: 8 hits, all scheme stalk-specialization
  or topological skyscraper/stalk identities, no nearby-cycle slice formula.
  Returned signatures inspected.
- Loogle: `"nearby", "slice"`: zero hits.
- Mathlib grep: `nearby.*geometric|nearby.*slice|vanishing.*topos`: zero hits.
- LeanSearch: “Geometric generic specialization slice of oriented nearby
  cycles is naturally i pullback R j pushforward”: 8 hits, ordinary module
  pullback adjunctions, topological stalk pushforward, and a sieve lemma.
  None has the oriented topos or the geometric-slice compatibility statements.
- `rg` in `WeilConjectures` for the geometric/nearby/slice expressions and
  `grep -rn` for this node id: no matching existing statement.
- `rg` in `lean/Sheaf` found the existing general strict-local slice helpers,
  the oriented-point comparison, and unrelated finiteness/base-change nodes.
  Read those interfaces and reused the relevant general helpers. The general
  slice deliberately retains the generic strict localization and does not
  state this geometric generic-fibre result or its lax tensor compatibility.
- `rg` for `nearby_geometric_slice`, `geometricSlice`, and
  `GeometricNearbySlice` in the upstream source, side library, and
  `dag/lean_names_upstream.json`: no existing declarations with these names.

All new helpers belong to the geometric-slice notion of this node and are
listed in `lean.declarations`. They are not new independent DAG notions.
The helper theorems are only identities of its explicit fibre-product maps
or the naturality of its identity-base-change components; their docstrings
provide complete elementary proofs. No new nodes or dependency repairs.

Validation: file-only compilation is performed with the prescribed
`scompile.py Q51 lem-trf-nearby-geometric-slice` wrapper. The dry-run preflight
and final delivery are performed with `deliver2.py`, using the same file.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
