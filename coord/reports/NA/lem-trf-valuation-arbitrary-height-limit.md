## Worker report

The module `Sheaf.TraceFormula.ValuationArbitraryHeightLimit` states
`valuation_arbitrary_height_limit`, with exactly one postponed theorem and no new definitions.
The natural-language node is unchanged; only its `lean` record is changed. The earlier sandbox
module and root-level JSON were retained. The delivery JSON is now in the required
`dag/nodes/sec-trace-formula/` directory, and this report supplies the previously missing report.

The source was checked in Temkin, *Stable modification of relative curves*, arXiv
0707.3953v3, Theorem 3.5.5, Step 5 (printed p. 24), and Corollary 2.1.3(i)-(ii)
(printed p. 8). The PDF was obtained from https://arxiv.org/pdf/0707.3953v3 into sandbox
scratch files `temkin.pdf` and `temkin.txt`. Step 5 misprints the union result's reference as
Lemma 2.1.1(ii), as the node already records. The finite-presentation descent and additional
properties are the eight explicit proof steps of the DAG node. No source correction is needed.

Hypothesis and conclusion correspondence:

- A separably closed field `K` is `(K : Type u) [Field K] [IsSepClosed K]`.
- The valuation subring with fraction field `K` is `(V : ValuationSubring K)`.
  Mathlib's bundle gives both `ValuationRing V` and the canonical `IsFractionRing V K`
  instance; the inclusion algebra is its standard subring algebra.
- A commutative `V`-algebra `A` is `(A : Type v) [CommRing A] [Algebra V A]`.
  Flatness is `[Module.Flat V A]`, and finite presentation is
  `[Algebra.FinitePresentation V A]`.
- Geometric reducedness of `A_K = A ⊗[V] K` is the `hgeom` hypothesis
  `Algebra.IsGeometricallyReduced K (A ⊗[V] K)`, specialized to
  `Algebra.TensorProduct.rightAlgebra (R := V) (A := A) (B := K)`.
  This is geometric reducedness over the fraction field, with scalars acting through
  the second tensor factor. Over a field the Mathlib condition is equivalent to
  reducedness after algebraic closure, hence to reducedness after every field extension.
- The subfield in the conclusion is `∃ (K₀ : Subfield K)`, and its separable closedness
  is `IsSepClosed K₀`. There is no equality requirement between `K₀` and `K`.
- Its valuation subring is `V₀ : ValuationSubring K₀`. Its fraction field is automatically
  `K₀`, by the same standard instance. The clause
  `∀ x : K₀, x ∈ V₀ ↔ (x : K) ∈ V` identifies it exactly with `V ∩ K₀`.
- Finite height is `ringKrullDim V₀ < ⊤`: `ringKrullDim` is the supremum of lengths
  of strict finite prime-ideal chains. For a valuation domain this is its valuation height.
  This replaces the earlier draft's `Finite (PrimeSpectrum V₀)` by the direct height notion.
- The inclusion is an existential ring homomorphism `iV : V₀ →+* V`, with
  `∀ x : V₀, ((iV x : V) : K) = ((x : K₀) : K)`. Together with the intersection
  clause, this forces the actual inclusion; it is not an unconstrained map.
- Locality is `IsLocalHom iV` and faithful flatness is `RingHom.FaithfullyFlat iV`.
  The rings are local by their valuation-ring instances; no extra local-ring hypothesis
  is introduced. Flatness of the inclusion is included in faithful flatness.
- The descended algebra is `∃ (A₀ : Type (max u v)) (_ : CommRing A₀)
  (_ : Algebra V₀ A₀)`. Its flatness and finite presentation are respectively
  `Module.Flat V₀ A₀` and `Algebra.FinitePresentation V₀ A₀`.
  The universe `max u v` accommodates the finite polynomial quotient over `V₀` and
  imposes no equality on the independently quantified input universes `u` and `v`.
- Geometric reducedness of its generic fibre is
  `Algebra.IsGeometricallyReduced K₀ (A₀ ⊗[V₀] K₀)`, with the second-factor
  `K₀`-algebra structure explicitly supplied by `rightAlgebra`.
- The required `V`-algebra isomorphism is `Nonempty (A₀ ⊗[V₀] V ≃ₐ[V] A)`.
  The `V₀`-algebra structure on `V` is explicitly `iV.toAlgebra`, and the `V`-algebra
  structure on the tensor product is explicitly `rightAlgebra`. Thus base change
  uses the inclusion specified earlier, not another algebra structure.

The specializations of `@_root_.id (∀ [Algebra ...], Prop)` merely apply a predicate to
its explicitly specified instance. They introduce no hypothesis or choice. They replace
all of the previous draft's `letI` statements, preserving reducibility for future consumers.
Every variable and universe is explicitly bound, with both `autoImplicit` and
`relaxedAutoImplicit` disabled. The sole proof is `by sorry`.

Dependency declarations read and used:

- `def-kun-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed`
  (the record lists it alongside `IsSepClosure`). The complete class signature and
  its docstring were read. No replacement definition was made.
- `def-trf-valuation-ring`: `Mathlib.RingTheory.Valuation.ValuationRing`,
  `ValuationRing` and `ValuationRing.TFAE`; the latter identifies the fraction-field
  alternative with Mathlib's divisibility definition. `ValuationSubring` in
  `Mathlib.RingTheory.Valuation.ValuationSubring` bundles the given subring, and
  provides its `ValuationRing`, `IsLocalRing`, and `IsFractionRing` instances.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`,
  and `Mathlib.RingTheory.Flat.Basic`, `Module.Flat`. This statement uses the module
  declaration recorded by that node for an already specified algebra structure.
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation`, whose finite-polynomial-surjection and finitely
  generated kernel formulation is exactly the node's finite presentation.

The statement imports those Mathlib interfaces publicly. It also publicly imports the
Mathlib geometric-reducedness and faithfully-flat-ring-map interfaces used in the signature.
The eight proof steps in its docstring retain the node's full route and name each dependency.
Proof-only imports supply `separableClosure` through the already public IsSepClosed module,
`Sheaf.TraceFormula.AbhyankarFiniteTypeFieldHeight` /
`abhyankar_finite_type_field_height`,
`Sheaf.RingTheory.ValuationAlgebraicHeight` /
`ValuationSubring.primeSpectrum_comap_orderIso_of_isAlgebraic`,
`Mathlib.RingTheory.Flat.TorsionFree` /
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` /
`Module.FaithfullyFlat.of_flat_of_isLocalHom`,
`Mathlib.RingTheory.Extension.Presentation.Basic` / `Algebra.Presentation.baseChange`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` / `Module.Flat.iff_flat_tensorProduct`,
and `Sheaf.AlgebraicGeometry.GeometricallyReducedFibreLocus` /
`AlgebraicGeometry.geometricallyReduced_fibre_locus_constructible_baseChange`.
The three delivered-project proof modules were opened and their docstrings and complete
signatures checked. The proof modules' equal-universe specializations do not constrain this
statement; stage 3 can use common-universe lifts when applying them.

Edge cases checked before completing the statement:

- The zero algebra is allowed: no `Nontrivial A` or `Nontrivial A₀` assumption occurs.
  The zero algebra over the descended valuation ring has a finite presentation, is flat,
  and has reduced empty generic spectrum.
- Height zero is allowed by `ringKrullDim V₀ < ⊤`; no positive-height condition occurs.
  In particular, the trivial valuation `V = K` is included.
- Empty coefficient sets and zero-variable polynomial presentations are included by the
  finite-presentation class. The coefficient-field argument starts from the prime field.
- The characteristic is unrestricted. Separably closed fields need not be perfect, and
  `IsSepClosed` does not impose algebraic closedness.
- `K₀ = K` is allowed, but never required. Both ring maps and both scalar structures in
  the conclusion identify the correct canonical inclusions.
- The input universes are independent; the output algebra has the available common universe.

Searches repeated in this attempt through `msearch.py`:

- LeanFinder: "A flat finitely presented algebra over a valuation ring in a separably
  closed field descends to a separably closed subfield with valuation ring of finite height".
  Eight results, including `IsSepClosed.lift`, `IsSepClosed.lift_def`, formal smoothness
  facts, `Tilt.instField`, and `Valuation.HasExtension.instAlgebra_valuationSubring`.
  None asserts finite-height descent of the input algebra.
- Loogle: `"ValuationSubring", "FinitePresentation"`. Zero results.
- LeanSearch: "Finite height approximation of valuation algebras over separably closed
  fields". Eight results involving finite-field valuations, Dedekind-domain height-one
  valuations, `ValuationRing.valuation`, and `Field.finInsepDegree`; none matches.
- Mathlib grep via `msearch.py`: `finite.height|finite.rank|FinitePresentation` in
  `RingTheory/Valuation`. Zero results.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf`: `valuation_arbitrary_height_limit|valuation.*finite.*height.*limit|
  arbitrary.height.*limit`. No existing declaration found. Broader `finite.height`
  searches in the trace-formula/ring-theory modules found other valuation arguments,
  not this assertion. `grep -rn` for the blueprint item id in upstream sources also
  returned no match.
- Direct Mathlib source searches/readings located `ValuationSubring.comap`, the
  valuation-subring fraction-field instances, `ringKrullDim`, and
  `Algebra.TensorProduct.rightAlgebra`; all existing notions are reused.

Validation: the repaired module passed `scompile.py NA
lem-trf-valuation-arbitrary-height-limit <module path>` in both sandbox and library
contexts, with no errors or unexpected warnings. No new nodes, dependency repairs,
statement corrections, disputed claims, or tool workarounds are included.

## Second reading by NA

A second pass by this worker checked the current DAG statement against the repaired file;
this is a self-check, not a claim of an independent reader. The dispatcher brief forbids
starting other agents; the maintainer supplies the independent review.

The original draft's four local-instance `letI` expressions were replaced by explicit
predicate specializations. In particular the concluding tensor product is now checked
with `iV.toAlgebra` and second-factor `rightAlgebra` simultaneously. The intersection
membership clause and equality in `K` force `iV` to be the actual inclusion. Both geometric
reducedness conditions use the proper fraction field and second-factor scalars.
The earlier type `Subring K₀` plus separate valuation/fraction-field propositions was
replaced by the existing `ValuationSubring K₀` bundle; the automatic fraction-field
instance has its signature in Mathlib and adds no hypothesis. The height condition now
uses Krull dimension directly. The descended algebra uses `Type (max u v)` to accommodate
its coefficient ring without an unsupported size restriction. The proof docstring's
incorrect phrase that `W` is "of finite type" was corrected: it is the coefficient
*field* that is finitely generated; Abhyankar gives the height bound for its valuation
ring. The missing proof imports, source header, required node path and report were added.

Every natural-language hypothesis and conclusion has the explicit counterpart listed
above. No positive-height, nonzero, Noetherian, perfectness, common-field, or arbitrary
scalar-structure assumption remains. The current node's non-Lean fields are retained
verbatim as parsed JSON. The single postponed theorem has the complete eight-step proof
plan and source in its docstring. Independent maintainer review remains external to this
worker delivery.
