## Worker report

The module `Sheaf.Algebra.Homology.FieldComplexCohomologySplitting` states
`DerivedCategory.field_complex_cohomology_splitting`, with one `sorry` and no new
definitions. The original statement and dependencies are unchanged. Its docstring
records all ten DAG proof steps, including the explicit contraction, localization
argument, and arbitrary-splitting calculation. There are no disputed statements,
new nodes, or dependency repairs.

The signature renders each hypothesis and clause as follows.

- `F : Type u` and `[Field F]` give the arbitrary field. Vector spaces are
  `ModuleCat.{u} F`, complexes are Mathlib's integer-indexed `CochainComplex`, and
  `DerivedCategory (ModuleCat.{u} F)` is the recorded derived category. The imported
  `PointFdComplexes` module supplies the project's chosen derived category size;
  no additional localization, dimension, or boundedness hypothesis is imposed.
- Mathlib's `Homotopy` and `HomotopyEquiv` implement the node's definitions of
  homotopy and homotopy equivalence. In cochain degree n the homotopy equation is
  the sum of the composites through degrees n-1 and n+1. The structure contains
  both maps and both homotopies to the respective identities.
- The first conjunction quantifies over every complex P, without boundedness or
  dimension restrictions. `LinearMap.range (P.d (n - 1) n).hom` is B^n and
  `LinearMap.ker (P.d n (n + 1)).hom` is Z^n. The existential V,T clause explicitly
  states the availability of complements. `Disjoint B (V n)` and `B ⊔ V n = Z`
  say Z=B⊕V; `IsCompl Z (T n)` says P^n=Z⊕T. A second clause quantifies over
  every such choice, so the result is not restricted to one arbitrary splitting.
- For those complements the literal complex
  `{ X := fun n ↦ P.homology n, d := fun _ _ ↦ 0 }` is H(P). The existential
  `E : HomotopyEquiv H(P) P` states the required equivalence. Its forward map
  has image V^n, its backward map has kernel B^n⊕T^n, and
  `E.inv.f n (P.iCycles n x) = P.homologyπ n x` makes its restriction to cycles
  the actual cohomology quotient. These identify the maps supplied by the chosen
  complements rather than an unrelated equivalence with the same endpoints.
- The second conjunction quantifies over every chain map f and assumes only
  `QuasiIso f`. It supplies `E : HomotopyEquiv P Q` with `E.hom = f`, so f itself,
  rather than some alternative map, is a homotopy equivalence.
- The third conjunction is `Function.Bijective` for the function sending a derived
  map f to `fun n ↦ (homologyFunctor (ModuleCat F) n).map f`. Its inferred target
  is exactly the product over all integers of the F-linear Hom sets. This is the
  canonical cohomology map, not a bare existence of an abstract Hom equivalence.
- The fourth conjunction assumes precisely `pointFiniteDimensional F P`.
  It supplies a model H with every differential zero, each term isomorphic to
  H^n(P), `H.IsStrictlyGE a`, `H.IsStrictlyLE b`, termwise `FiniteDimensional`,
  and `Nonempty (P ≅ Q.obj H)`. These are the bounded finite-dimensional
  zero-differential model and its representing isomorphism. Its additional
  conclusion is the recorded `IsPerfectRingComplex P`, not a substitute predicate.
- The fifth conjunction assumes the same finite-dimensional bounded-cohomology
  condition and `e ≫ e = e`. The complexes S,N have zero differentials and terms
  isomorphic respectively to `LinearMap.range` and `LinearMap.ker` of H^n(e).
  Using isomorphisms of terms expresses representation of those vector spaces
  without making arbitrary choices of equality between bundled modules.
- The maps i,r satisfy `i ≫ r = 𝟙 (Q.obj S)` and `r ≫ i = e`; category composition
  is left to right, so these are exactly ri=1 and ir=e. Likewise j,s split 1-e.
  The isomorphism α from P to `Q.obj S ⊞ Q.obj N` has forward map
  `biprod.lift r s` and inverse `biprod.desc i j`. Thus the displayed models and
  maps give the specified complementary decomposition of P.
- For every v satisfying `v ≫ e = e ≫ v`, the block identity is
  `α.inv ≫ (e ≫ v) ≫ α.hom = biprod.map (i ≫ v ≫ r) 0`.
  This is exactly ve acting as rvi and zero on the two summands. Since e and v
  commute, either order of their product gives the node's ve.
- The final universally quantified clause covers arbitrary S,S' in D(F) and
  arbitrary splitting maps of e, not only the preceding chosen models. The two
  equations say that `i ≫ r'` (the node's r'i) and `i' ≫ r` (ri') are inverse.
  The last equation is `(r'i)(rvi)=(r'vi')(r'i)`, translated to left-to-right
  category composition. The same commuting v hypothesis remains in force.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q`, in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-derived-category-cohomology-functor`: its `mathlib_match` is
  `DerivedCategory.homologyFunctor`, in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. Read its full
  signature and the adjoining `homologyFunctorFactors` declaration. The raw
  complex cohomology is Mathlib's `HomologicalComplex.homology`, whose module
  interpretation is the cycles quotient (ShortComplex.ModuleCat).
- `def-weil-point-fd-complexes`: `DerivedCategory.pointFiniteDimensional`, in
  `Sheaf.Paper.PointFdComplexes`; read the whole definition, which uses finite
  cohomological support and termwise finite dimension inside this same D(F).
- `def-pc-perfect-ring-complex`: `DerivedCategory.IsPerfectRingComplex`, in
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`; read the
  whole existential bounded finite projective model definition.

The stated proof dependencies are imported using the recorded Mathlib modules:
`Module.Projective.of_free`, `Module.Projective`, `Module.Free.of_divisionRing`,
`FiniteDimensional`, and `Module.Finite`. The four statement-dependency modules
are public imports. There are no missing proof dependency interfaces.

Edge cases: P=0; acyclic unbounded complexes; arbitrary infinite-dimensional
terms and cohomology in the first three clauses; negative degrees; empty finite
cohomology support; a single nonzero degree; e=0 and e=1; v=0; identity and
noncanonical splittings. Nothing requires a≤b, nonzero cohomology, positive degree,
a nonzero image or kernel, or finite-dimensional terms of the original complex.
For e=0 the S model is zero and N models P; for e=1 the roles reverse. For
arbitrary alternative splittings the final equations retain their usual meaning.
All universes and variables are explicit; no independent small index universe is
introduced. The finite-dimensional predicate uses exactly its published universe.

Searches for existing statements (2026-10-17):

- `msearch.py ... leanfinder "Every complex of vector spaces is homotopy equivalent
  to its zero differential cohomology complex and cohomology is fully faithful on
  the derived category"`: eight hits, including `DerivedCategory.instFullSingleFunctor`,
  K-injective/K-projective `Qh_map_bijective`, `DerivedCategory.Q`, and localization
  quasi-isomorphism results. None states the whole item or its complement/retract clauses.
- `msearch.py ... loogle "HomotopyEquiv, CochainComplex.of"`: zero hits.
- `msearch.py ... leansearch "A complex of vector spaces is homotopy equivalent to
  its cohomology with zero differentials"`: eight hits on cylinder, reflexive,
  coinductive and isomorphism-induced homotopy equivalences, and homotopy to zero;
  none supplies the asserted field-complex statement.
- `msearch.py ... grep "homotopyEquiv|[Ss]emisimple|[Zz]eroDifferential"
  Algebra/Homology/DerivedCategory`: thirteen hits, involving conditional
  K-injective/K-projective homotopy equivalence and derivability structures.
- Direct `rg` of `zeroDifferential|zero_differential|cohomologyComplex|
  cohomology.*[Ss]plit|field.*[Ss]plit|[Ss]plit.*field` in upstream WeilConjectures
  and project `lean/Sheaf`: inspected the upstream private
  `exists_quasiIso_of_zero_differential` in DerivedCategory/Perfect.lean,
  `DerivedCategory.isPerfect_iff`, and the project's
  `CochainComplex.exists_quasiIso_from_zeroDifferential` in ResidueCohomologySplit.
  The private theorem supplies only a quasi-isomorphism, and the last theorem
  assumes prescribed finite cohomology dimensions; neither states this item.
  TruncationCouple.cohomologyComplex is bounded-below single-degree truncation
  data, not this unbounded cohomology model. No new model definition was needed.
- The requested search for the exact node id in upstream WeilConjectures had no
  hits. A declaration-name search for `field_complex_cohomology_splitting` in
  upstream, Mathlib, the side library, and `dag/lean_names_upstream.json` had no
  hits, so the name is unused.

Validation: `scompile.py N4 lem-trf-field-complex-cohomology-splitting <module>`
compiled both sandbox and library views cleanly (8.4 s and 9.1 s). No warnings
were reported. Only the named theorem is postponed; there are no definitions with
postponed data. No repair note for this item was present.

## Second reading by N4

I reopened the node and the complete module and made a second clause-by-clause
reading against the correspondence above. This was a self-review, not a claim
that another worker reviewed it: the dispatcher explicitly forbids starting
other agents and assigns independent review to the maintainer after delivery.

Checked in particular the direction of every composite: E runs from H(P) to P;
i≫r is the identity on S; r≫i is e; α maps P to S⊞N; conjugation starts with
α.inv. Checked the final comparison maps have types S→S' and S'→S and the two
intertwining composites both have type S→S'. The final clause quantifies over
arbitrary splittings. The complement clause uses ambient submodules with sum
exactly the cycles, not a complement of boundaries in the whole term. The
normalization on cycles is the actual homology quotient. The Hom bijection is
the canonical functorial one. There were no mismatches requiring a statement
change or dependency repair. The maintainer's independent reading remains the
review step specified by the dispatcher.
