## Worker report

The module `Sheaf.AlgebraicGeometry.ComplementaryPureSubcurveComponents` states
`AlgebraicGeometry.complementary_pure_subcurve_components`. It contains one theorem,
with `sorry`, and no definitions or proved helpers. Source: Stacks Project,
`literature/stacks-project/curves.tex`, Tag 0E38,
`lemma-closed-subscheme-nodal-curve`, first proof paragraph, together with the
finite-component complement argument recorded in this node's six proof steps.
The local source was opened and read. No statement correction is needed.

Hypothesis and conclusion correspondence:

- `X Y Z : Scheme.{u}` gives the ambient scheme and both closed subschemes, in an
  explicitly bound arbitrary universe.
- `[IsReduced X]` renders reducedness of X.
- `[IsNoetherian X]` means locally Noetherian and quasi-compact: Mathlib's class
  extends exactly `IsLocallyNoetherian X` and `CompactSpace X`. Compactness uses
  finite subcovers and imposes no Hausdorff condition.
- `hX : X.IsPureDimension 1` says every irreducible component has topological
  Krull dimension one, with the component carrying the subspace topology.
- `iY : Y ⟶ X`, `[IsClosedImmersion iY]`, `[IsReduced Y]`, and
  `hY : Y.IsPureDimension 1` render exactly the reduced closed pure subcurve Y.
- `iZ : Z ⟶ X`, `[IsClosedImmersion iZ]`, `[IsReduced Z]`, and
  `hZ : Set.range iZ = closure (Set.range iY)ᶜ` render Z as the reduced induced
  closed subscheme on the specified closure. This uses an arbitrary presentation
  of that closed subscheme; the recorded reduced-induced uniqueness theorem
  identifies it uniquely over X with its canonical `vanishingIdeal` construction.
  These binders specify the Z already in the node, rather than additional
  geometric restrictions on X or Y.
- `(irreducibleComponents X).Finite` renders the finite component set.
- `∃ I : Set (Set X), I ⊆ irreducibleComponents X` selects a subset of it.
- `Set.range iY = ⋃₀ I` and
  `Set.range iZ = ⋃₀ (irreducibleComponents X \ I)` render the two reduced closed
  unions. Since the given immersions are closed and their sources reduced,
  equality of these supports identifies the reduced closed subschemes, by the
  dependency's uniqueness clause. There is no replacement of a scheme union by
  an unrelated scheme with the same topological space.
- `Z.IsPureDimension 1` is the component dimension assertion for Z.
- The final `∃ φ : Y ≅ (vanishingIdeal (Closeds.closure (Set.range iZ)ᶜ)).subscheme`
  with `φ.hom ≫ ...subschemeι = iY` identifies Y with the actual reduced induced
  double-complement closed subscheme, as a scheme over X. This is the categorical
  meaning of equality of closed subschemes with possibly different presentations.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`
  and `AlgebraicGeometry.IsNoetherian` (the latter is the exact conjunction of
  local Noetherianity and compactness). The module also supplies the proof
  dependency `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`.
- `Mathlib.Topology.Irreducible`, `irreducibleComponents`, the maximal
  irreducible subsets; also the recorded component-cover lemmas.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`, dimension in
  `WithBot ℕ∞` by chains of nonempty irreducible closed subsets.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, closed embedding and surjective stalk maps.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`;
  its full statement and docstring were read. Its canonical objects are Mathlib's
  `Scheme.IdealSheafData.vanishingIdeal`, `subscheme`, and `subschemeι`.
- `Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Scheme.IsPureDimension`.
  The existing landed node `def-weil-pure-dimension` was added to `stmt_deps` to
  use this definition rather than repeat it. Its declaration is exactly the
  all-components condition and explicitly allows the empty scheme.
- `Sheaf.Topology.IrreducibleOpenComplementDimension`,
  `irreducible_open_complement_dimension`, is imported only for the recorded
  proof plan. The other proof dependencies are supplied by the above imports.
  In particular the scheme-sobriety instances are in Properties.

Edge cases checked before writing:

- Empty X: both closed subcurves must be empty; the component set and I are empty,
  the dimension conditions are vacuous, and the double complement is empty.
- Empty Y with nonempty X: take I empty; Z is all of X with its reduced structure;
  its complement and the double-complement subscheme are empty.
- Y = X: take all components; Z is empty; its complementary closure is X,
  with the original reduced structure. No `Nonempty` hypothesis excludes this case.
- Two intersecting one-dimensional components and Y one component: the closure
  of the complement is the other component, including the intersection point.
  The statement uses complementary component sets, not disjoint point sets.
- A zero-dimensional closed point is excluded by hY, as required. Dropping
  reducedness would permit thickenings with the same support, so it is retained.
- No base field, finite type, connectedness, separatedness, or nodal assumption
  was added; the node deliberately states the general component argument.

Searches for existing declarations (all on 2026-10-17 UTC):

- `msearch.py ... leanfinder` with “A reduced pure one dimensional closed subscheme
  of a Noetherian pure one dimensional scheme is a union of irreducible components
  and its complementary closure is the remaining components” returned eight
  results, including scheme sobriety, `PrimeSpectrum.zeroLocus_minimalPrimes`,
  and finite components. None is the whole statement.
- `msearch.py ... leansearch` with “A pure one dimensional reduced closed subscheme
  is a union of irreducible components” returned eight results, including
  `irreducibleComponents`, finite closed irreducible decompositions, and finite
  components. No exact statement.
- `msearch.py ... loogle "irreducibleComponents, closure"` returned three results:
  `closure_sUnion_irreducibleComponents_sdiff_singleton`,
  `PrimeSpectrum.vanishingIdeal_mem_minimalPrimes`, and
  `AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents`.
  The first concerns the complement of all but one component; it does not identify
  arbitrary pure closed subcurves or assert the reduced-scheme conclusions.
- `msearch.py ... grep "subcurve|complementary.*component|pure.*dimension"
  AlgebraicGeometry` returned zero Mathlib hits.
- `rg -n "subcurve|complementary.*component|pure.*dimension"` on the source project's
  `WeilConjectures` and on `lean/Sheaf` found unrelated curve purity, boundary,
  and derived-category statements, plus the usable `PureDimension.lean` definition.
  No exact theorem. Targeted name searches for
  `complementary_pure_subcurve_components|ComplementaryPureSubcurveComponents`
  in the upstream name index and relevant Lean sources found no existing name.
- `grep -rn "lem-trf-complementary-pure-subcurve-components"` on upstream
  `WeilConjectures` found no declaration.

No new nodes, dependency modules, or disputed statements. The only node changes
are its `lean` record and the addition of the existing landed pure-dimension
node to `stmt_deps`. `lean.statement` is extracted verbatim from the theorem
keyword up to `:=`; the date is UTC.

Validation: `scompile.py Q119 lem-trf-complementary-pure-subcurve-components`
compiled the delivered file in both sandbox and library module contexts, cleanly,
with no errors or non-sorry warnings (1.6 seconds in each context).

## Second reading by Q119

A second clause-by-clause pass opened the node and the completed module together.
`IsNoetherian` was checked against its full class definition, and `IsPureDimension`
against its complete body, rather than inferred from names. The empty-scheme
condition is vacuous in that definition. The Z binders were checked against the
reduced-induced dependency's uniqueness clause: every permitted representation
is uniquely isomorphic over X to the canonical one. The two union equalities
concern precisely the selected components and the set difference from all
components, so intersection points of components are correctly retained.
The final isomorphism includes its commuting equation over X and uses the
canonical vanishing-ideal subscheme, not merely equality of abstract schemes.
No hypothesis or conclusion mismatch was found and no correction was made.
This pass was performed by the dispatcher worker; the maintainer supplies the
independent delivery review specified in the brief.
