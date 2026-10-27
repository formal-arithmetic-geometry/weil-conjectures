## Worker report

The module `Sheaf.AlgebraicGeometry.SfBaseChangeGeometryHypotheses` states
`AlgebraicGeometry.sf_baseChange_geometry_hypotheses`. It introduces no definitions.
Its only postponed proof is that theorem, with the seven-step DAG proof in its docstring.
The natural-language statement, proof and proof dependencies are unchanged. The existing,
landed node `def-weil-finite-field-fiber` is added to statement dependencies to reuse
`WeilConjectures.FiniteFieldDatum`, rather than duplicate its finite-field data.

Hypothesis-by-hypothesis correspondence:

- The given `k = algebraic closure of F_q`, in characteristic `p`, is
  `D : WeilConjectures.FiniteFieldDatum.{u}`. Its fields are the prime `D.p`, positive
  exponent `D.a`, `D.q = D.p ^ D.a`, finite field `D.k₀` with cardinality `D.q`,
  and fixed algebraic closure `D.k`. This is exactly the existing global datum.
  Its characteristic is necessarily `D.p`; no independent characteristic or
  algebraic-closedness hypothesis is added.
- The coefficient prime is `ell : ℕ`, `hell : ell.Prime`, `hellp : ell ≠ D.p`.
- The four corners are `X' X Y' Y : Scheme.{u}`. Their `Over (Spec (.of D.k))`
  instances give their k-scheme structures. For each structure morphism the three
  classes `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` state separated finite
  type, using the recorded finite-type convention (the latter two classes together).
- The four arrows are `g'`, `f'`, `f`, `g` with exactly the indicated sources and targets.
  Each has `IsOver (Spec (.of D.k))` and the same three scheme-morphism classes,
  rendering separated finite-type k-morphisms. No arrow is assumed proper.
- `sq : ChosenCartesianSquare g' f' f g` is the dependency's actual chosen Cartesian
  square: commutativity, isomorphism of X' with the pullback, and its two projection
  equations. There is no replacement by an arbitrary isomorphism or commutative square.

Clause-by-clause correspondence:

- In the first conjunct, `∀ T : Scheme.{u}, (T = X ∨ T = Y ∨ T = X' ∨ T = Y') → ...`
  restricts the conclusions exactly to the four corners, permitting coincident corners.
  `IsNoetherian T`, `CompactSpace T`, `QuasiSeparatedSpace T` state Noetherianity,
  quasi-compactness and quasi-separatedness of each corner. Finite dimension is
  `∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)`, which also permits bottom.
- `∀ t : T, IsUnit (ell : T.presheaf.stalk t)` states invertibility of ell on each
  corner. The local rings are the actual structure-sheaf stalks.
- The next four conjuncts are `QuasiCompact h ∧ QuasiSeparated h` for each of
  `f`, `g`, `g'`, `f'`, respectively. Although quasi-compactness is also part of the
  given finite-type condition, the node explicitly asks for this conclusion.
- `∃ e : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y), ...`
  gives one nonnegative bound before any geometric point is chosen. The geometric
  fibre is the actual scheme pullback `pullback f y`; its underlying topological
  type is written explicitly as `↑(pullback f y) : Type u` to disambiguate the
  pullback category. `topologicalKrullDim ... ≤ (e : WithBot ℕ∞)` is the bound.
  The second clause `IsEmpty ... → topologicalKrullDim ... = ⊥` explicitly retains
  the empty-fibre convention. Arbitrary algebraically closed field-valued points
  include the chosen algebraic closure of every residue field; dimension invariance
  under field extension makes this independent of the chosen geometric point over
  a given ordinary point, exactly as in the DAG's affine-cover argument.
- `IsProper f → IsProper f'` retains the conditional properness assertion.
- The last conjunct quantifies over exactly the four corners again and every
  `U : Scheme.{u}`, `h : U ⟶ T`, with `IsSeparated h`, `LocallyOfFiniteType h`,
  and `QuasiCompact h`. It concludes `∃ c : Compactification h, QuasiCompact c.i`.
  The dependency structure supplies `c.Z`, open immersion `c.i`, proper `c.g`, and
  `c.comm : h = c.i ≫ c.g`. The extra predicate explicitly supplies the required
  quasi-compactness of the open immersion. The current upstream definition has
  deliberately dropped that field (matching its blueprint_update), so a bare
  `Nonempty (Compactification h)` would omit a stated conclusion. The existing
  theorem `Compactification.quasiCompact_openImmersion` explains the equivalence
  for the finite-type morphisms here; no dependency replacement is needed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`, including its full structure and docstring.
- `def-weil-scheme-morphism-properties` and `def-weil-pbc-scheme-conventions` are
  recorded convention nodes, with no declaration to import. Their named notions
  are the existing Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `QuasiSeparated`,
  `IsSeparated`, `IsProper`, `Scheme`, and `Scheme.Over`/`Scheme.Hom.IsOver`.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`, defined as
  `Order.krullDim (IrreducibleCloseds T)` in `WithBot ℕ∞`.
- `WeilConjectures.Compactification.Defs`, `AlgebraicGeometry.Compactification`,
  and its existing open-factor quasi-compactness theorem, as described above.
- `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`, the full
  landed structure for the base field. The corresponding DAG statement and Lean
  record were read; its node is added as an existing statement dependency.

The stated proof-dependency modules are imported without `public`:
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
(`AlgebraicGeometry.exists_fibre_dimension_bound`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(`AlgebraicGeometry.exists_topologicalKrullDim_le`),
`WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers`
(`AlgebraicGeometry.exists_field_baseChange_affine_covers`),
`WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension`
(`AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension`),
`WeilConjectures.Mathlib.Topology.KrullDimension`
(`topologicalKrullDim_le_of_iSup_eq_top`), and
`WeilConjectures.Compactification.NagataCompactification`
(`AlgebraicGeometry.NagataCompactification`). The remaining proof dependencies are
Mathlib leaves supplied by the imported Noetherian, finite-type, separated,
quasi-compact, quasi-separated, proper, topology and scheme modules. There is no
missing proof-dependency module or additional postponed helper theorem.

Edge cases checked before writing:

- No nonemptiness assumption on any corner, on U, or on a fibre. Empty schemes
  have dimension bottom and satisfy the asserted finite bounds. When Y is empty,
  the geometric-point quantification is empty and e = 0 is allowed.
- A nonempty Y can have empty fibres; these are covered by the same uniform bound
  and by the explicit `IsEmpty` implication. Dimension zero is allowed.
- The theorem assumes ell prime and different from p; it does not exclude p = 2,
  ell = 2 when p differs, or characteristic-p finite fields of any positive degree.
- Corner equality and identity arrows are allowed. Properness of f is conditional,
  and compactification is asked even when h is not proper or U is empty.
- The universe `u` is explicit for all schemes, base fields and test geometric
  fields, matching the project's small-scheme convention. Residue fields and their
  algebraic closures lie in that universe. There is no independent smaller test
  universe that could make the geometric-point assertion vacuous. All variable
  binders are explicit and `autoImplicit` is false.

Searches for existing declarations:

- `msearch.py leanfinder`: "Separated finite type schemes over an algebraically
  closed field have finite dimension uniformly bounded geometric fibres and
  compactifications" returned eight finite/proper morphism facts, including
  `AlgebraicGeometry.IsFinite`, properness of finite morphisms and finite fibres.
  None states the joint assertion with all four corners, all geometric fibres,
  conditional properness and the compactification clause.
- `msearch.py loogle`: "AlgebraicGeometry.IsNoetherian,
  AlgebraicGeometry.FiniteType" found no declaration (FiniteType is not a bundled
  Mathlib class). The corrected query "AlgebraicGeometry.IsNoetherian,
  AlgebraicGeometry.LocallyOfFiniteType" returned zero hits. The node's recorded
  convention correctly uses LocallyOfFiniteType together with QuasiCompact.
- `msearch.py grep`: `geometric.*[Ff]ib.*[Dd]im|[Nn]agata|finiteType.*[Dd]imension`
  in Mathlib/AlgebraicGeometry returned zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id and geometric
  fibre-bound terminology found existing individual ingredients and
  `finiteType_noetherianCover_dimension_geometricFibres` in
  `Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound`. The latter requires an
  existing finite Noetherian affine cover and a dimension bound on its base; it
  gives geometry for a single source and preserves invertibility. It does not
  state this node's Cartesian-square or compactification assertions. Its full
  signature and docstring were read; it is not an exact existing match.
- `grep -rn 'lem-sf-bc-geometry-hypotheses' lean/WeilConjectures` found no match.
  Searches for `sf_baseChange_geometry_hypotheses` and the proposed module name in
  both library roots and `dag/lean_names_upstream.json` found no existing declaration.
- Searches for `FiniteFieldDatum` found the existing `FiniteFieldFiber` module and
  its owning node, which are reused instead of introducing another finite-field
  definition. Searches for invertibility found the existing local-ring `IsUnit`
  formulation in `FiniteTypeGeometryFibreBound` and other library modules.

No statement fault or STATEMENT-DISPUTED issue was found. The previous attempt's
reported live stage-1 split is now the reviewed seven-step proof plan; the live
node has no stage-2 Lean record. This delivery leaves that reviewed split intact.

Validation: `scompile.py Q77 lem-sf-bc-geometry-hypotheses` compiled the complete
module successfully in both sandbox and library-name modes on the live server
(2.0 s and 2.1 s respectively), with no errors or unexpected warnings. An initial
elaboration failure inferred the category of types for an unannotated pullback;
explicitly coercing the scheme pullback to `Type u` repaired it without changing
any mathematical hypothesis or conclusion.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
