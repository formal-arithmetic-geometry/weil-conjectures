## Worker report

Repair of immutable head 2e6c6ef0fcde, stage-2 check (c): the returned packet
was reported to declare AlgebraicGeometry.Scheme.cbcCompletedCoefficientIso in
both IntegralCompactSupportUniformRestriction and ProEtaleProjectionCompactification.

The repair removes ProEtaleProjectionCompactification.lean from the delivery.
The now-published Sheaf.Paper.ProjectionCompactification is imported and reused
for proEtaleRingOpenExtension, proEtaleRingDerivedOpenExtension and
proEtaleRingCompactSupportImage. The dependency node's lean record points to
that published declaration with existing: true and no file. This also avoids
redeclaring the published extension and compact-support functors. The canonical
completed-coefficient comparison is defined once, in the item's own module;
its owning lean.declarations lists it there and nowhere else in the packet.
The construction is unchanged: conjugate the published fourCornerCoefficientIso
by pbcCompletedComparison, rather than choosing arbitrary coefficient maps.

The main theorem signature, all mathematical node statements, all statement
dependencies, and every conclusion are unchanged. The convenience definition
cbcIntegralCompactSupport and its shift instance now explicitly take
[QuasiCompact f], already present in the main theorem. In its definition,
Compactification.quasiCompact_openImmersion supplies the published construction's
[QuasiCompact cp.i] from this existing hypothesis. This is actual proof data,
not an additional hypothesis on the main theorem. Empty and identity
compactifications satisfy the same implication. No universe equality, new node,
statement correction, or STATEMENT-DISPUTED issue is introduced.

The packet has three modules: IntegralUniformCoefficient,
UniformCompleteTriangulated and IntegralCompactSupportUniformRestriction;
and four existing-node records, including the published compactification record.
Definitions have real data and all postponed theorem proofs are sorry.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `l : ℕ` and `[Fact l.Prime]`. |
| Finite extension E of Q_ell | `E : Type (u + 1)`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. |
| Valuation ring, uniformizer, ideal | `Padic.coefficientExtensionIntegers l E`, `Padic.coefficientExtensionUniformizer l E`, and `pbcPadicCoefficientDatum l E`. Its ideal is the singleton span of this uniformizer. |
| Completed coefficient sheaf | `pbcAdicCompletion T (pbcPadicCoefficientDatum l E)`, the published actual limit of positive quotient sheaves. Its quotient-diagram comparison is normalized on constant sections, not an identification with constant A. |
| Ambient D(Mod(A_T)) | `DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)))`, with the standard localization of actual completed-coefficient module sheaves. |
| X and Y are Noetherian schemes | `{X Y : Scheme.{u}}`, `[IsNoetherian X]`, `[IsNoetherian Y]`. |
| Finite Krull dimension | `_hXdim` and `_hYdim` are existential natural upper bounds for `topologicalKrullDim`, including the empty scheme. |
| ell invertible on both schemes | `_hXl : IsUnit (l : Γ(X, ⊤))`, `_hYl : IsUnit (l : Γ(Y, ⊤))`. |
| f separated and of finite type | `(f : X ⟶ Y)`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`. |
| Chosen compactification, pj=f, j open and p proper | `cp : Compactification f`, with `cp.i`, `cp.g`, `cp.Z`, `cp.comm`, and its open-immersion and properness fields. The quasi-compactness of `cp.i` follows from `[QuasiCompact f]` by the upstream compactification API; no non-quasi-compact case is admitted. |
| Exact compatible uniform category C_T | `IsPbcBoundedConstructibleComplete T l E` is an abbreviation for the published `PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)`. This is the conjunction of `PbcIsIntrinsicallyComplete`, `PbcHasUniformConstructibleReductions`, and `PbcHasCompatibleEtaleOrigins`; the category is the published full subcategory. |
| Common bounded adic-lisse finite-type local models | `IsUniformlyBoundedConstructibleAdicTower` uses one common interval and finite stratification and an `AdicTowerLocalModel` on covering members. The model and quotient-normalization compatibility are data, not a levelwise constructibility abbreviation. |
| Compatible etale-origin witnesses | Published `PbcHasCompatibleEtaleOrigins` asserts the existence of a `PbcWitnessedTower` and comparison isomorphisms to the actual derived reductions, with the canonical coefficient-reduction compatibility equation. Its iterated-composite convention gives the quotient cocycle, including equal indices. |
| Inherited triangulation | `pbcUniformComplete_isTriangulated` states isomorphism closure and `ObjectProperty.IsTriangulated` for this same predicate. Mathlib supplies its full-subcategory triangulation and exact inclusion. |
| A_Xbar restricted to X equals A_X | `cbcCompletedCoefficientIso cp.i ...`, induced by canonical finite-quotient inverse image and the constant-section-normalized diagram comparisons. The proper morphism uses the same canonical identification. Neither identification is an arbitrary parameter. |
| j_! is localized module extension by zero | `AlgebraicGeometry.Scheme.proEtaleRingDerivedOpenExtension` from `Sheaf.Paper.ProjectionCompactification` is degreewise exact extension; its ordinary functor is the representing left adjoint to ringed restriction. |
| Rp_* is completed-coefficient derived module direct image | `proEtaleRingDerivedDirectImage cp.g ...` is the existing K-injective right derived functor in the full coefficient-module category. It does not replace Rp_* by a completion or assume preservation. |
| Rf_!^c = Rp_*j_! | `cbcIntegralCompactSupport` unfolds to the published `proEtaleRingCompactSupportImage`, the composite of these two functors, in this order. |
| Lands in C_Y, including compatible witnesses | The first conjunct quantifies every ambient `K` with `IsPbcBoundedConstructibleComplete X l E K` and asserts that precise predicate for its image. |
| Functor restricts to the full subcategories | The ambient candidate already has identity and composition laws. The first conjunct restricts its object map; fullness restricts every ambient morphism without choices. No arbitrary restricted functor or unrelated natural isomorphism is substituted. |
| A-linearity | The second conjunct is preservation of addition for every morphism between selected objects. The third is preservation of multiplication by every actual `a : Padic.coefficientExtensionIntegers l E`. `pbcCompletedLinear` restricts the canonical global-section action along the unique compatible-residue ring homomorphism. Additivity implies zero preservation; hence these are exactly homomorphisms of A-modules. |
| Exactness | `cbcIntegralCompactSupport_commShift` is the canonical composite shift comparison. The fourth conjunct maps every ambient distinguished triangle whose three vertices lie in C_X to an ambient distinguished triangle. The first conjunct puts its three output vertices in C_Y, so this is precisely exactness for the inherited triangulations. |

The inherited triangulation is stated by pbcUniformComplete_isTriangulated.
The main theorem retains the node's five-step proof docstring: compactification
geometry and common fibre bounds; extension of stratified models and origins by
zero; the common interval for canonical reductions; proper-image preservation;
and scalar and triangle preservation followed by restriction to full subcategories.
UniformCompleteTriangulated retains its eight-step proof docstring.

Dependency declarations used:

- Mathlib: Scheme, IsNoetherian, topologicalKrullDim, IsSeparated,
  LocallyOfFiniteType, QuasiCompact, IsOpenImmersion, IsProper; the full-subcategory
  triangulated API; CommShift and mapTriangle; linear module and derived categories.
- WeilConjectures.Compactification.Defs: AlgebraicGeometry.Compactification,
  its Z, i, g, comm, proper/open fields, quasiCompact_openImmersion and ofIsProper.
- Sheaf.Paper.BoundedConstructibleTower: AdicCoefficientDatum,
  pbcAdicCompletion and pbcCompletedComparison (the actual positive quotient limit
  and its constant-section-normalized comparison).
- Sheaf.Paper.ProperBaseChangeFourCorners: fourCornerCoefficientIso, the
  canonical completed coefficient inverse image. Its conjugation supplies the
  single cbcCompletedCoefficientIso definition in the main module.
- Sheaf.Paper.BoundedConstructibleComplete: PbcIsBoundedConstructibleComplete and
  PbcBoundedConstructibleComplete, including intrinsic completeness, common local
  models and compatible etale origins. IntegralUniformCoefficient abbreviates
  these exactly for pbcPadicCoefficientDatum.
- Sheaf.Paper.PbcRationalCategory: pbcCompletedScalarSections,
  pbcCompletedModulesLinear and pbcCompletedDerivedLinear; no duplicate scalars.
- Sheaf.Paper.ProjectionCompactification: proEtaleRingOpenExtension,
  proEtaleRingDerivedOpenExtension and proEtaleRingCompactSupportImage. Its full
  current server source was read through scompile.py --source; it defines exact
  open extension by its representing adjunction, then the composite with the
  existing proEtaleRingDerivedDirectImage on actual coefficient-module categories.
- Sheaf.Paper.IntegralUniformCoefficient: pbcPadicCoefficientDatum and
  IsPbcBoundedConstructibleComplete; Sheaf.Paper.UniformCompleteTriangulated:
  pbcUniformComplete_isTriangulated. The other statement/proof imports of the
  main and triangulation modules are retained from the independently read packet.

Edge cases reviewed: empty schemes and open complements; zero objects and maps;
identity and proper identity compactifications; disconnected schemes; finite
Krull dimension including bottom for the empty scheme; ell=2 and all allowed
residue characteristics; positive quotient exponents including the first,
equal quotient indices and their identity normalization; all integer shifts.
The new use of quasiCompact_openImmersion applies to every compactification of
the finite-type f, including these cases. Coefficients remain in Type (u+1)
and site objects/morphisms retain their respective universes.

Searches: the original worker and second-reader searches (preserved verbatim
in scratchpad/pre-collision-repair-report.md and searches.jsonl) used msearch
LeanFinder for compact support preserving compatible uniformly bounded
constructible complete reductions, Loogle for shriek/constructible and linear
triangulated functors, and Mathlib grep for shriek and adic/constructible
combinations. They found no exact statement of this theorem. Repair searches
used rg for cbcCompletedCoefficientIso in shared lean/Sheaf and upstream
WeilConjectures (no published declaration there), the stage2_delivery.py decls
reader on each packet module, and scompile.py --source on
IntegralCompactSupportUniformRestriction and ProEtaleProjectionCompactification
(both unpublished), then ProjectionCompactification (published exact compact
support construction, read in full and now reused). These are source/record
searches for the returned collision; no mathematical notion is introduced.
No search result is treated as a proof.

## Dependency modules

- def-weil-pbc-bounded-constructible-complete: IntegralUniformCoefficient reuses
  the published generic category unchanged and supplies the unlifted finite
  extension specialization at E : Type (u+1). The older convenience wrapper
  takes E : Type u and ULifts its integers. Published scalar maps and instances
  are imported rather than duplicated.
- lem-weil-pbc-uniform-complete-triangulated: UniformCompleteTriangulated states
  isomorphism closure and inherited triangulated closure for that exact published
  predicate specialized to the actual valuation ring.
- def-weil-pbc-projection-compactification: no dependency module remains.
  Its lean-only repair is an existing: true record for the published
  AlgebraicGeometry.Scheme.proEtaleRingCompactSupportImage from
  Sheaf.Paper.ProjectionCompactification. The published interface is usable with
  the quasi-compactness proof described above. The returned replacement module
  is removed, not renamed or retained with alternate duplicate declarations.

## Validation

All checks are performed through the prescribed scompile.py and deliver2.py
wrappers. The current compile log is scratchpad/collision-repair-compile.log;
the current no-push preflight log is scratchpad/collision-repair-dry-run.log.
The packet was checked with the project's declaration parser: no name is declared
in two delivered modules, each module has one owning node, the three declaration
signatures match their lean.statement records after whitespace normalization,
and every Lean line is at most 100 characters. The earlier second reading is
preserved in the scratchpad as history; a new independent second reader must
review this repaired packet before delivery. Nothing is pushed by this worker.

Fresh repair compilation completed successfully (scompile.py exit status 0):
all three delivered modules compiled under their actual library names, with no
errors or warnings. The wrapper’s default per-file limit was unchanged.

## Second reading by Q01

I reread the node statement, its dependency records, the source description at
`thm-cbc-finite-extension` (proof, sole paragraph), and the Stacks references
Tags 0GL0 and 095U cited there. The source argument is preservation of integral
constructibility under extension by zero followed by proper direct image, with a
uniform finite-level bound and the resulting exact linear functor.

The node's objects and hypotheses match the Lean as follows:

- A prime `ell` is `l : ℕ` with `[Fact l.Prime]`.
- The finite extension `E / ℚ_[l]` is `E : Type (u + 1)` with `Field E`,
  `Algebra ℚ_[l] E`, and `FiniteDimensional ℚ_[l] E`.
- The valuation ring, uniformizer, and ideal are the canonical
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`,
  and `Ideal.span` packaged by `pbcPadicCoefficientDatum`.
- The completed coefficient sheaf and ambient derived module category are
  `pbcAdicCompletion T (pbcPadicCoefficientDatum l E)` and
  `DerivedCategory (pbcModules T (...))`; these are the recorded completed
  coefficient/module constructions, with coefficient universe `u+1` and site
  universes retained.
- `X` and `Y` are `Scheme.{u}` with `[IsNoetherian X]` and `[IsNoetherian Y]`;
  the finite-dimensional hypotheses are the two existential bounds on
  `topologicalKrullDim`, and invertibility of `l` is the two global-section
  `IsUnit` hypotheses.
- The separated finite-type morphism is `(f : X ⟶ Y)` with
  `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and `[QuasiCompact f]`.
- The chosen compactification is `cp : Compactification f`; its `i`, `g`, `Z`,
  and commutativity/proper/open-immersion fields provide the displayed
  `X → Z → Y`. The candidate supplies `[QuasiCompact cp.i]` canonically from
  `[QuasiCompact f]`, exactly as required for the published construction.
- The category `C_T` is rendered by
  `IsPbcBoundedConstructibleComplete T l E`, the published predicate containing
  intrinsic completeness, one common bounded uniform constructible reduction
  interval/local models, and compatible etale-origin witnesses. Its inherited
  triangulation is the `pbcUniformComplete_isTriangulated` dependency.
- The coefficient identification on the open is the canonical
  `cbcCompletedCoefficientIso cp.i ...`; the proper-leg identification is the
  corresponding canonical `cbcCompletedCoefficientIso cp.g ...`.
- `j_!` and `Rp_*` are represented by the published
  `proEtaleRingDerivedOpenExtension` and `proEtaleRingDerivedDirectImage`, and
  `cbcIntegralCompactSupport` is their composite in the stated order.
- The conclusion's landing clause is the first conjunct, quantifying every
  ambient `K` satisfying the source category predicate and asserting that its
  image satisfies the same precise predicate on `Y`, including witnesses.
- The second and third conjuncts quantify all selected objects and morphisms and
  express preservation of addition and scalar multiplication by every actual
  coefficient-ring element. The fourth quantifies an ambient distinguished
  triangle with all three selected input vertices and asserts preservation under
  `mapTriangle`; with `cbcIntegralCompactSupport_commShift` and the inherited
  triangulations, this is the exactness clause. Together these conjuncts are the
  full-subcategory restriction of the stated exact `A`-linear functor.

No hypothesis is stronger than the node's separated finite-type assumption:
`LocallyOfFiniteType` plus `QuasiCompact` is the recorded Lean presentation of
finite type. No universe equality, extra Noetherian condition, or nonempty-index
assumption was introduced. The empty scheme and empty fibres are covered by the
WithBot dimension bounds; zero objects and zero morphisms satisfy all four
conjuncts; identity and proper identity compactifications are covered; `n = 0`
and equal reduction indices are allowed; and `l = 2` is allowed whenever the
stated invertibility hypotheses hold.

I searched the project and upstream source with `rg`, and ran LeanFinder,
Loogle, and LeanSearch queries for compact-support/constructible/adically
complete functors and extension-by-zero/proper direct image combinations. The
searches found no existing declaration of this theorem or of the canonical
completed comparison used here. The recorded dependency declarations were
opened, including the published projection-compactification construction; the
packet's single `cbcCompletedCoefficientIso` definition is the only one in the
three delivered modules. The sole citer, `thm-cbc-finite-extension`, uses this
node only as a proof dependency and remains valid (`holds: true`); no statement
correction was made.

No mismatch was found, so no Lean or node change was required in this second
reading. The three delivered modules compile cleanly with `scompile.py`, with
only the intended postponed theorem proofs reported as `sorry`.
