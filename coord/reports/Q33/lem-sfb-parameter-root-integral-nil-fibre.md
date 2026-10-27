## Worker report

The module `Sheaf.Paper.ParameterRootIntegralNilFibre` states the complete item
in five substantive theorems in namespace
`AlgebraicGeometry.ProEtale.ParameterRootNilFibre`:
`colimit_presentation`, `integral_nil_fibre`, `finiteStage_baseChange`,
`baseChange_naturality` and `profinite_naturality`. The primary declaration is
`integral_nil_fibre`; all declarations are listed in `lean.declarations`.
The other eight theorem declarations are well-definedness or structural-square
parts needed by the canonical quotient and pullback constructions. Every new
theorem has proof `sorry`, a source, the owning node id and a complete proof
in its docstring. Every definition has actual data. The elementary boundary constructions have now landed in
`Sheaf.Paper.ParameterRootBoundaryData`, retaining their public names.
`RootBoundaryComparison` imports that module and has relinquished ownership of
the moved declarations. This delivery uses the landed extraction. The
mathematical statement is unchanged.

The source is the item's extracted returned step 2, expanded by its ten proof
steps. The blueprint paragraph (3) was read; as the node itself records, the
commutative-algebra assertion is agent-extracted, not a theorem quoted verbatim
from that paragraph.

The finite algebra and root coordinates already exist: the module uses
`sncRootLevel`, `sncRootCoordinate` and `sncFullRootCoordinate` from the recorded
`def-sfb-snc-residual-chart-data`. It does not redeclare them. The fields of
`SNCParameterTower` also describe transitions and a colimit, but that structure
requires nonempty connected base and root spectra. No such package is assumed
here: the new transition and inclusion maps are actual polynomial quotient
lifts valid for arbitrary commutative rings, including zero rings. Their
well-definedness proofs have been separated as named theorem declarations.

Hypotheses and construction data, clause by clause:

- A prime p is `(p : ℕ)` with `(hp : p.Prime)` on each substantive theorem.
  `R : Type u`, `[CommRing R]`, `{r : ℕ}` and `t : Fin r → R` bind the arbitrary
  ring and finite tuple. There are no regularity, characteristic, henselian,
  invertibility, Noetherian or nontriviality hypotheses.
- Positive orders prime to p are the recorded `TameRootOrder p`, namely
  `{n : ℕ // 0 < n ∧ n.Coprime p}`. `sncRootLevel t n.val` is exactly the
  polynomial quotient by `X_i^n-C(t_i)`. Its named root is
  `sncRootCoordinate t n.val i`.
- `transition p t n m h` uses evaluation at the m-th roots raised to `m/n`,
  followed by the quotient lift. `stageInclusion p t n` sends its roots to
  `sncFullRootCoordinate p t n i`. Identity and composite transitions,
  cocone compatibility and unique factorization of every compatible family
  are precisely the clauses of `colimit_presentation`. The target algebra
  of a test family is `Type (max u v)`, so no smaller-universe vacuity occurs.
- The full algebra is the recorded `tameRootAlgebra p t`. Its presentation
  imposes all power equations and exactly the divisibility transition
  relations. `colimit_presentation` certifies that this existing presentation
  has the displayed colimit universal property; no second chosen algebra
  replaces it.
- `RootBoundary.tower p t` is T, `RootBoundary.stratumRing t` is R/(t_i),
  `RootBoundary.stratumScheme t` is S and `stratumInclusion t` is s. The
  recorded `boundary p t` is Spec of the actual evaluation `zeroRoots p t`
  setting all compatible roots to zero, so is i. Its source is the same
  parameter quotient, rather than a reduced substitute.
- `RootBoundary.test X P` is the existing `profiniteToProEtOf X` test object,
  hence the actual Spec LC(P,Z) fibre product over Spec Z. Its `.hom` is
  the test projection. `qP p t P` is pi_P followed by q. The library uses
  ULift Z for Spec Z in universe u, retaining all rings and profinite sets.
- `fibre p t P` is exactly `pullback (qP p t P) (stratumInclusion t)`.
  `testMap (boundary p t) P` is i_P and `(test (stratumScheme t) P).hom`
  is rho_P. `inclusion p t P` is their canonical pullback lift, namely a_P.

Conclusions and compatibilities, clause by clause:

- The first conjunct of `integral_nil_fibre` gives, for every admissible n,
  a `Module.Basis (Fin r → Fin n.val) R (sncRootLevel t n.val)` whose value
  at e is exactly `∏ i, sncRootCoordinate t n.val i ^ (e i).val`. Thus its
  exponents are precisely 0 through n-1, including empty tuples. The same
  conjunct states `Module.Free` and `Module.Finite` for this algebra.
- Its second conjunct quantifies every `P : Profinite.{u}` and asserts
  `IsIntegralHom (qP p t P)`. The proof docstring gives the finite clopen
  partition argument; it does not infer integrality from weak etaleness.
- The stated closed inclusion s is `IsClosedImmersion (stratumInclusion t)`.
  The two next properties are `IsClosedImmersion (inclusion p t P)` and
  `Surjective (inclusion p t P)`, giving the surjective closed immersion a_P.
- The coordinate-ring quotient is literally
  `((inclusion p t P).appTop).hom`, on actual scheme global sections.
  `Function.Surjective` states that this is a quotient homomorphism.
  `root p t P i n` pulls the existing full-tower root section through
  `B_P -> T[P] -> T`. `rootIdeal` is the ideal span of all these images,
  indexed by `Fin r × TameRootOrder p`. The equality of the quotient's
  `RingHom.ker` with `rootIdeal` says it kills exactly that ideal.
- `(∀ y, y ∈ rootIdeal p t P → IsNilpotent y)` is elementwise nilpotence.
  There is no common exponent or ideal-power assertion. In particular a
  nilpotent already in R/(t_i) is not silently killed by replacing this
  kernel with the whole nilradical.
- The last two equalities of `integral_nil_fibre` are exactly
  `a_P ≫ pullback.fst = i_P` and `a_P ≫ pullback.snd = rho_P`.
  No isomorphism of B_P with S[P] is asserted.
- `stageMap` applies f to polynomial coefficients and fixes finite roots.
  `finiteStage_baseChange` gives the cartesian square for every finite
  level, the root-value formula, compatibility with `stageInclusion`, and
  compatibility with every divisibility transition. Its root formula
  sends each displayed basis monomial to the corresponding basis monomial.
- `algebraMapOf` and `stratumMapOf` are polynomial and parameter quotient
  maps, not arbitrary maps assumed as input. `towerMap` and `stratumMap`
  are their actual Spec maps. `baseChange_naturality` quantifies arbitrary
  `R' : Type u`, `[CommRing R']` and `f : R →+* R'`, asserts their cartesian
  base-change squares, and states commutation with zero-root evaluation.
- That theorem also quantifies every continuous `v : P' ⟶ P` and gives
  the equality between `inclusion' ≫ fibreMap` and the profinite product
  map followed by `inclusion`. It states equality on every root global
  section and equality of the extended root ideals. Thus both the quotient
  and its generating ideal commute with ring and parameter changes together.
- `collapse X P Q` is a constructed map from `(X[P])[Q]` to `X[Q ⨯ P]`.
  It uses the canonical product comparison of the existing profinite
  functor into schemes over Spec Z, and the actual pullback lift.
  `profinite_naturality` asserts that collapse is an isomorphism for the
  full tower and stratum, with its tower-projection equation. Product
  symmetry identifies the label order Q times P with P times Q.
- Further testing a_P by Q is again a surjective closed immersion. Its
  coordinate kernel is exactly the extension of `rootIdeal` along the
  Q-test projection, and every element of that ideal is nilpotent. These
  are explicit additional clauses of `profinite_naturality`.
- For every arbitrary ring map f and every simultaneous continuous
  `w : Q ⨯ P' ⟶ P`, `familyTowerMap` and `familyFibreMap` are the actual
  collapse/product/pullback composites. The final clauses give commutation
  of a_P with those maps and equality of the pulled root ideals. These
  are equalities on whole schemes and coordinate rings, with no reduction
  to the points of Q, no continuity assumption omitted and no identity or
  composite parameter case excluded.

Dependency declarations used (their signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`:
  `AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.IsIntegralHom` and
  `AlgebraicGeometry.IsIntegralHom.SpecMap_iff`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `profiniteToProEtOf`, `profiniteToProEt`, `profiniteToScheme`, `toSpecZ`
  and `preservesFiniteLimits_profiniteToProEt` in `AlgebraicGeometry.ProEtale`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`:
  `MvPolynomial`, `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`.
- `Mathlib.Algebra.Algebra.Hom` and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`:
  `AlgHom`, `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`,
  `Ideal.Quotient.liftₐ`, `Ideal.quotientMap`.
- `Mathlib.CategoryTheory.Limits.HasLimits` and
  `.Shapes.Pullback.HasPullback`: `colimit`, `Cocone`, `IsColimit`,
  `pullback`, `pullback.lift`, `pullback.map`, `pullback.fst`, `pullback.snd`.
  The colimit universal property is expanded directly in `colimit_presentation`.
- `Mathlib.LinearAlgebra.FreeModule.Basic` and
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Basis`, `Module.Free`,
  `Module.Finite`.
- `Sheaf.Paper.StrictLocalKummerTameModule`:
  `TameRootOrder`, `tameRootRelations`, `tameRootAlgebra`.
- `Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts`:
  `sncRootLevel`, `sncRootCoordinate`, `sncFullRootCoordinate`.
- `Sheaf.Paper.ParameterRootBoundaryData`:
  `RootBoundary.tower`, `stratumRing`, `stratumScheme`, `stratumInclusion`,
  `zeroRoots`, `boundary`, `test`, `testMap`, `qP`, `test_boundary_square`.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`:
  `AlgebraicGeometry.Scheme.UniversalCover.profiniteProductMap`.
- The proof plan imports the recorded `MonicTensorPresentation.basis` and
  `presentationMap_surjective`, Mathlib's tensor/pushout maps and
  `pullbackSpecIso`, the filtered-colimit representatives API, and the
  finite-algebra-integrality API. The proof dependency
  `lem-sfb-root-tower-profinite-base-change` has no Lean declaration in the
  read node and supplies no statement object here; its import is omitted
  until stated. The new module supplies its own needed canonical coefficient
  maps as part of the present item's construction and states naturality
  directly; it makes no dependency wait.

Four already-landed definition nodes were added to `stmt_deps` because they
own the finite/full root coordinates and actual parameter maps:
`def-sfb-strict-local-kummer-tame-module`, `def-sfb-snc-residual-chart-data`,
`def-sfb-profinite-product-maps`. The landed node
`def-sfb-parameter-root-boundary-data` owns the relocated elementary boundary
maps separately from the downstream derived comparison. The original
nine statement dependencies are retained. No original dependency is removed.

Edge cases checked before the final statement:

- `r = 0`: `Fin 0 → Fin n.val` has one element. The empty product is 1,
  the parameter ideal and root ideal are zero, and no nonempty-coordinate
  hypothesis or connectedness package is used.
- `n = 1`: the stage has the singleton power basis and its root equals t_i.
  The divisibility exponent is positive for all admissible transitions.
- Zero R is allowed: the indexed zero free module supplies the basis;
  all spectra are empty and the coordinate map is the zero-ring quotient.
- Empty P or Q is allowed: locally constant integer functions give the
  zero ring and the whole test schemes are empty. No `Nonempty P`, point
  evaluation, or chosen finite partition with a nonempty part is required.
- A parameter that is a unit gives the empty stratum and empty fibre;
  the statements still concern the unique empty-to-empty closed immersion.
- R = Z/4 with t = 0 retains the base nilpotent 2 in the zero-root quotient;
  the kernel is only the root ideal. This checks the distinction from a
  nilradical quotient.
- R a field with t = 0 has root nilpotence orders increasing through all
  admissible n. Thus no uniform exponent can be substituted for the
  elementwise nilpotence conclusion. Nothing asserts B_P = S[P].
- Arbitrary nonflat ring maps, identity maps, continuous noninjective and
  nonsurjective parameter maps, and product maps are permitted in the
  same signatures. The universal property tests arbitrary larger algebras
  using `Type (max u v)`.

Searches for existing declarations:

- msearch leanfinder: "The compatible tower adjoining all prime to p roots
  of finitely many ring parameters is integral and its zero-root closed fibre
  has nil kernel". Eight hits, including `Algebra.ZariskisMainProperty.of_isIntegral`,
  `Algebra.zariskisMainProperty_iff`,
  `exists_integral_inj_algHom_of_quotient`; no complete matching assertion.
- msearch loogle: `MvPolynomial, Module.Basis, IsIntegralHom`.
  Zero hits, with unknown unqualified identifier `IsIntegralHom`; the
  qualified Mathlib declaration was then read in the source.
- msearch grep: `tameRootAlgebra|parameterRoot|nil.*fibre`.
  Zero Mathlib matches.
- msearch leansearch: "The compatible prime to p root algebra is integral
  over the base ring and setting all roots to zero on the closed parameter
  fibre has nil kernel". Eight hits, including `IsIntegral`, `integralClosure`,
  `AdjoinRoot.isIntegral_root` and algebraic/integral equivalences; none the item.
- Direct rg in `lean/WeilConjectures` for
  `tameRootAlgebra|parameterRoot|nil.*fibre`, and for the exact node id:
  no matching complete assertion. The nil-fibre text hits concern different
  generic-fibre and smooth-trait results.
- Direct rg in `lean/Sheaf` for the root names found the existing full-root,
  projection, zero-evaluation, finite-level coordinate and profinite-product
  interfaces listed above. The broader follow-up for `StageAlgebra`,
  `stageRelations`, `tameRoot.*[mM]ap`, and maps of `tameRootAlgebra` found
  no existing arbitrary-ring canonical transition/map implementation:
  the residual chart structure has specified maps as fields but requires
  connected spectra and is not assumed here. Existing finite root definitions
  and all coordinates are reused. The exact `ParameterRootNilFibre` namespace
  was absent from both library roots and the upstream-name index.

## Repair of return L and rebase on current main

The first required dry run on the retained packet failed under (c): the stale
`RootBoundaryComparison.lean` was a modified library file without a changed
owning node. Direct comparison and `scompile.py --source
Sheaf.Paper.RootBoundaryComparison` show that the maintainer has now landed the
requested extraction. The elementary module is byte-identical to the retained
repair; the comparison module differs only by ten obsolete blank lines, and
its current node already carries the corrected ownership record and additionally
cites the elementary node. The saved dependency-node copy would remove that
newly landed dependency.

Removed both already-landed modules and their redundant node copies from the
sandbox packet. This delivery now contains only the item module, its node and
this report. It reuses the landed elementary interface, without changing any
statement, mathematical clause, definition or theorem body. The old delivery
gate problem is superseded by the maintainer's landed extraction.

## New nodes

None in this delivery. The earlier proposed
`def-sfb-parameter-root-boundary-data` has landed and is used as a dependency.
Its twelve declarations have one owner, that node; the comparison node no
longer records them. `RootBoundary.testMap` is an actual pullback lift and
contains no reference to `RootCoordinateFace.testMap`.

## Dependency modules

None in this delivery. The required elementary extraction and lean-only repair
of the comparison owner have landed upstream. Current
`RootBoundaryComparison` publicly imports `ParameterRootBoundaryData` and
retains the derived comparison declarations. The item publicly imports the
elementary module and does not import the downstream comparison module.

## Self-check by Q33

Rechecked both return points against current main. The twelve elementary
RootBoundary declarations each have exactly one owning node,
`def-sfb-parameter-root-boundary-data`. The landed comparison module imports
the elementary module and no longer defines those names. Its node has removed
them from `lean.declarations`, with the explanatory `lean.note`. The elementary
`testMap` uses its own pullback lift, not the coordinate-face declaration.
The item imports the elementary module; its theorem statements are unchanged.

A comment-aware traversal of public and ordinary project imports reaches
9,602 modules from the elementary module and 9,654 from the item. Neither
closure contains `Sheaf.Paper.RootBoundaryComparison` or
`Sheaf.Paper.RootTowerCoordinateFace`. All traversed project sources resolve;
for the absent local lisse-extension source the traversal used the current
server source read by `scompile.py --source`.

The overlaid combined statement/proof dependency traversal reaches 4,130
prerequisites, never the item itself, and excludes the comparison node.
The item's changed fields are exactly `lean` and additions to `stmt_deps`.
Its primary signature matches `lean.statement` verbatim, all binders are
explicit under `autoImplicit false`, and every Lean line is at most 100
characters. The clause-by-clause rendering and edge-case checks above remain
valid; no mathematical correction or hypothesis change was needed.

## Validation

The prescribed `scompile.py Q33 lem-sfb-parameter-root-integral-nil-fibre`
passed for the sole delivered file, both sandbox and library checks (23.3 and
24.4 seconds), with no compiler diagnostic. The reduced packet then passed
`deliver2.py ... --no-push`: `OK (dry run): commit dd93b5768e9 passes the
preflight and compiles; nothing pushed`. The server preflight supplies the
authoritative delivery DAG check; no prohibited local `check_dag.py`,
`preflight_delivery.py` or `review_split.py` was run. No direct live-repository
edit or Git command was used.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
