## Worker report

The module Sheaf.Paper.CompactSupportUniformTorBound states
AlgebraicGeometry.ProEtale.compactSupport_uniform_tor_bound with one sorry and no
new definitions. The source is the current main-20261015 blueprint,
sec-smooth-purity/sk-lem-sp-tower-bound/sk-lem-sp-tower-bound-uniform.md;
the expanded DAG statement and all seven proof steps were read. The declaration
docstring contains all seven steps, including the arbitrary test-module projection
formula, the bound on original rather than compactified fibres, and the levelwise
argument. No statement correction or new node is needed. A published generic system
interface required the dependency repair described below.

Hypothesis and clause correspondence:

* `p l : ℕ`, `Fact p.Prime`, `Fact l.Prime`, `k : Type u`, `Field k`,
  `CharP k p`, and `_hlp : l ≠ p` render the standing positive-characteristic
  field and the distinct prime ell. Primality implies p > 0.
* `X Y : Scheme.{u}` and their `Over (Spec (.of k))` instances render schemes
  over the same field. Each structure morphism has `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`: separated and finite type.
* `f : X ⟶ Y`, `f.IsOver (Spec (.of k))`, `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f` render exactly the specified
  separated finite-type k-morphism.
* `c : Compactification f` and `QuasiCompact c.i` specify the chosen proper/open
  factorization of def-weil-pbc-projection-compactification. The latter is the
  quasi-compactness explicitly required by that recorded functor; it is automatic
  in the standing setting (the source's first proof step uses the same fact).
  This parameter permits every such choice, including the chosen Nagata one.
* `d : ℕ` and `_hd` bound topologicalKrullDim of the pullback along the canonical
  algebraic-closure point over every y by `(d : WithBot ℕ∞)`. Testing these
  algebraic-closure geometric fibres is the usual dimension condition on all
  geometric fibres. The expression is exactly that of the recorded
  lem-dg-compact-support-amplitude, so it bounds f's fibres, never c.g's fibres.
* `a b : ℤ` and `_hab : a ≤ b` retain arbitrary ordered integer intervals.
* The first conjunct quantifies over every `A : Type u` with `CommRing A` and
  `Finite A`. `∃ r : ℕ, 0 < r ∧ (l : A)^r = 0` is precisely annihilation by
  a power of ell: multiplying 1 by this power is zero, hence it kills all A.
  No nonzero-ring assumption occurs. The discrete coefficient ring is represented
  by the existing `proEtaleConstantRing`, with the coefficient ULift supplied by
  its definition; no topology or additional coefficient structure is chosen.
* `M : proEtaleDerivedCategory X A` with `spFiniteConstructibleTor X A M`
  is finite-level Dctf, in the exact ringed coordinates already used by
  sk-def-sp-normalized-towers. This predicate means bounded cohomology,
  constructible cohomology sheaves, and finite Tor amplitude.
  `HasProEtaleTorAmplitude X A M a b` imposes the specified interval and tests
  EVERY module sheaf via K-flat representatives, not just constructible tests.
  For finite discrete coefficients on the qcqs schemes here this is the
  discrete presentation of det-def-sfb-constructible-tor-amplitude, using
  det-pe-finite-tor-comparison-noetherian to pass to etale origins.
* The output is exactly `proEtaleRingCompactSupportImage c` applied to M,
  using `proEtaleConstantRing` on X,c.Z,Y and the canonical
  `proEtaleConstantRingComparison` on c.i,c.g. This is the recorded Rp_* j_!,
  without an arbitrary coefficient identification, unrelated map, or replacement
  by the etale value. Its two asserted properties are
  `spFiniteConstructibleTor Y A` and `HasProEtaleTorAmplitude Y A _ a
  (b + 2 * (d : ℤ))`: Dctf membership and the exact asserted output interval.
* The second conjunct takes every finite-dimensional extension `E` of `Padic l`.
  `SpTowerShriek.R l E n` is literally O_E/(ell^(n+1)), covering every n>=1
  of the paper. `base : SpTowerShriek.Base l E` and
  `ops : SpTowerShriek.Operations l E base` are the already published,
  section-normalized realization/operation interfaces, not new hypotheses on
  the geometric morphism or tower. Existence is supplied by the imported
  `SpTowerShriek.tower_shriek_levels`. Quantifying over these implementations
  allows any of the recorded canonical realizations.
* `C : SpTowerShriek.D l E X` is the ordinary unbounded derived category of
  actual strict varying-coefficient systems. Base.realization is the sectionwise
  equivalence with the coefficient-tower category. It is not a diagram of
  derived objects. No normalization condition is imposed.
* The single input hypothesis `∀ n, spFiniteConstructibleTor ... ∧
  HasProEtaleTorAmplitude ... a b` is exactly levelwise Dctf and one common
  interval. `SpTowerShriek.Ev` is the recorded exact derived evaluation.
  These common bounds imply the input lies in D+, by levelwise cohomology;
  taking the ordinary unbounded object adds no assumption or input case.
* For every n the output evaluation of `SpTowerShriek.F l E base ops c`
  has Tor amplitude `a` to `b+2d`, and `∀ q, q<a ∨ b+2d<q → IsZero ...`
  explicitly states cohomology vanishing outside the same closed interval.
  F is the recorded compactification composite, whose Fcomparison identifies
  each output evaluation with finite compact support. This bound is independent
  of n, ramification, coefficients, and choice of etale antecedents.

Dependency declarations and source inspection:

* sk-def-sfb-dc-setting: WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.
  BoundedConstructible, CondensedRing.compactificationOverField and the explicit
  scheme-over-field binders; the exact side-framework source and
  coord/pefw-upstream-framework.md were read. Its current definition uses Over
  instances (the older recorded signature still uses Over objects).
* def-kun-topological-krull-dimension: Mathlib.Topology.KrullDimension,
  topologicalKrullDim, read with its IrreducibleCloseds definition and docstring.
* def-weil-pbc-derived-categories: WeilConjectures.AlgebraicGeometry.DerivedCategories,
  Etale.DerivedCategoryModule and DerivedCategory.homologyFunctor; its source
  describes the fixed-scalar etale category and cohomology convention.
* def-weil-pbc-proetale-modules: Sheaf.AlgebraicGeometry.ProEtaleFiniteModules,
  FiniteCoefficientModules, finiteCoefficientDerivedComparison, and
  isBoundedConstructibleFiniteCoefficient; the continuous-function ring and
  constant-scalar realization are imported, not reconstructed. For the conclusion
  the constant-ring module presentation is the one in the recorded tower and
  compactification interfaces.
* det-def-sfb-constructible-tor-amplitude: Sheaf.Paper.ConstantModelTorAmplitude,
  constantModelConstructibleFiniteTor_wellDefined, importing
  Sheaf.Paper.CondensedConstantConstructibility's four full-subcategory definitions;
  in discrete finite-level coordinates use the already recorded
  spFiniteConstructibleTor and HasProEtaleTorAmplitude, not a new predicate.
* det-pe-finite-tor-comparison-noetherian: Sheaf.AlgebraicGeometry.
  ProEtaleFiniteTorComparisonNoetherian, finiteTorComparisonNoetherian; its full
  signature retains the localization factorization, interval iff, and full
  finite-Tor equivalence. It supplies the etale-origin interpretation, not a
  replacement by an arbitrary abstract equivalence.
* def-weil-pbc-projection-compactification: Sheaf.Paper.ProjectionCompactification,
  Scheme.proEtaleRingCompactSupportImage, proEtaleRingDerivedOpenExtension;
  the signature and ordinary-adjoint characterization were read.
* sk-def-sp-normalized-towers: Sheaf.Paper.SmoothPurityNormalizedTowers,
  spFiniteConstructibleTor, spDerivedCoefficientEvaluation,
  spConstructibleTorTowers, IsSpNormalizedTower. Its finite-level predicate is
  reused; the last normalization condition is intentionally absent as in the item.
* det-sp-tower-shriek-levels: Sheaf.Paper.SmoothPurityTowerShriekLevels,
  SpTowerShriek.R, Base, Operations, D, Ev, F, Fcomparison, tower_shriek_levels.
  The full record fields, normalizations, and Laws were read. Ordinary unbounded
  F is used on the subset the common interval puts in D+.
* def-weil-l-adic-coefficient-extension: Sheaf.NumberTheory.Padics.
  CoefficientExtensionFinite, Padic.finite_coefficientExtensionRing and its
  imported actual integers/ideal/quotient constructions. These are also used
  by SpTowerShriek.R/Base and spEllQuotientFinite.

The stated proof-dependency modules are imported without public, except those
already public statement dependencies. Mathlib proof leaves are imported from
their recorded files. No proof import was intentionally omitted for a cycle.

Edge cases checked before writing: X or Y empty (empty fibres have dimension
bottom); d=0 (no enlargement); negative a,b; a=b (single degree); the zero
coefficient ring (the annihilation hypothesis and zero modules still make sense);
the zero derived object; n=0 in Lean is exponent 1, so no positive coefficient
level is lost; towers with non-normalized transition maps; arbitrary degree-zero
module tests, including infinite or nonconstructible ones. There is no hidden
nonempty scheme, nonzero coefficient, flat input, or algebraically closed base
assumption. Geometric fibre fields are algebraic closures of actual residue fields.

Searches made with the prescribed launcher msearch.py, group NK and this item:

* LeanFinder: “Compactly supported derived direct image preserves constructibility
  and sends Tor amplitude [a,b] to [a,b+2d] for fibres of dimension at most d”:
  eight hits on constructible images/complex support and standard bounds, no match.
* Loogle: “HasProEtaleTorAmplitude, proEtaleRingCompactSupportImage”: zero hits,
  the project-specific identifier is unknown to the Mathlib search service.
* grep of Mathlib/AlgebraicGeometry: “TorAmplitude|torAmplitude|CompactSupport”:
  zero hits.
* LeanSearch: “Compact support direct image has Tor amplitude bounded by twice
  the geometric fibre dimension”: eight hits on module support dimensions and
  analytic compact supports, no matching etale/pro-etale theorem.
* rg in the named WeilConjectures source and lean/Sheaf: tower-bound, uniform Tor,
  compact-support Tor, and the item id. Found consumers describing this result,
  and separate integral or open-extension results, but no existing theorem
  stating both the finite-ring bound and this arbitrary-tower consequence.
  The prescribed item-id search finds no upstream declaration.

No STATEMENT-DISPUTED issue remains: the interval is justified by the source's
arbitrary-module projection formula and [0,2d] sheaf bound. In particular, no
bound is asserted for the chosen compactification's entire geometric fibres.

## Second reading by NK

Author self-check only, under this dispatcher brief's instruction to deliver
without starting other agents; the maintainer supplies the independent review.
Reopened the item and the complete module and checked the clause correspondence
above. The finite assertion uses the actual recorded compactification functor;
the tower assertion uses actual derived evaluation and actual F. The same a,b,d
occur at every level, n+1 covers all positive exponents, and q outside the closed
interval is explicitly zero. No normalization or extra origin compatibility
was introduced. The comparison's finite Noetherian restriction is automatic for
the finite rings in this theorem. No definition was copied or fabricated.

Validation results are recorded after the prescribed single-file compilation
and deliver2.py dry run below.

## Dependency modules

`def-coef-semilinear-system-models` is a landed node newly cited in stmt_deps
because the tower conclusion uses its actual system categories, and its module
`Sheaf.Paper.SemilinearSystemModels` is supplied with a section 1(B) elaboration
repair. The unmodified server source failed with stuck universe constraints
`max (max c r) v =?= ?u + 1` at scalarExtensionSection (606), ScalarTensorPure
(619), scalarEpsilonIso (639) and ScalarTensorComparisonModel (663). Its generic
coefficient universe is not required to be a successor. The competing
GrothendieckTopology.hasSheafify_of_essentiallySmall instance enforces that shape
when inferred for projections. During this module's elaboration it is disabled,
using the existing independent-coefficient sheafification instead, and restored
at the end, as the recorded coefficient-tower modules already do. The node is
changed only in lean; the main item gains the existing landed definition in
stmt_deps. All definition bodies, theorem statements, proof plans and independent
universe parameters of the dependency remain unchanged. This supplies the
recorded notion, rather than weakening its independent universe convention.

Validation: `deliver2.py NK det-sp-tower-bound-uniform --no-push` returned
`OK (dry run): commit d9fa37a499 passes the preflight and compiles; nothing pushed`.
It compiled both delivered files separately against the current server overlay,
including all repaired-interface consumers, and accepted the lean records, added
landed dependency, module ownership, docstrings, line widths and sorry-only theorem
proofs. No compiler warnings other than the permitted sorry warning were reported.
The dependency's public mathematical signatures and all universes are unchanged.

## Returned-delivery repair, 2026-10-18

The return for immutable head `0d59aa7f61ce` reported a 60-second private-overlay
timeout in `Sheaf.Paper.DerivedPullbackTensorHom`. Per the repair brief, the saved
packet was inspected and tested first, without restarting its construction. The
current dry run passed: `OK (dry run): commit 8c35caa234 passes the preflight and
compiles; nothing pushed`. It compiled the two delivered files separately and
rebuilt the required tower-shriek overlay without the returned timeout. The saved
repair is therefore retained, as the brief directs for a passing initial dry run.

Compared the sandbox with current shared main: the item's only differences are
`lean` and the added landed semilinear-model statement dependency. Current main's
semilinear module now also disables the competing sheafification instance; it
additionally imports two representative-model modules. The saved packet retains
its narrower import list and restores the instance after its own elaboration;
its mathematical declaration signatures and definition bodies are unchanged.
No global build, direct Git operation, live-source edit, timeout increase, or
launcher-tool modification was used.

Self-check reopened the current blueprint statement and proof, the saved theorem,
and the actual finite-level predicate, compactification composite, ordinary
tower category, exact evaluation and normalized geometric operations. Both
clauses keep the same input interval and original-fibre dimension bound; every
positive coefficient exponent is represented by `n + 1`. Empty schemes, zero
coefficients, dimension zero, negative degree endpoints and non-normalized towers
remain allowed. The return requires no mathematical statement correction.

Explicit wrapper validation also passed:
`scompile.py NK det-sp-tower-bound-uniform
lean/Sheaf/Paper/SemilinearSystemModels.lean
lean/Sheaf/Paper/CompactSupportUniformTorBound.lean`. The delivered library files
compiled in 47.7 seconds and 11.3 seconds respectively, each below 60 seconds;
the required tower-shriek overlay compiled in 53.2 seconds. Exit status was zero,
with no disallowed compiler warnings.

## Resumed repair validation, 2026-10-18

The required initial dry run of the retained packet passed against the refreshed
current base: `OK (dry run): commit 5e466216c8 passes the preflight and compiles;
nothing pushed`. The shared-fetch wait completed within the prescribed wrapper;
no lock inspection or tool modification was used. The return's overlay timeout
did not recur, so the saved Lean files and node records are retained as instructed.

The explicit prescribed `scompile.py NK det-sp-tower-bound-uniform` check of both
delivered files also exited zero: SemilinearSystemModels compiled in 22.6 seconds
and CompactSupportUniformTorBound in 4.1 seconds. No disallowed warnings appeared.

The resumed self-check reopened the current blueprint statement and proof, the
node, both delivered modules, the finite-level Dctf predicate, and the actual
sequence-site tower category and derived evaluations. The finite assertion keeps
constructibility and the precise [a,b+2d] Tor interval; the tower assertion keeps
that interval and explicitly states vanishing outside it, without normalization.
The bound is on the original geometric fibres. Comparing with current shared
main confirms that only lean changes on the dependency node, while the item
changes only lean and adds the already landed semilinear-system definition to
stmt_deps. No mathematical statement correction is needed.
