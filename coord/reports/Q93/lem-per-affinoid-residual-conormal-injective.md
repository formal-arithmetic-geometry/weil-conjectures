## Worker report

The delivery states `RestrictedSeries.affinoid_residual_conormal_injective` in
`Sheaf.RingTheory.AffinoidResidualConormalInjective`. There is one theorem, whose whole
proof is `sorry`; there are no new definitions, auxiliary theorems or axioms. The node
changes only in `lean`. No statement correction or dispute is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The complete field with a nontrivial real-valued nonarchimedean absolute value is
  `(K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`.
  A multiplicative field norm is the absolute value; the ultrametric distance condition
  is the nonarchimedean inequality. No discretely valued, characteristic-zero, perfect,
  algebraically closed or separability hypothesis is added.
- The integers `r,s ≥ 0` are `(r s : ℕ)`. The ring `A` is written directly as
  `↥(MvPowerSeries.IsRestricted.subring (R := K) (1 : Fin r → ℝ))`.
  At polyradius one Mathlib's cofinite weighted coefficient-decay condition is exactly
  the node's finiteness condition for coefficients of norm at least each positive epsilon.
  The operations are the inherited formal-series operations, including Cauchy product.
- The equations are `f : Fin s → A`; the named ideal `I` has defining equality
  `hI : I = Ideal.span (Set.range f)`. Naming `I` this way is equivalent to substituting
  its defining expression, and does not add a restriction. `C = A ⧸ I` is not used as
  a separate parameter because the hypothesis uses its coefficient-extended versions
  and the conclusion only uses `I` and `n`.
- The geometric regularity assumption is `hgeom`. It quantifies over all complete
  ultrametric normed fields `L` and isometric ring maps `φ : K →+* L`. Isometry makes
  these ring maps embeddings. The extended equation ideal is
  `Ideal.span {g : L⟨x⟩ | ∃ j : Fin s, g.val = MvPowerSeries.map φ (f j).val}`.
  This uses the actual coefficient extension, not an arbitrary map. Since φ is isometric,
  coefficient decay is preserved: for each j there exists exactly one such restricted
  series. Hence the displayed ideal is exactly `(f₁,L,…,f_s,L)`, including s=0.
  `IsRegularRing` is the dependency node's Mathlib ring predicate, which extends
  `IsNoetherianRing` and requires regular localizations at every prime.
- `L : Type (max u v)` permits larger extensions without a vacuous small-universe
  hypothesis. For a smaller extension its universe lift preserves the coefficient
  formula, norm, completeness and regularity. In particular a lift of the residue
  field is always among the tests, and no equality of universes is assumed.
- The maximal ideal is `(n : Ideal A) [n.IsMaximal]`, with `hIn : I ≤ n`.
  `Ideal.IsMaximal` means proper and maximal among proper ideals, as specified.
- The residue field is exactly `A ⧸ n`, not a chosen extension or the residue field
  of a different local ring. Mathlib supplies its field structure from `[n.IsMaximal]`.
- The source of `d` is the actual quotient `I ⧸ (n • ⊤ : Submodule A I)`.
  The submodule consists of finite sums of products of elements of n with elements of I,
  so this is `I / n I`. Mathlib's canonical quotient-scalar module instance supplies
  its `A ⧸ n`-vector-space structure, with
  `Module.Quotient.mk_smul_mk` describing the quotient action. No module structure
  is chosen existentially.
- The target `Fin r → A ⧸ n` is the finite direct sum of r copies of κ in its
  canonical coordinate model. It includes r=0.
- The conclusion existentially supplies an `A ⧸ n`-linear map `d`, its formula on
  EVERY representative, and `Function.Injective d`. For every `g : I` and coordinate
  `i`, the formula supplies the restricted series `dg` whose underlying series is
  `MvPowerSeries.pderiv K i g.val.val`, and asserts
  `d (Submodule.Quotient.mk g) i = Ideal.Quotient.mk n dg`.
  The underlying-series equality uniquely determines dg. Surjectivity of the quotient
  projection and coordinatewise equality uniquely determine d. Thus this is exactly
  the specified canonical conormal map, with its well-definedness and linearity,
  not injectivity of an unconstrained existential map. The existential restricted
  derivative includes the necessary preservation of restriction without defining
  derivative data using a postponed existence theorem.

Dependencies and sources read:

- `def-weil-regular-scheme`: its complete node, the recorded
  `Sheaf.AlgebraicGeometry.IsRegularScheme` / `AlgebraicGeometry.IsRegularScheme`, and
  its `mathlib_match` ring clauses were read. This item uses the ring clause,
  `IsRegularRing` in `Mathlib.RingTheory.RegularLocalRing.Defs`, rather than the scheme
  clause. The old mathlib_match remains valid for precisely this clause, as its lean.note
  explicitly says. Importing the unused scheme definition would not change this encoding.
- `Mathlib.RingTheory.MvPowerSeries.Restricted`: `MvPowerSeries.IsRestricted` and
  `MvPowerSeries.IsRestricted.subring`, including their operations and signatures.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv` and the termwise
  coefficient formula in its documentation and implementation.
- `Mathlib.Algebra.Module.Torsion.Basic`: the canonical instance
  `Module (A ⧸ n) (I ⧸ n • ⊤)` and `Module.Quotient.mk_smul_mk`.
- `Mathlib.RingTheory.Ideal.Quotient.Basic`: quotient rings and their maximal-ideal fields.
- Private proof imports retain the already stated plan:
  `Mathlib.LinearAlgebra.TensorProduct.Defs`;
  `WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`;
  `Mathlib.RingTheory.Localization.Ideal`;
  `Mathlib.RingTheory.Flat.Localization`;
  `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.
  In particular the signatures and docstrings of
  `AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_flat_base_change`,
  `IsRegularLocalRing.exists_span_eq_of_isRegularLocalRing_quotient`, and
  `IsLocalization.flat` were read. The three analytic Tate proof prerequisites have
  no Lean records yet, so there is no module for them to import. They are proof-only
  prerequisites and no missing statement notion is used here.

The source PDFs were opened online: Temkin Proposition 3.3.2 and its preceding
continuous differential discussion (printed pp.20–21), and Conrad section 3.3
(printed pp.509–512). The proof docstring includes all seven node proof steps:
restrictedness/Leibniz and descent; finite residue extension and evaluation; rational
local coordinates and regular quotient; two flat conormal base changes and residue
identification; independent generators; kernel calculation; derivative factorization.

Edge cases checked before writing: r=0 gives a zero target and the source is zero
for every admissible maximal ideal; s=0 gives I=0 and zero source; I=A gives no
maximal n containing I; the empty equation family extends to the empty generating
set; no test-field separability or perfection assumption was introduced. Fin r
rather than a positive index type retains all zero-index cases. In characteristic p
the termwise natural-number coefficient is reduced in K, as required.

Searches for duplicates (all prescribed searches were run):

- `msearch.py … leanfinder`: “Geometric regularity of a Tate algebra quotient implies
  injectivity of the continuous conormal differential on every residue fibre”. Eight
  hits, including `Algebra.SubmersivePresentation.cotangentComplexAux_injective` and
  `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`.
  These concern algebraic presentations/formal smoothness, not restricted series.
- `msearch.py … loogle`: `MvPowerSeries.pderiv, PowerSeries.IsRestricted, IsRegularRing`.
  Zero hits; the existing notions were located by direct source search.
- `msearch.py … leansearch`: “Tate algebra continuous conormal map residue field injective”.
  Eight hits on algebraic cotangent criteria, continuous algebra maps and quotient
  residue maps; none assert this analytic theorem.
- `msearch.py … grep`: `TateAlgebra|RestrictedPowerSeries|IsRestricted|pderiv`, in
  `RingTheory/MvPowerSeries`. Eleven hits found the restrictedness definition/subring
  and formal partial derivative. These existing notions are reused directly.
- `rg` over Mathlib and `lean/WeilConjectures`, plus the required item-id search:
  no declaration of this theorem; Mathlib has the component notions just listed.
- `rg` over `lean/Sheaf` for Tate/restricted-series and derivative/conormal names:
  `RestrictedSeriesPresentation`, `AffinoidPolynomialClosedPointComparison`,
  `GrauertRemmertPowerbounded`, and `NonarchimedeanSeriesSubstitution` were found/read.
  They reuse the same Mathlib subring, and none states this theorem or constructs
  the multivariate residue conormal map. No copy of their constants or presentation
  predicates is needed here.
- The DAG restricted-series/Tate nodes and `tools/blueprint_refs.py search 'Tate'`
  were checked; the existing restricted-series definition node is
  `def-trf-restricted-series-presentation`, and the present statement directly uses
  its underlying Mathlib notion without introducing another node. The ancestor command
  returned `lem-per-artin-gabber-affine-curve`.

## Second reading by Q93

The dispatcher explicitly prohibits starting another agent. This section records a
second pass by the same worker, not a claim of independent review; the maintainer's
independent reading remains the review gate.

With the node and Lean signature open, I checked each item above again: the input
absolute value, completeness, r and s, restricted coefficient decay, generated ideal,
every isometric complete field extension and regular Noetherian quotient, maximality
and containment, the actual quotient field and vector-space action, each derivative
coordinate, and injectivity. The existential formula determines the unique intended
map; it is not a replacement by an arbitrary injective linear map. The use of a set of
coefficient-extended equations agrees with a finite family because isometry preserves
restrictedness and subtype inclusion is injective. No mismatch or node correction was
found. Two elaboration annotations were repaired: the extended-series set binder has
its explicit subtype, and the quotient submodule has its explicit base ring. These
annotations do not change the mathematical statement. The unused project presentation
import was replaced by its smaller Mathlib restricted-series dependency.

Validation: the final module passes both the sandbox and actual module-name compiles
through `scompile.py`, with no errors or unexpected warnings.
