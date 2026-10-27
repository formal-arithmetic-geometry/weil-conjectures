## Worker report

The item is stated as `RestrictedSeries.jacobianIdeal_eq_top_of_geometrically_regular`
in `Sheaf.RingTheory.GeometricAffinoidJacobianUnit`. Its proof is `sorry`; no mathematical
theorem is proved in this delivery. The original TeX statement is unchanged. Its
`stmt_deps` gains `def-per-restricted-series-jacobian`, which is now a landed dependency giving the canonical maps
and the explicit ideal used in the conclusion. This repair delivers only the theorem
module, its item record and this report; it introduces no definition node.

Hypothesis and clause correspondence:

- The field K with a nontrivial real-valued absolute value is
  `{K : Type u} [NontriviallyNormedField K]`; the nonarchimedean inequality is
  `[IsUltrametricDist K]`, and completeness is `[CompleteSpace K]`.
- The nonnegative integers r and s are `{r s : ℕ}`. The Tate algebra is exactly
  `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))`.
  In Mathlib's definition the monomial weight is the product of powers of one,
  hence one, so the defining condition is coefficient norms tending to zero in
  the cofinite filter. This is exactly finiteness of the coefficients of norm
  at least ε for every positive ε. No formal-power-series ring replaces it.
- The equations are the function `f : Fin s → ...`. `relationIdeal f` is
  `Ideal.span (Set.range f)`, and the quotient is the ordinary ring quotient by
  this ideal. There is no separatedness or nonzero-quotient hypothesis.
- Every complete real-valued nonarchimedean extension field is quantified by
  `∀ (L : Type (max u v)) [NormedField L] [IsUltrametricDist L] [CompleteSpace L]`.
  The ring homomorphism `φ : K →+* L` with `hφ : Isometry φ` is precisely the
  isometric embedding (field homomorphisms are injective). L need not separately
  carry a nontrivial-norm hypothesis, since the isometry from K implies it.
  The max universe avoids a vacuous smaller-universe test-field condition;
  the theorem is polymorphic in v, and includes same-universe/identity tests.
- `map r φ hφ` uses `MvPowerSeries.map φ`, restricted to the two radius-one
  subrings; its coefficients are φ of the original coefficients. Thus
  `relationIdeal (fun j ↦ map r φ hφ (f j))` is exactly the extended equation ideal.
- `IsRegularRing` of the quotient is the node's regular Noetherian ring condition:
  the Mathlib class extends `IsNoetherianRing` and requires regular local rings at
  all primes. This is the ring clause of `def-weil-regular-scheme`'s recorded
  `mathlib_match`; its scheme-only public module is also imported as prescribed.
- E and T are `Finset (Fin s)` and `Finset (Fin r)`; `h : T.card = E.card`
  restricts the sum to equal-size pairs. `orderEmbOfFin` orders both increasingly.
  `jacobianMinor` has rows T (variable indices) and columns E (equation indices),
  both indexed by `Fin E.card`, with entry `pderiv r i (f j)`, and uses `Matrix.det`.
- `pderiv` has underlying power series exactly `MvPowerSeries.pderiv K i f.val`.
  Its coefficient at ν is `(νᵢ+1)` times the coefficient at `ν+eᵢ` (commutativity
  reconciles Mathlib's multiplication order). It is the termwise continuous
  derivative, not an algebraic derivative of a polynomial approximation.
- `Ideal.span (f '' (E : Set (Fin s)))` is I_E. Its `.colon (relationIdeal f : Set _)`
  is exactly the set of a with aI contained in I_E, by `Submodule.mem_colon`.
- `Ideal.map (Ideal.Quotient.mk (relationIdeal f))` is the barred colon ideal.
  Multiplying it by `Ideal.span {Ideal.Quotient.mk ... (jacobianMinor f E T h)}`
  gives its product with the principal minor ideal in C. The indexed supremum
  in `jacobianIdeal` is the sum over all pairs. Repeated proof witnesses of the
  cardinality equality do not affect an ideal supremum.
- The conclusion `jacobianIdeal f = ⊤` says exactly H=C. No fixed cardinality of
  minors, equidimensionality, characteristic, perfection, or discrete valuation
  has been imposed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`,
  and the node's ring match `IsRegularLocalRing`, `IsRegularRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs` (including the Noetherian superclass).
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, `Matrix.det` and `det_apply`.
- Landed interface `Sheaf.RingTheory.RestrictedSeriesJacobian`, declarations
  `RestrictedSeries.map`, `pderiv`, `relationIdeal`, `jacobianMinor`, `jacobianIdeal`.
  The radius-one ring itself is reused from Mathlib and from
  `Sheaf.RingTheory.RestrictedSeriesPresentation` / `def-trf-restricted-series-presentation`;
  there is no second definition of the ring.
- Proof-only imports: `Mathlib.RingTheory.Localization.AtPrime.Basic`
  (`Localization.AtPrime`), `Mathlib.Algebra.Module.LocalizedModule.Basic`
  (`LocalizedModule`), `WeilConjectures.LinearAlgebra.NonzeroMaximalMinorOfInjective`
  (`Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective`),
  `Mathlib.RingTheory.LocalRing.Module` (`IsLocalRing.map_mkQ_eq_top`),
  `Mathlib.RingTheory.Ideal.Maximal` (`Ideal.exists_le_maximal`), and
  `Mathlib.LinearAlgebra.LinearIndependent.Lemmas` (`exists_linearIndependent'`).
  `lem-per-affinoid-residual-conormal-injective` now records
  `Sheaf.RingTheory.AffinoidResidualConormalInjective` /
  `RestrictedSeries.affinoid_residual_conormal_injective`. Its full signature and
  docstring were read and its proof-only import is included. Its derivative formula
  specifies the same canonical conormal map used in Step 1.

Edge cases checked before finalizing:

- s=0: I=0, E is empty, its colon is (0:0)=the whole ring and the empty minor
  equals one. Thus the defined ideal has the expected unit summand.
- r=0: only T=empty is available; equal cardinality forces E=empty. The Tate
  algebra is K. Equations all zero give the preceding case; a nonzero constant
  equation gives C=0. Neither is excluded.
- C=0: `⊤` is also the zero ideal; neither the construction nor the theorem
  assumes `Nontrivial C`.
- E=T=empty even when r,s are positive: I_E=0, D=1, giving exactly the
  annihilator-of-I summand, not an unjustified unit summand.
- Positive characteristic: for f=x^p-a over an imperfect field, the derivative
  is zero, but a complete extension containing a p-th root has a nonregular
  quotient, so the hypothesis correctly excludes this obstruction. For f=x,
  the first derivative is one and the unit certificate is present.

Searches actually run (full machine output is retained in the landed definition node's
`mathlib_searches` and the wrapper's `searches.jsonl`):

- LeanFinder: “For a geometrically regular quotient of a Tate algebra the continuous
  Jacobian ideal generated by minors times colon ideals is the unit ideal”. Eight
  algebraic smooth-presentation hits; none is the analytic statement.
- Loogle: `MvPowerSeries, RestrictedPowerSeries, TateAlgebra` returned an unknown
  identifier for RestrictedPowerSeries; this is not counted as a negative search.
  Follow-up `MvPowerSeries.IsRestricted` found the exact existing restriction predicate
  and related closure lemmas. The local source's subring and its data were read.
- msearch grep: `TateAlgebra|RestrictedPowerSeries|restricted.*[Ss]eries|IsRestricted`
  found Mathlib's multivariate/univariate restriction files. Reused the subring.
- LeanSearch: “Restricted multivariate power series form the Tate algebra subring,
  coefficient extension preserves restriction and continuous partial differentiation
  preserves restriction”. Eight hits concerning coefficient-subring restriction;
  no canonical analytic coefficient-map/derivative/Jacobian bundle.
- LeanFinder: “The Tate algebra of restricted multivariate power series, with
  coefficient extension along an isometric field embedding and termwise partial
  derivatives”. Eight perfectoid/Laurent/Weierstrass hits; no matching construction.
- Direct rg over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  found the existing RestrictedSeriesPresentation and AffinoidPolynomialClosedPointComparison,
  which use the radius-one ring but do not give these maps or this ideal. The node-id
  search in WeilConjectures found no statement. Exact new-declaration-name rg over
  Mathlib, WeilConjectures and Sheaf found no conflicts.
- DAG text search for restricted series and Tate algebras found
  `def-trf-restricted-series-presentation`, which is cited by the landed Jacobian definition node, and
  statement nodes concerning other affinoid properties. `blueprint_refs.py search
  'restricted power series'` and `search 'Jacobian ideal'` each returned zero;
  the broader `search 'Tate'` returned 276 mostly Tate-twist matches and no copy of
  the analytic Jacobian construction. `blueprint_refs.py ancestor` returned
  `lem-per-artin-gabber-affine-curve`.

Source read: Temkin's linked PDF, Proposition 3.3.2 and its preceding formula on
printed pp.20--21. The displayed matrix there is transposed relative to the node;
transposing the square selected minor does not change its determinant. The node's
geometric-regularity hypothesis is retained in full. No statement correction or
STATEMENT-DISPUTED finding is made.

## Second reading by Q06

Author's second pass, not an independent review: the dispatcher brief forbids
starting another agent and assigns independent review to the maintainer. I reread
the current item JSON, theorem file, and landed definition node and module side by side. The field/completeness,
all-extension hypothesis, finite equation list, both increasingly ordered subsets,
colon membership, quotient images, and unit-ideal conclusion match as detailed
above. The regularity node's scheme declaration alone does not describe rings;
its recorded Mathlib match does, so `IsRegularRing` is used and its superclass was
checked. The duplicate definition node and byte-identical module were removed from this
delivery as required by the return. No original item hypothesis or clause changed,
and all definition references now resolve to the already landed module.

## Repair of return 6347acacf25d

1. The return says that `def-per-restricted-series-jacobian` already exists on
   `sheaf-dag`. Compared the retained delivered module and node with the current
   read-only main checkout. The modules are byte-for-byte identical; the definition
   node differs only by main's `reviewed` and `reviewed_lean` fields. Removed the
   duplicate definition node and module from the sandbox delivery. The theorem
   imports the existing `Sheaf.RingTheory.RestrictedSeriesJacobian` and its item
   `stmt_deps` cites the landed `def-per-restricted-series-jacobian`. No existing
   dependency record is changed. Recreated the item record from current main,
   preserving all main fields except the authorized `lean` and dependency addition.
   This repairs the collision instead of renaming or recreating the same notion.

The current main also records the conormal lemma. Read its complete signature and
proof docstring and added its required proof-only import. The theorem signature
and every hypothesis and conclusion remain exactly as in the returned delivery.
The same edge-case checks above apply because the reused definitions are identical.

Repair validation: `scompile.py Q06 lem-per-geometric-affinoid-jacobian-unit`
compiled the sole delivered theorem module against the published library and current
landed dependencies with exit code 0 and no errors or warnings. The wrapper included
server queue time in the reported durations. The delivery now contains only the item
node, theorem module and report; the duplicate definition is absent.
