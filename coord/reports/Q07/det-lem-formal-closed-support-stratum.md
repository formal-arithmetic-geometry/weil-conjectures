## Worker report

The item is a duplicate of the parallel node
`det-lem-formal-closed-support-stratum-hom` (its `blueprint.same_as` field names this
node).  I therefore added no Lean module.  The node's `lean` record points to the
landed declaration
`AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_stratum_globalHom` in
`Sheaf.AlgebraicGeometry.ClosedSupportStratumHom`, with `existing: true` and all of
that module's helper declarations listed in `declarations`.

The existing declaration renders the statement as follows.  Its hypotheses are
schemes `S Z V X`, morphisms `i : Z ⟶ X`, `j : V ⟶ X`, and `uS : S ⟶ Z`, with
`IsClosedImmersion i`, `IsOpenImmersion j`, `QuasiCompact j`, and
`IsOpenImmersion uS`; `hij` identifies the closed and complementary open ranges;
`_hΛ` is admissibility of the commutative condensed coefficient ring; and `L` is a
finite locally projective module.  The factorization `a_! = i_*u_!` is rendered by
`lowerStar` composed with `openImmersionLowerShriek`.  The first conjunct is the
natural comparison from global derived Hom on `X` to closed-support derived Hom on
`Z`; the second is restriction along `uS`; the third is evaluation by the dual and
termwise tensor followed by derived global sections.  The final clause gives, for
every `q : ℤ`, the corresponding natural isomorphism after `homologyFunctor q`,
which is the displayed `Hom(K[q]) = H^q` assertion.  The helper declarations are
`stratumGlobalRHom`, `stratumRGamma`, `stratumDual`,
`stratumDualTensor_preservesFiniteLimits`, `stratumDualTensor`, and
`stratumDualTensor_derived`.

The two recorded statement dependencies were read in full.  The declaration for
`det-lem-formal-closed-support-derived` is
`AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_derived` in
`Sheaf.Paper.FormalClosedSupportDerived`; it supplies the closed-support derived
adjunction, injective-unit clause, support triangle, and fibre formula used by the
first comparison.  The declaration for `sk-lem-coefficient-heart` is
`AlgebraicGeometry.ProEtale.coefficientHeart` in `Sheaf.Paper.CoefficientHeart`;
its docstring supplies the locally closed extension and constructible-heart context.
The existing duplicate's module is the concrete statement interface, so no new
imports or dependency modules are needed here.

Edge cases checked against the existing statement and its docstring: the zero
module (`L` of rank zero), the empty scheme or empty stratum, an empty open
complement, arbitrary integer shifts including `q = 0` and negative `q`, and the
identity/empty immersion cases.  The finite locally projective predicate permits
rank zero, and the standing finite-type hypotheses make the quasi-compact open
complement required by the existing declaration automatic.

Searches made:

- `msearch.py ... leanfinder "Hom out of an extension by zero from a stratum"`:
  only generic homological-complex embedding hits; no independent Mathlib match.
- `msearch.py ... loogle "closedSupport_stratum_globalHom, stratumGlobalRHom"`:
  no Loogle hit (the project declaration is not in Mathlib).
- `msearch.py ... grep "closedSupport_stratum_globalHom|stratumGlobalRHom"` on
  `lean/Sheaf`: found the landed declaration and helper definitions in
  `Sheaf/AlgebraicGeometry/ClosedSupportStratumHom.lean`.
- `rg` over `lean/Sheaf` and the read-only slopmaster2 `WeilConjectures` source for
  `closedSupport`, `stratumGlobalRHom`, extension-by-zero, and derived-Hom terms:
  found no second declaration of this statement.
- `grep -rl 'det-lem-formal-closed-support-stratum' dag/nodes`: confirmed the
  sibling node and its `same_as` link; its `lean` record and source module were read
  before reusing the declaration.

No `STATEMENT-DISPUTED` flag or node correction is needed.  Since this is an
`existing: true` attachment, there is no file to compile with `scompile.py`.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
