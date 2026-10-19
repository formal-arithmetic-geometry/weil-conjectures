## Worker report

The module `Sheaf.AlgebraicGeometry.FsChartFreeFactorization` states
`AlgebraicGeometry.exists_fs_chart_free_factorization`, with `sorry` as its only proof.
It is the node's general algebraic refinement of ILO VI Proposition 1.9, rather than
an assertion that ILO states the general lemma verbatim. No definition, new node,
dependency repair, or statement correction is needed. There is no disputed clause.

The hypothesis and conclusion correspondence is as follows:

- The additive commutative monoids are `{P : Type u} {Q : Type v}` with
  `[AddCommMonoid P] [AddCommMonoid Q]`. Both universes are explicitly bound and
  independent. The fine saturated hypotheses are `hP` and `hQ`, using the existing
  `IsFineSaturatedMonoid (Multiplicative P)` and the analogous expression for `Q`.
  `Multiplicative` is Mathlib's notation-changing type tag: finite generation,
  injectivity into group completion and root saturation are exactly the existing
  predicate's clauses, with no sharpness or torsion-freeness of the monoids imposed.
- The given chart is `g : P →+ Q`. Its canonical group-completion homomorphism is
  `Algebra.GrothendieckAddGroup.lift
  ((Algebra.GrothendieckAddGroup.of (M := Q)).comp g)` throughout the statement.
  `hg : Function.Injective (...)` is exactly the asserted injectivity of `g^gp`.
- The cokernel `L` is the actual quotient `Algebra.GrothendieckAddGroup Q ⧸
  (...).range`. The range is the additive subgroup image of the canonical map from
  `P^gp`, not the image monoid of `P`. `htorsion` says, for every `n : ℕ` and
  every element `ℓ` of that quotient, `0 < n → n • ℓ = 0 → ℓ = 0`.
- The existential `r : ℕ` supplies the nonnegative rank, and `q : Fin r → Q`
  supplies exactly `r` elements in the target monoid itself. The first conjunct
  quantifies over every `ℓ : L` and states `∃! m : Fin r → ℤ` with
  `ℓ = ∑ i, m i • QuotientAddGroup.mk
  (Algebra.GrothendieckAddGroup.of (q i))`. This is precisely the node's definition
  of a Z-basis: existence and uniqueness of all integer coefficients, for the images
  of the selected elements under the actual group-completion/quotient maps.
- The existential homomorphism `h : P × (Fin r → ℕ) →+ Q` has the Cartesian
  product with componentwise addition as its domain. The second conjunct requires
  `h (p,n) = g p + ∑ i, n i • q i` for all inputs. Thus `h` is completely fixed
  by the requested formula; an unconstrained map has not replaced this construction.
  The third conjunct is `Function.Injective h`.
- The existential `φ : Algebra.GrothendieckAddGroup P × (Fin r → ℤ) ≃+
  Algebra.GrothendieckAddGroup Q` is an additive group isomorphism. The final
  conjunct fixes its value on every pair `(x,m)` to `g^gp(x) + ∑ m_i[q_i]`.
  Under the product universal-property identification stated in the node,
  this is exactly `h^gp`, not an arbitrary isomorphism between the groups.
  Indeed, its restriction along `(p,n) ↦ ([p], fun i ↦ (n i : ℤ))` agrees with
  `[h(p,n)]`; these elements generate the group completion. The docstring records
  this identification and the proof of all other clauses.

Dependency declarations read and used:

- The statement dependency `def-trf-fs-log-blowup` records
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`, which is imported publicly.
  Its `EtaleLogStructure.IsFineSaturated` and `IsNonemptyCoherentIdeal` use
  `AlgebraicGeometry.IsFineSaturatedMonoid` from its public dependency
  `Sheaf.AlgebraicGeometry.LogRegularPair`. I read that definition's full signature,
  its canonical-group-completion docstring and its three defining clauses.
  This is the same fs notion specified inline in the dependency node; no log scheme
  is needed as an additional input to the purely monoid statement.
- Mathlib's `Algebra.GrothendieckAddGroup`, `.of`, and `.lift` in
  `Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup` provide the canonical
  additive completions and induced map; their signatures/docstrings were inspected.
  `AddMonoidHom.range` in `Mathlib.Algebra.Group.Subgroup.Ker` and
  `QuotientAddGroup.mk`/the quotient structure in
  `Mathlib.GroupTheory.QuotientGroup.Basic` provide the image subgroup and quotient.
- Proof-only imports retain the stated proof plan: `Mathlib.LinearAlgebra.FreeModule.PID`
  (`Module.basisOfFiniteTypeTorsionFree'`, the `mathlib_match` for
  `lem-trf-fg-torsionfree-group-free`); `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`
  (`Matrix.det`, `Matrix.det_apply`); `Mathlib.LinearAlgebra.Matrix.Adjugate`
  (`Matrix.adjugate_mul`, `Matrix.mul_adjugate`); and
  `WeilConjectures.LinearAlgebra.Matrix.CauchyBinet` (`Matrix.cauchy_binet`).
  The last recorded module was read using `scompile.py --source` against the
  current published source. These are ordinary imports, not public imports.

Source checks: read ILO VI Proposition 1.9 on printed pp. 70--71 (the nodal chart
has injective `g` and cokernel Z), VIII 3.1.1--3.1.2 and 3.1.9--3.1.10 on
pp. 98--99, and the saturation convention VIII 3.1.17 on p. 101 in the local PDF.
The general assertion and nine-step proof are the node's explicit agent-supplied
refinement. The theorem docstring contains all nine steps, including the quotient
image saturation calculation, the Cauchy--Binet nonsingular tuple, least determinant,
rational-coordinate floor calculation, saturation and column replacement, basis lift,
isomorphism, and the group completion of the product.

Edge cases checked by reading the explicit hypotheses and conclusions:

- `r = 0` is allowed (`Fin 0`); its function types are singletons and its sums are
  empty. The quotient has a unique empty expansion, and the last formula is `g^gp`.
  The identity chart and the zero monoids are included.
- `P = 0`, `Q = ℕ^r` gives the ordinary free chart, and the diagonal chart
  `ℕ → ℕ²`, `1 ↦ (1,1)`, admits a quotient-basis lift in one coordinate.
- Torsion units are permitted, for example `P = Q = ℕ × Z/2`, `g = id`.
  No `IsAddTorsionFree P` or `IsAddTorsionFree Q` assumption was inserted.
- The multiplication-by-two chart on `ℕ` is correctly excluded by `htorsion`;
  the nonsaturated submonoid generated by 2 and 3 is excluded by `hQ`.
- No assumption that `g(P)` is a face, that either monoid is sharp, or that the
  cokernel basis is nonempty appears. The product is a product of additive monoids,
  so natural coefficients use addition and natural scalar multiplication.

Searches for reuse (all with group Q157 and this item):

- `msearch.py leanfinder`: "An injective homomorphism of fine saturated monoids
  with torsion-free group cokernel has lifts of a Z basis inside the target monoid
  and factors through adjoining free nonnegative generators". Eight hits included
  `AffineAddMonoid.embedding`, `Module.Baer.extension_property_addMonoidHom`, and
  free-group universal properties. Read the affine-monoid embedding source: it
  embeds a torsion-free monoid into a free group, and does not factor a prescribed
  chart or choose quotient basis vectors in `Q`. No exact match.
- `msearch.py leansearch`: "A fine saturated monoid map injective on group
  completions with torsion-free cokernel has generators lifting an integer basis
  of the cokernel". Eight hits included the canonical Grothendieck embedding/lift,
  localization-map injectivity and torsion-free transfer. These do not assert the
  required target-monoid basis lifts.
- `msearch.py loogle`: `"GrothendieckGroup.lift"`. Three hits were the lift,
  its inverse evaluation and evaluation formula. These supply the canonical map
  used above, not the factorization theorem.
- `msearch.py grep`: `saturat.*basis|basis.*saturat|fsChart|freeFactorization`.
  No Mathlib hits. The group's searches reuse existing Mathlib notions rather
  than adding a duplicate fs or group-completion definition.
- `rg` in `WeilConjectures/`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `fsChartFreeFactorization|fine saturated|fine.*saturat.*chart|saturat.*basis|basis.*saturat`
  found the existing fs definition and its log-geometry users, but no factorization
  theorem. The candidate final name `exists_fs_chart_free_factorization` was also
  checked against project/Mathlib sources. The required `grep -rn` of the item id
  in `WeilConjectures/` returned no hits.

Validation: the module was compiled separately through the prescribed `scompile.py`
wrapper. Both its sandbox and library-module invocations compiled without errors
or warnings. `autoImplicit` is disabled, every universe and variable is bound,
and the only postponed proof is the named theorem belonging to this node.

## Returned-delivery repair and self-check

The return of immutable head `ec731e593b09` reports that the reviewer's
`--apply-fixes` rejected the repository-relative report path
`coord/reports/Q157/lem-trf-fs-chart-free-factorization.md`. This retry retains the
saved theorem and node record and supplies the report through the prescribed
sandbox `report.md`; `deliver2.py` puts it at its repository destination. No
repository-relative report path is submitted as a review fix. This is a report
and packet repair; no mathematical change was requested by the return.

The initial repair dry run passed preflight and compiled the saved module against
the current published library (`242ee58852`, nothing pushed). A fresh comparison
with the shared node found that only `lean` differs. The recorded signature is
verbatim from the theorem, every universe and variable is explicitly bound, and
all module lines are at most 100 characters. Rereading the fs predicate confirmed
its finite-generation, integrality and root-saturation clauses, via the recorded
dependency's public import. The quotient-basis, formula for `h`, injectivity and
formula for the group isomorphism still match every conclusion of the node,
including rank zero and monoids with torsion units. No mismatch was found.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
