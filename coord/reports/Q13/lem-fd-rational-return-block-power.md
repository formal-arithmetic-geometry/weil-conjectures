## Worker report

The module `Sheaf.Paper.RationalReturnBlockPower` states
`WeilConjectures.fdRationalReturnBlockPower`, with `sorry`, and defines its explicit
endpoint identifications and named specializations of the existing constructions.
No node statement or dependency list is changed. No new nodes or dependency modules
are needed. Every universe is explicit (`universe u`) and `autoImplicit` is false.
The two elementary helper theorem proofs are also `sorry`; they express the
positive-multiple return equality and the scheme-power equality already present in
Steps 1 and 2 of this node, and are listed in `lean.declarations`. Their docstrings
supply their full proofs. Every definition contains actual data.

Source checked: the current `literature/blueprint/latest/blueprint/`
`sec-deligne-laumon-a1/sk-p-dl-a1-some-weight/`
`lem-fd-realified-kernel-real.proof.md`, Step 2, the residue-extension power of
local Frobenius. The assigned node extracts the repeated-return calculation
rather than asserting the unit statement about reality of a kernel.

Hypothesis correspondence:

- The fixed finite field, cardinality q, its characteristic and arbitrary fixed
  algebraic closure k are `D : FiniteFieldDatum.{u}`. The chosen prime, its
  primality, its inequality with the characteristic and the chosen algebraic
  closure of Q_l are `c : D.CoefficientDatum`, with `c.l` and `c.different`.
  The field `E : Padic.FiniteCoefficientFields c.l c.Qbar` is exactly a finite
  coefficient subextension of that closure, with its published instances.
- The separated finite-type k_0-scheme is `Y₀ : Over (Spec (.of D.k₀))`,
  `[LocallyOfFiniteType Y₀.hom]`, `[QuasiCompact Y₀.hom]`,
  `[IsSeparated Y₀.hom]`. Its geometric fibre is the existing
  `(D.geometricFiber Y₀).left`, s is `Spec (.of D.k)`, and the Frobenii are
  `(D.geometricFrobenius Y₀).hom` and `(frobeniusPointIso D).hom`.
- The specified associative integral and rationalized comparison framework is
  `C : IntegralComparisonSystem c.l` and `_hC :
  IntegralComparisonRealizationCoherence c.l E.val E.val (AlgHom.id _ _) C`.
  The identity coefficient extension is sufficient because there is only one
  coefficient field in this statement. C supplies the stipulated comparison
  families, and hC supplies their published coherence, not an extra geometric
  or lattice assumption. This is the same framework interface as the recorded
  iterated-return calculus theorem.
- The positive paper period is `d+1` in Lean, with arbitrary `d : ℕ`.
  The geometric k-point is `z : Over.mk (𝟙 (Spec (.of D.k))) ⟶
  D.geometricFiber Y₀`; its underlying scheme arrow is `z.left`.
  The return hypothesis is `w : localPositivePower g_s d ≫ z.left =
  z.left ≫ localPositivePower g_Y d`. Categorical composition is left-to-right,
  so this is exactly the paper's g_Y^(d+1) z = z g_s^(d+1), with the sides swapped.
  `localPositivePower g d` is the recorded positive power g^(d+1).
- Prime invertibility on s and Y is supplied by the already defined
  `frobeniusPointPrimeInvertible D c.l c.different` and
  `sfWeilPrimeInvertible D c.l c.different Y₀`. These are passed explicitly;
  no independent prime-invertibility hypotheses are added.

Construction and clause correspondence:

- `fdRationalReturnIndex d 0 = d` and
  `fdRationalReturnIndex d (r+1) = fdRationalReturnIndex d r + d + 1`.
  Thus its successor is `(r+1)*(d+1)`: the successor-indexed block count and
  period cover every positive multiple. Using this recursion makes the first
  block literally the original period and avoids unnecessary predecessor casts.
- `fdRationalReturnFibre` is exactly the dependency's
  `LocalFrobeniusTransport.rationalFibre = rationalDerivedPullback z ⋙
  pointRationalFibre`, so it is J, not an arbitrary fibre functor.
  `fdRationalReturnPullback n` specializes the published rational pullback to
  `localPositivePower g_Y n`. The power-composition comparisons identify this
  presentation with repeated G. No alternate rationalized category is used.
- `fdRationalReturn_multiple` deduces each positive-multiple return from w.
  `fdRationalReturnTransport d r` specializes the dependency's
  `LocalFrobeniusTransport.rationalTransport` to that return, with the same C.
  This is the specified sequence of normalized point transports and the actual
  return-square comparison. It is defined for every underlying rational
  constructible object N, without any Weil structure on N.
- `fdRationalReturnBlockComparison` is the actual C-compositor after the scheme
  equality `fdRationalReturn_blockPower`; its endpoints are pullback along the
  (r+2)-block power and the d+1 pullback of the (r+1)-block pullback. This is the
  associative identification suppressed in the displayed paper formula.
- The first main conjunct quantifies over every N and `r : ℕ` and says
  `t_(r+2) = t_(r+1) ≫ t_1(at G^((r+1)(d+1))N) ≫ J(blockComparison.inv)`.
  This is exactly `t_((r+1)d)=t_(d,G^(rd)N) t_(rd,N)` in the paper's positive
  indexing, with the endpoint comparison explicit. No naturality clause or
  extra property beyond the node's conclusion is added.
- `M : sfWeilComplex ... E.val` is the recorded category of pairs
  `(M,theta : G M ≅ M)`, not the derived category of integral Weil objects.
  `fdRationalReturnOperator` is the normalized transport followed by J of
  `(localWeilIterate ... M index).hom`, exactly R_j in the source convention.
- The second conjunct is `R_(r+2) = R_1 * R_(r+1)` for all M and r.
  Mathlib's `End` multiplication is reverse categorical composition, so this
  is precisely `R_((r+1)d) = R_d R_(rd)` with the stated order.
- The third conjunct is `R_(e+1) = R_1 ^ (e+1)` for all M and `e : ℕ`.
  This covers exactly the positive e in `R_(ed)=R_d^e`.
- The final conjunct quantifies over every Weil complex, closed point
  `x : {x // x ∈ closedPoints Y₀.left}`, residue embedding `ι` and its base-field
  compatibility `hι`. The antecedents
  `localClosedPointDegree D Y₀ x = d+1` and
  `z.left = localClosedPoint D Y₀ x ι hι` express exactly that the chosen point
  lies above x with the indicated degree. For every `j : ℤ`, the map under
  `DerivedCategory.coefficientFdCohomology E.val j` is identified with the actual
  `localClosedFrobeniusCohomology ... x ι hι j`. `HEq` accommodates the propositionally
  equal point and degree endpoints; after substituting the two antecedents it
  is ordinary equality of the specified linear operators. It imposes no
  arbitrary comparison or mere existence of a conjugacy.
- All values and equations are in the published raw rationalized constructible
  category and the published bounded finite-dimensional derived point category.
  There is no stable integral Weil lattice, perfectness, finite Tor-amplitude
  of reductions, or idempotent-completion hypothesis anywhere in the signature.

Dependency declarations read and used:

- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`, its
  `rationalDerivedPullback_existsUnique` object/pure-tensor normalization, and
  the underlying `constructibleIntegralPullback`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`, with its actual
  target and the unique extension of the integral sections functor.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, `IntegralComparisonRealizationCoherence` and the
  specified integral composition families. Its realization theorem supplies
  the stipulated coherent comparison framework.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`, with the fixed geometric field action.
- `Sheaf.Paper.LocalFrobeniusTransportNormalization`:
  `LocalFrobeniusTransport.rationalFibre`, `rationalTransport`,
  `rationalComposition`, and the positive-power convention `positivePower_eq`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`,
  `sfWeilFrobeniusPullback`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`, `localWeilIterate`,
  `localClosedPoint`, `localClosedPointDegree`,
  `localClosedFrobeniusCohomology`, and the cohomology functor they use.
- Proof-only import `Sheaf.Paper.IteratedReturnTransportScalarCalculus`:
  `IteratedReturnTransport.rationalReturn`, `rationalI`, `rationalTransport`,
  and the naturality assertion `iteratedReturnTransportScalarCalculus`.
  The direct-composite and repeated-one-step presentations are related by the
  specified power compositors already defined in that module. No import cycle.

Edge cases checked before writing: d=0 means paper degree 1; r=0 means the
first nontrivial block-composition equation (second versus two first blocks);
e=0 means the power-one equality. The index recursion covers all positive
periods/counts with no n=0 case added or lost. The zero complex and every
negative cohomological degree are included; no nonzero or heart assumption is
used. The empty scheme is permitted (there is then no geometric point z and
no closed point). General rational Weil structures with no stable integral
lattice remain allowed. The closed-point condition is conditional as in the
node, while the first three conclusions apply to every supplied periodic
geometric k-point, without a closed-point assumption.

Searches for an existing declaration (all via the prescribed tools):

- LeanFinder, “Block composition of geometric point Frobenius transports for
  rational Weil complexes gives powers of the first return operator”: 8 hits,
  including `iterateFrobeniusEquiv_add`, `iterateFrobeniusEquiv_symm_add`,
  purely inseparable iterations and Witt-vector Frobenius; none concerns the
  specified point return in rational constructible derived categories.
- Loogle, `"Frobenius", "pow"`: 12 hits, including
  `iterateFrobenius_eq_pow`, `FiniteField.frobenius_pow`, field Frobenius and
  polynomial-expand lemmas. None states these transport or Weil-operator laws.
- Mathlib grep, `return.*[Ff]robenius|[Ff]robenius.*return|point.*transport`:
  two affine-space comments, no matching declaration.
- LeanSearch, “Repeated return maps at a geometric point for a rational Weil
  complex are powers of the first local Frobenius”: 8 ring-Frobenius hits,
  including `LinearMap.frobenius` and `iterateFrobeniusEquiv_eq_pow`, no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for return/block and
  rational/power names, plus the exact blueprint id in upstream sources:
  no existing declaration of this node. The relevant hits are the already
  cited iterated-return calculus and local normalization; the parent
  `WeilPullbackLocalFrobenius` only describes this block calculation inside its
  proof docstring and states a different pullback theorem. Its declaration is
  not an existing match. The chosen new declaration names have no prior hits.

Validation: required `scompile.py Q13 lem-fd-rational-return-block-power` checked
this single module against the live server library. Both sandbox and library
modes passed (10.4 s and 8.1 s), without errors or non-sorry warnings. The initial
elaboration issue was repaired with explicit helper result types and the
recursive positive block index, without raising time or heartbeat limits.
No statement dispute or node fault was found.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
