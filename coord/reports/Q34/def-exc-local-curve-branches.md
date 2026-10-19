## Worker report

The module `lean/Sheaf/AlgebraicGeometry/LocalCurveBranches.lean` defines the branch index as the subtype of minimal primes of the zero ideal, the quotient rings, their fraction rings, and the integral-closure factors. It then defines `excLocalCurveQ` and `excLocalCurveB` as the coordinatewise products, together with the canonical structural map `excLocalCurveBAlgebraMap`.

The hypotheses are rendered by `[CommRing R]`, `[IsReduced R]`, `[IsLocalRing R]`, `[IsNoetherianRing R]`, and the explicit one-dimensionality equality `_hRdim : ringKrullDim R = (1 : WithBot ℕ∞)`. The minimal-prime clause is the index subtype `{p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes}`. The quotient clause is `R ⧸ p.1`; the fraction-field clause uses `FractionRing`; the integral-closure clause uses `integralClosure` and `Subalgebra.restrictScalars R`; and both products use dependent function types with coordinatewise ring operations. The structural map is `AlgHom.pi` of the quotient-to-fraction-ring maps restricted to the integral closures. The factor map proof uses `mem_integralClosure_iff` and `isIntegral_algebraMap`, so its data is constructive and contains no `sorry`.

Dependency declarations used are `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`, `Mathlib.RingTheory.KrullDimension.Basic.ringKrullDim`, `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian.Ideal.finite_minimalPrimes_of_isNoetherianRing`, `Mathlib.Algebra.Module.LocalizedModule.Basic.LocalizedModule` (the fraction-ring construction is provided by `FractionRing`), `Mathlib.RingTheory.IntegralClosure.Algebra.Basic.integralClosure`, `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization.AlgebraicGeometry.Scheme.normalization`, and `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization.AlgebraicGeometry.Scheme.normalizationIn`. The normalization declarations are imported as required statement dependencies, although the branch-algebra definition itself only needs the integral-closure ingredient.

Edge cases checked: the index subtype permits any finite number of minimal primes, including one; dependent products over an empty index are still defined (the hypotheses and reduced Noetherian assumptions are retained exactly); `FractionRing` is used without imposing an extra domain or nonzero hypothesis; and dimension is an explicit equality, so the zero-dimensional and zero-ring cases are excluded by the node's own one-dimensional hypothesis rather than by an added assumption.

Searches made: the recorded node searches (LeanFinder, LeanSearch, Loogle, and Mathlib/source grep for branch-algebra, minimal-prime, normalization, and fraction-ring products) found no whole-item declaration. I additionally searched `rg -n "minimalPrimes|integralClosure|FractionRing|branchAlgebra|LocalCurve"` in `WeilConjectures/` and `lean/Sheaf`; only the individual Mathlib ingredients and unrelated normalization results were found. No existing declaration has the two products and the canonical structural map together.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading of the module and node.

## Second reading by Q34

I independently read the entire sandbox node and module, all seven statement-dependency
nodes, and the actual archived master source at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/def-exc-local-curve-branches.md`
(order 1917). The source is absent from the local literature mirror; I read the server's
read-only copy directly. I also read the unit and chapter section files. This auxiliary
ring definition explicitly has the general ring hypotheses below; it does not require
excellence, a base field, finite type over a field, or a coefficient characteristic from
its surrounding applications. The source and DAG agree, so no statement correction or
citer audit is required. There are no new nodes or dependency modules in this delivery.

The complete object/hypothesis/clause checklist is:

| Node item | Lean rendering and verdict |
| --- | --- |
| A commutative ring R | `(R : Type u) [CommRing R]`; exact, arbitrary universe. |
| Reduced | `[IsReduced R]`; exactly absence of nonzero nilpotents. |
| Local | `[IsLocalRing R]`; unique maximal ideal, including nontriviality already forced by dimension one. |
| Noetherian | `[IsNoetherianRing R]`; the recorded dependency, equivalent to every ideal being finitely generated. |
| Dimension exactly one | `_hRdim : ringKrullDim R = (1 : WithBot ℕ∞)` on the main structural-map declaration; exact, not merely dimension at most one. |
| All distinct minimal prime ideals | `excLocalCurveBranchIndex R = {p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes}`; each ideal appears once, with primality and minimality in its membership proof. |
| Finitely many indices | Noetherianity gives `Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥`; the exact recorded Mathlib match for `lem-sc-finite-minimal-primes-over-ideal`, not an extra hypothesis or finiteness claim about B. No numbering or Fintype choice is needed for this definition. |
| A_a = R / p_a, a domain | `excLocalCurveBranchQuotient R p := R ⧸ p.1`; the added `excLocalCurveBranchQuotientIsDomain` reuses `Ideal.Quotient.isDomain` with `p.2.isPrime`. |
| K_a = Frac(A_a) | `excLocalCurveBranchFractionRing R p := FractionRing (excLocalCurveBranchQuotient R p)`; the canonical localization at nonzerodivisors, which are exactly the nonzero elements in these domains. The field instance now synthesizes. |
| Integral-closure factor | `(integralClosure A_a K_a).restrictScalars R`; its elements are exactly those integral over A_a. Restricting scalars changes only the algebra structure, not the carrier or ring operations. |
| Q(R) = product K_a | `excLocalCurveQ R := (p : excLocalCurveBranchIndex R) → excLocalCurveBranchFractionRing R p`; dependent product, coordinatewise ring operations. |
| B(R) = product of the integral closures | `excLocalCurveB R := (p : excLocalCurveBranchIndex R) → excLocalCurveBranchIntegralClosure R p`; same index and coordinatewise ring operations. |
| Canonical R-to-factor map | `excLocalCurveBranchAlgebraMap` composes `Ideal.Quotient.mkₐ R p.1` and `IsScalarTower.toAlgHom R A_a K_a`, then restricts the codomain to the integral closure using `isIntegral_algebraMap`; its value is the image of r modulo p_a, not an arbitrary map. |
| R-to-B map and R-algebra structure | `excLocalCurveBAlgebraMap := AlgHom.pi (fun p => excLocalCurveBranchAlgebraMap R p)`; its coordinates are the specified maps and the inherited `Pi.algebra` structure has this structural map. |
| No assumed finiteness or local-factor decomposition | There is no `Module.Finite`, semilocality, DVR, or product-of-local-rings hypothesis/conclusion. Exact. |

I opened the recorded Mathlib signatures and definitions of `IsNoetherianRing`,
`ringKrullDim`, `Ideal.minimalPrimes`,
`Ideal.finite_minimalPrimes_of_isNoetherianRing`, `FractionRing` and its field instance,
`Ideal.Quotient.isDomain`, and `integralClosure`. The recorded module-localization
notion is `LocalizedModule` (localization at a submonoid); the ring localization
specialization used here is Mathlib's `FractionRing = Localization (nonZeroDivisors _)`.
The `Scheme.normalization`, `Scheme.fromNormalization`, `Scheme.normalizationIn`, and
`Scheme.fromNormalizationIn` declarations in
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` were also read: they are the
integral-closure constructions referenced by the node, not a competing definition of
this ring product. All dependency interfaces are usable; no repair under §1(B) is needed.

Edge cases: a one-branch domain gives its ordinary fraction field and integral closure;
a reducible reduced local curve retains every minimal prime, with no domain hypothesis
on R. The empty minimal-prime product is still a legitimate dependent product, although
dimension one rules out the zero ring and an empty spectrum here. A field or another
zero-dimensional local ring does not supply `_hRdim`, exactly as in the source. The
helper constructions make sense more generally; their availability in additional cases
does not restrict or alter the requested dimension-one specialization. No integer n,
coefficient ring, characteristic restriction, scheme, or scheme-size condition enters
this node. Every index, quotient, fraction field, and product remains in the arbitrary
universe u; no independent smaller universe or added universe equality is used.

Independent H4 searches, using words beyond the worker's original queries:

- LeanFinder: `Normalization ring of a reducible affine curve defined componentwise using fraction fields and integral elements, with the diagonal ring homomorphism`.
  Eight results about Weierstrass coordinate rings, their function fields and integral
  models; none defines the product over all minimal primes or this structural map.
- Loogle: `"FractionRing", "minimalPrimes"`; accepted query, zero hits.
- Grep through all Mathlib: `normalization.?[Aa]lgebra|branch.?[Aa]lgebra|integralClosure.*minimalPrimes|minimalPrimes.*integralClosure`;
  zero hits. The same search through `WeilConjectures/` and project `lean/Sheaf/`
  found two descriptive comments in `StalkNormalizationFinite.lean` and
  `FiniteGenericCurveModel.lean`, neither a definition of this branch product.
  The chosen declaration names were also absent from `dag/lean_names_upstream.json`.
- LeanSearch: `The ring of fractions on irreducible components and their integral closures define the normalization algebra of a reduced local ring`;
  service returned Internal Server Error, recorded as unavailable. No absence verdict
  is inferred from this unsuccessful search.

Mismatches and repairs: the original carrier constructions and canonical map already
match the source. However, the minimal-prime membership proof was not exposed to typeclass
inference, so downstream users could not directly synthesize the quotient's domain or
the fraction ring's field structure. I added the named domain instance by applying
Mathlib's existing prime-quotient instance to the stored primality proof; this introduces
no new theorem or postponed proof. Two docstrings misleadingly tied the field property
to reducedness, although primality alone is sufficient; I corrected them. The factor-map
docstring lacked its source and blueprint marker; I supplied both, and added the module's
main-definition list. I retained the correct constructions and hypotheses. The node's
`lean.declarations` now lists the domain instance, and `lean.statement` is copied verbatim
from the main declaration's signature, retaining its line breaks.

Validation: the delivered module compiles without errors or warnings through the required
`scompile.py` wrapper. A separate scratch interface check, also compiled through that
wrapper, successfully synthesizes the quotient domain, fraction field, factor algebra,
product commutative rings, and B(R)'s R-algebra structure. Its axiom queries for the domain
instance and both canonical maps report only `propext`, `Classical.choice`, and
`Quot.sound`; no definition or instance contains `sorry`, no theorem is proved, and
all variables and universes are explicitly bound. The scratch check is not delivered.
