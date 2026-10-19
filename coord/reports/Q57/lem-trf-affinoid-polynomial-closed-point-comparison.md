## Worker report

The module `Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison` defines the actual
polynomial inclusion into Mathlib's restricted-series subring and its quotient map, then
states `RestrictedSeries.affinoid_polynomial_closed_point_comparison` with `sorry`.
No statement correction, disputed statement, new node, or dependency repair is needed.
The only added statement dependency is the already landed
`def-trf-restricted-series-presentation`, whose `RestrictedSeries.constants` is reused.
The other dependency records are unchanged and used directly.

Hypotheses and clauses, with the node and module open:

- The complete real-valued nonarchimedean field is `(F : Type u) [NormedField F]
  [IsUltrametricDist F] [CompleteSpace F]`; `hF : ∃ a : F, a ≠ 0 ∧ ‖a‖ ≠ 1`
  says precisely that the absolute value is nontrivial.
- `n : ℕ` permits zero variables; `MvPolynomial (Fin n) F` is P, and
  `J : Ideal (MvPolynomial (Fin n) F)` is an arbitrary ideal.
- `MvPowerSeries.IsRestricted.subring (fun _ : Fin n ↦ 1)` is the actual ring
  of coefficient families tending to zero in the cofinite filter. At polyradius one,
  this is equivalent to the finite-exceptional-set definition in the node.
  `MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1)` is its Gauss norm.
- `polynomialInclusion` evaluates coefficients through the existing `constants F n`
  and variables through `MvPowerSeries.X`. The proof that each variable is restricted
  is Mathlib's `isRestricted_monomial`; it is not postponed.
- `J.map (polynomialInclusion F n)` is exactly the extended ideal J D.
  B is `MvPolynomial (Fin n) F ⧸ J`; C is the quotient of the restricted-series subring
  by this extended ideal. `polynomialQuotientMap` is Mathlib's `Ideal.quotientMap`
  for this inclusion and extension, using `Ideal.le_comap_map`.
- `∃ N : NormedCommRing D` supplies the Gauss norm structure absent from the library.
  Its `toCommRing` is equated to the existing subring's commutative ring structure,
  and its norm is equated pointwise to the Gauss norm. Consequently the following
  `@IsClosed _ N.toUniformSpace.toTopologicalSpace (J.map ... : Set _)`
  is closedness in precisely the Gauss topology, not the product topology.
- `∃ Q : NormedCommRing C` supplies a norm on the actual algebraic quotient. Its
  `toCommRing` equals the existing quotient ring, and its norm is exactly the infimum
  of the Gauss norms of all representatives (`Ideal.Quotient.mk ... s = c`).
  `@CompleteSpace _ Q.toUniformSpace` is completeness for that quotient norm.
  This is conclusion data, never an extra assumption or a choice from an arbitrary
  existence theorem in a definition.
- `∃ A : @NormedAlgebra F C ... Q.toSeminormedRing` supplies the normed F-algebra
  structure. Its scalar map is fixed pointwise to `mk (constants F n a)`.
  Pointwise equality avoids transporting a bundled homomorphism across the preceding
  equality of ring instances. All operations and scalars are therefore the specified ones.
- `IsNoetherianRing C` uses exactly the dependency's Noetherian-ring predicate.
- For every ideal `m` with `[m.IsMaximal]`, the first conclusion is
  `(m.comap (polynomialQuotientMap F n J)).IsMaximal`: precisely maximality of p.
  Primality needed to type localization already follows from maximality of m and
  contraction; maximality of p is a conclusion, not a hidden assumption.
- The second conclusion provides a ring equivalence between
  `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (Localization.AtPrime p)` and the corresponding completion at m.
  It is tied to `Localization.localRingHom p m (polynomialQuotientMap ...) rfl`
  by the formula for every k, every completed element x and every representative a
  of its kth residue. `AdicCompletion.evalₐ` of `e x` is the residue of the local
  map applied to a. This is the canonical induced map at every finite level, not
  merely an unspecified abstract isomorphism or an equation only on the dense ring.
  Each residue has a representative, so this condition fixes every coordinate and
  determines the isomorphism uniquely. Conversely the canonical completion comparison
  has exactly this formula. Including k=0 adds only the tautological zero quotient,
  and permits the same uniform characterization over all k.

Dependency declarations read and used:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval` and `eval₂Hom`.
  The inclusion uses `eval₂Hom` to avoid installing an unnecessary algebra instance.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`; the recorded residue field/fibre companions are not
  needed in this statement.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `AdicCompletion.evalₐ`, and its ring structure. `IsAdicComplete`, read in the
  dependency record, is not the norm completeness conclusion here.
- `Sheaf.RingTheory.RestrictedSeriesPresentation`: `RestrictedSeries.constants`;
  its imports expose Mathlib's `MvPowerSeries.IsRestricted.subring` and `gaussNorm`.
- The stated proof dependency `Algebra.IsIntegral.of_finite` is imported from
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` with a plain import.
  The two analytic proof-dependency nodes have no Lean record on this base, so
  there are no published modules to import for them. Their uses remain in the
  twelve-step proof docstring. This delivery does not state or prove those nodes.

Edge cases checked: n=0 gives constants and the field (or its zero quotient),
J=top gives C=0 with its complete zero norm and no maximal ideals, J=0 and
proper ideals are unrestricted, and no characteristic, perfectness, separability,
algebraic closedness, or reducedness hypothesis was introduced. A proper J may
also extend to the unit ideal (for example T-a with ‖a‖>1); this is allowed, and
there is no assertion that B→C is injective or has nonzero target. NormedAlgebra
allows the zero algebra. The finite-residue characterization excludes wild
noncontinuous ring isomorphisms between the completions. Universes are explicit,
with arbitrary coefficient universe u; no auto-bound implicit or local notation.

Searches: `msearch.py` LeanFinder query “The polynomial and Tate algebra quotients
have canonically isomorphic completed local rings at maximal ideals” returned eight
formal-power-series Weierstrass quotient results, none the desired analytic theorem.
Loogle query `"IsRestricted"` returned the existing restricted-series predicate,
subring, monomial and related results, which are reused. Its remote search index
mentions `isRestricted_X`, but direct compilation showed that name is absent in the
pinned source; the existing `isRestricted_monomial` supplies the exact certificate.
`msearch.py grep 'TateAlgebra|affinoid|GaussNorm'` returned Gauss-norm modules and
no comparison theorem. Direct `rg` in Mathlib, upstream WeilConjectures and
lean/Sheaf for TateAlgebra, RestrictedSeries, restrictedSeries, GaussNorm and
gaussNorm found the existing `RestrictedSeriesPresentation` module and its consumers;
these were read and reused. Direct upstream item-id search returned no match.
DAG search for restricted series, Tate algebra and Gauss norm found the landed
definition node and analytic theorem nodes; no new notion or duplicate definition
is introduced. Exact searches/results are retained in searches.jsonl.

Source checked: downloaded arXiv 0707.3953v3 into the sandbox and read Theorem 3.5.5
Step 3, printed p. 22. It asserts contraction to a maximal ideal and the isomorphism
of the two completed local rings at a rigid point of the affinoid domain. The item's
polynomial presentation is the supporting comparison expanded by its stage-1 proof,
not the current blueprint unit's own statement. The current `sk-i-curve-zero` proof
was read and is the contracting-correspondence route; this historical analytic
ingredient is retained without changing that route. The twelve-step node proof
is reproduced as natural-language instructions in the theorem docstring.

Validation: `scompile.py Q57 lem-trf-affinoid-polynomial-closed-point-comparison`
compiled this module both as a sandbox and under its final library name, with no
errors or warnings, after correcting explicit normed-structure projections and
using pointwise scalar compatibility. All proofs remain `sorry`; all helper maps
have real data and use Mathlib's universal maps.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
