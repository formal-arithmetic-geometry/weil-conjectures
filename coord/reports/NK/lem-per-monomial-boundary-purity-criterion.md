## Worker report

`Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion` states
`AlgebraicGeometry.Etale.monomial_boundary_purity_criterion` with proof `sorry`.
Its three helpers construct the actual coordinate quotient, its spectrum map,
and the closed-immersion instance from Mathlib's surjective-quotient construction.
Punctual purity and the canonical supported class are reused from the landed
`def-per-punctual-purity`, not defined again.

Hypothesis and clause correspondence:

* `(ℓ : ℕ) (hℓ : ℓ.Prime)` fixes the prime. The published map uses
  `regularClassCoefficients ℓ 1 = ULift (ZMod (ℓ ^ 1))`, exactly F_ℓ in the
  required coefficient universe. There is no extra coefficient assumption.
* The opening definition of punctual purity is `IsPunctuallyPure ℓ hℓ W`
  from `Sheaf.AlgebraicGeometry.PunctualPurity`. It means purity at every
  ordinary point, using `IsPunctuallyPureAt`. That predicate uses the actual
  local stalk, `Spec.map (W.residue w)`, and a natural dimension `d` with
  `ringKrullDim (W.presheaf.stalk w) = (d : WithBot ℕ∞)`.
  Its Noetherian, regular-immersion and coefficient-unit witnesses allow the
  existing class map to be evaluated; for regular Noetherian W with ℓ
  invertible they add no geometric assumption.
* `punctualPurityClassMap ℓ hℓ i c hi hInv` is the published level-one,
  untensored Kummer class transposed through the D+ closed-support adjunction.
  It is the map A_Z -> i^! A_X(c)[2c], with the fixed positive Cartier Kummer
  normalization. The fully faithful inclusion D+ -> D preserves and reflects
  isomorphisms, so this renders the node's ordinary small-etale derived map.
  It uses `regularImmersionClasses`, the unique family selected by
  `(regular_immersion_class_calculus ℓ hℓ).exists.choose`.
* A trait is `(R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R]`, `hdim : ringKrullDim R = 1`, and
  `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`. These say precisely
  Noetherian local domain of dimension one with the given uniformizer.
  `hℓR : IsUnit (ℓ : R)` renders coefficient invertibility.
* `n : ℕ`, `hn : 1 ≤ n`, `a : Fin n → ℕ`, and `ha : ∃ i, a i ≠ 0`
  say n≥1 and nonnegative exponents not all zero. There is no prime-to-ℓ
  restriction on any exponent.
* V is literally `Spec (.of (monomialTraitAlgebra R π n a))`. This existing
  algebra is `MvPolynomial (Fin n) R` modulo the product-minus-π relation.
  Its owning definition node is `def-per-monomial-trait-model`; its module
  remains `Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart`.
  The chart theorem is not used as a statement dependency.
* `hregular : IsRegularScheme (Spec (.of (monomialTraitAlgebra R π n a)))`
  is exactly regularity of V. Polynomial and quotient instances give its
  Noetherianity from R, without an additional theorem hypothesis.
* `monomialBoundaryAlgebra R π n a i` is B/(T_i), with T_i the image of the
  actual polynomial variable. `monomialBoundaryInclusion` is the spectrum of
  the canonical quotient homomorphism. Its instance is the direct application
  of `IsClosedImmersion.spec_of_surjective` to `Ideal.Quotient.mk_surjective`.
* The conclusion is `IsPunctuallyPure ... V ↔ ∀ i, 0 < a i → ...`.
  On the right the witnesses are the codimension-one regular closed immersion
  and invertibility of ℓ on V; the assertion is
  `IsIso (punctualPurityClassMap ℓ hℓ (monomialBoundaryInclusion ...) 1 hreg hunit)`.
  Thus the displayed map is precisely A_H_i -> h_i^! A_V(1)[2].
  The witnesses are existential conclusions, not additional theorem hypotheses.
  The divisor is effective Cartier since its single generator T_i is a
  nonzerodivisor in this regular trait model. No condition is asserted for a_i=0.

Dependency declarations read and used:

* `def-per-punctual-purity`: `Sheaf.AlgebraicGeometry.PunctualPurity`,
  `AlgebraicGeometry.Etale.IsPunctuallyPure`, `IsPunctuallyPureAt`, and
  `punctualPurityClassMap` (including their full signatures and docstrings).
* `def-per-monomial-trait-model`: existing `AlgebraicGeometry.monomialTraitAlgebra`
  in `Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart`.
* `lem-per-regular-immersion-class-calculus`:
  `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`,
  `regularClassCoefficients`, `regularClassTwist`, `RegularImmersionClassFamily`,
  and `regular_immersion_class_calculus`; these fix the normalized class family
  selected by the punctual-purity module.
* `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme`, the locally Noetherian stalkwise predicate.
* `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`, the ordinary small-etale
  derived categories; this current source was read through `scompile.py --source`
  because it is absent in the older local checkout.
* `def-asd-finite-etale-tate-twist`:
  `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`,
  `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`, used by the published class map.
* `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField` and `Scheme.residue`, used by the published point predicate.
* `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
* `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, valued in `WithBot ℕ∞`.
* `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`.

Proof-only imports retain `RegularLCIGeometricCalculus`, upstream affine-space
smoothness, and Mathlib finite-type infrastructure. The proof dependencies
`lem-per-prime-field-punctual-purity` and `lem-per-punctual-purity-two-of-three`
still have no recorded Lean module, so no import for them is invented.

Edge cases: n=1 gives H=Spec(R/(π)); exponent-zero variables remain free and
are not tested on the right. The all-zero family and n=0 are excluded by exactly
ha and hn. No smoothness of the generic fibre over Frac(R) is assumed. At a
generic point the punctual predicate includes d=0 and the class family's
codimension-zero identity. On the empty scheme the all-points predicate is
vacuous. Dimension one and the domain/local hypotheses exclude fields, the
zero ring, and π=0. The scheme universe u remains arbitrary, with coefficients
in u+1 as required by the ordinary small-etale API.

Source: retained source reading of ILO XVI Definitions 3.2.1--3.2.2,
Proposition 3.2.3 (printed p.244), and Lemma 3.5.13(iv) and proof (printed p.251).
The six-step theorem docstring is preserved. No source statement is corrected.
The class-calculus dependency's existing uniqueness dispute remains its own
proof obligation; this delivery makes no additional statement dispute.

Searches retained in searches.jsonl: msearch grep `punctual.*pur|monomial.*pur|Kummer`
found no Mathlib algebraic-geometry match; Loogle `"Kummer"` returned field/ideal
Kummer declarations; LeanFinder's monomial boundary purity criterion query
returned Weierstrass and standard-etale infrastructure, not this criterion;
LeanSearch's punctual cohomological purity query returned local closed-point
and residue declarations. Repeated LeanFinder and grep searches found no
criterion. A later Loogle request was unavailable; the earlier successful
request remains recorded. Direct rg of upstream, side sources and the upstream
name index found no criterion declaration. On repair, direct rg of the current
side library found the landed `IsPunctuallyPure` and `punctualPurityClassMap`
in PunctualPurity.lean, and their complete implementations were read and reused.
Upstream punctual purity of Weil weights is a different notion. The retained
monomial algebra search is resolved by its landed definition owner.

## Returned points repaired

1. H4/H12: deleted `regularKummerClasses`, `regularKummerPurityMap`,
   `IsPunctuallyKummerPureAt`, and `IsPunctuallyKummerPure`. The theorem now
   uses the landed `IsPunctuallyPure` and `punctualPurityClassMap`, publicly
   imports PunctualPurity, and cites `def-per-punctual-purity` in stmt_deps.
2. F2/H2: replaced the saved packet's chart-theorem stmt_dep by
   `def-per-monomial-trait-model`. The module import remains the recorded
   location of its existing monomialTraitAlgebra declaration.
3. H13/H2: removed the EtaleFiniteTwistPullback sibling module, removed its
   dependency node copy, and removed `lem-asd-etale-finite-twist-pullback`
   from the packet's stmt_deps. Its published record is untouched. No
   unrelated source is republished for compiler-cache purposes.

The node copy was rebased from the current shared node without direct Git
operations. Relative to that base, only lean and the addition of the two
landed definition dependencies change; statement, proof, proof_deps and all
other fields remain verbatim. There are no new nodes or dependency modules.

## Second reading by NK

This is the dispatched author's separate self-reading; no second agent was
started, as required by this repair brief. The maintainer supplies independent
review. I reopened the repaired module and item node, and the landed
PunctualPurity and monomial-model records. The coefficient prime, trait binders,
n≥1, nonzero exponent family and regularity of exactly V are preserved.
The left side now uses the shared all-points predicate, and the right uses
the shared D+ class map at c=1 for the literal B/(T_i) quotient inclusion.
Both maps use the same unique normalized supported Kummer family; the
fully faithful D+ inclusion justifies the ordinary derived formulation.
The existential regular-immersion/unit witnesses remain in the conclusion,
no exponent-zero divisor is required, and the d=0 case remains included.
I checked all four duplicate declarations and the finite-Tate sibling/record
are absent. The only added stmt_deps own definitions actually used. The
class-calculus dependency remains because it fixes the selected class family.
The theorem signature is extracted verbatim from the repaired file into lean.

Validation: the initial required dry run of the saved packet failed by a
60-second timeout in RegularImmersionClassCalculus, locally and in server
confirmation. After the three interface repairs, `scompile.py NK
lem-per-monomial-boundary-purity-criterion <MonomialBoundaryPurityCriterion.lean>`
completed cleanly: sandbox 8.6 seconds, library 8.4 seconds, no compiler
messages or warnings. Final preflight/delivery results are recorded below.

Final self-check: only lean and stmt_deps differ from the current node;
stmt_deps gains exactly def-per-punctual-purity and def-per-monomial-trait-model.
The signature matches verbatim, all Lean lines are at most 100 characters,
and the one theorem has the only sorry. The packet has exactly one module
and one node file. deliver2.py --no-push returned OK at 0b1a360ba9: preflight
and compilation pass; exactly the module, item node and report are staged.
