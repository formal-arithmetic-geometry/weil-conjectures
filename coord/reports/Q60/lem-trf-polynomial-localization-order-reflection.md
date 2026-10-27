## Worker report

The module `Sheaf.RingTheory.PolynomialLocalizationOrderReflection` states
`Hironaka.polynomialLocalization_orderReflection`, with one postponed theorem
and no new definition. Its proof is `sorry`, as required at stage 2.

Hypothesis and clause comparison:

- The nonzero commutative Noetherian regular local base is `(R : Type u)
  [CommRing R] [IsRegularLocalRing R]`. The regular-local class extends
  `IsNoetherianRing` and `IsLocalRing`; the latter extends `Nontrivial`, so
  the nonzero, Noetherian and local hypotheses are all present without
  adding redundant instance arguments.
- The nonnegative number of variables is `(s : ℕ)` and the polynomial ring
  is `MvPolynomial (Fin s) R`. This includes `s = 0`.
- The prime is `(q : Ideal (MvPolynomial (Fin s) R)) [q.IsPrime]`.
  The hypothesis `hq` is exactly contraction along the coefficient inclusion:
  `q.comap (algebraMap R (MvPolynomial (Fin s) R)) =
  IsLocalRing.maximalIdeal R`.
- The ring S is literally `Localization.AtPrime q`, and the natural map j
  is `algebraMap R (Localization.AtPrime q)`, with the canonical polynomial
  and localization algebra tower. No arbitrary algebra map is supplied.
- The ideal n is literally `q.map (algebraMap (MvPolynomial (Fin s) R)
  (Localization.AtPrime q))`. The existing theorem
  `Localization.AtPrime.map_eq_maximalIdeal` identifies this with the maximal
  ideal upstairs. No claim that n equals the extended base maximal ideal
  is made; the closed fibre can have positive dimension.
- The first conjunct is `IsRegularLocalRing (Localization.AtPrime q)`.
- The next conjunct is `∀ a : ℕ, (n ^ a).comap j =
  IsLocalRing.maximalIdeal R ^ a`, using the explicit terms for n and j.
- The last conjunct is `∀ r : R, adicOrder n (j r) =
  adicOrder (IsLocalRing.maximalIdeal R) r`. The reused `Hironaka.adicOrder`
  is the supremum in `ℕ∞` over precisely the natural n with membership
  in the n-th ideal power. The order equality is thus the node's stated
  consequence, including infinite order.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (abbreviation
  for `IsNoetherian R R`, equivalently every ideal finitely generated).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the
  unchanged ring clause of `def-weil-regular-scheme.mathlib_match`.
  The recorded module `Sheaf.AlgebraicGeometry.IsRegularScheme` is also
  imported publicly; its scheme predicate is unnecessary in this ring statement.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, with its canonical
  coefficient algebra map. Also read `MvPolynomial.algHom_ext` there and
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  and `Localization.AtPrime.map_eq_maximalIdeal`. The residue-field and fibre
  signatures recorded on this node were read in `LocalRing.ResidueField.Ideal`
  and `LocalRing.ResidueField.Fiber`.
- `Sheaf.RingTheory.LocalStandardBasisInvariants`: `Hironaka.adicOrder`.
  Its owning, already landed node `def-trf-local-standard-basis-invariants`
  is added to `stmt_deps`, as authorized for citing existing landed notions.
  It defines the exact order used here; no new order notion is introduced.

Every already recorded proof dependency has its available module imported
privately, except those already imported publicly for statement dependencies.
Mathlib matches supply the finite-type Noetherian, localization Noetherian,
flat-height, quotient-localization, regular-polynomial, cotangent-dimension,
stalk-localization and free-symmetric-algebra inputs. The recorded regularity
ascent module is `WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber`
(`IsRegularLocalRing.of_flat_of_regular_closedFiber`). The associated graded
ring and universal property use their recorded modules. The graded cotangent
criterion `lem-sfb-regular-local-graded-cotangent-criterion` currently has no
recorded module or Mathlib match, so no import exists for it; it remains named
in the proof docstring and does not occur in the theorem's signature.

The theorem docstring gives all six DAG proof steps, including the identification
of the actual induced graded map and the induction on ideal powers. Source read:
`literature/stacks-project/algebra.tex`, lemma-flat-over-regular-with-regular-fibre
(Tag 031E, parameter-generating proof) and lemma-regular-graded (Tag 00NO,
canonical graded polynomial map). The latest blueprint locality node was also
read; this ancillary algebra node retains its historical source provenance,
without changing that unit's current contracting-correspondence statement.

Edge cases checked mathematically before writing:

- At `a = 0`, both ideals are top, including when the variable list is empty.
- At `s = 0`, the only prime contracting to the maximal ideal is that maximal
  ideal under the empty-polynomial identification, and its localization is R.
- At `r = 0`, every power contains the element; both suprema are infinity.
- A field base has maximal ideal zero: nonzero constants remain units upstairs,
  with order zero, while zero retains infinite order.
- For a DVR base, primes equal to the extended maximal ideal give a
  zero-dimensional closed fibre; primes with extra variable conditions give
  a positive-dimensional fibre. Both retain the base parameter order.
- No residue separability or characteristic hypothesis is added, and the
  regular-local class excludes the zero ring as the node requires.

Searches (all on 2026-10-24):

1. `msearch.py ... leanfinder "Polynomial localization over a regular local
   ring reflects powers of the maximal ideal and preserves maximal ideal orders"`:
   eight hits, including localization maximal-ideal identifications and regular
   sequences; none states contraction of powers or equality of adic orders.
2. `msearch.py ... loogle '"maximalIdeal", "comap", "pow"'`:
   zero hits.
3. `msearch.py ... grep 'order|comap.*pow|pow.*comap'
   RingTheory/RegularLocalRing`: zero hits.
4. `msearch.py ... leansearch "Polynomial localization over a regular local
   ring preserves maximal ideal adic order"`: eight hits on ordinary
   localization/maximal-ideal results, no order-reflection theorem.
5. Direct `rg` across `lean/WeilConjectures` and `lean/Sheaf` for the node id,
   polynomial order, `idealOrder`, `Ideal.order`, and `adicOrder` found the
   existing `Hironaka.adicOrder` and its consumers. The only mention of this
   exact lemma was in a consumer proof docstring, with no declaration.
   `grep -rn` for the exact node id in upstream returned no match.
6. Mathlib ideal-directory search for order definitions and suprema of powers
   found no general ideal-adic order. Read regular-local polynomial results:
   `Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal`
   gives regularity only, not this theorem's contraction and order clauses.
7. Checked the proposed declaration name against Mathlib, upstream names JSON,
   `WeilConjectures`, and `Sheaf`: no collision.

No statement correction, new nodes, dependency repair modules, or
STATEMENT-DISPUTED issue is needed. Only `lean` and the addition of the existing
order-definition owner in `stmt_deps` change in the item node.

Validation: the prescribed `scompile.py` compiled the sandbox and library
module cleanly (1.7 s and 1.8 s), with no errors or non-sorry warnings.

## Second reading by Q60

Self-check of the finished source against the node: the theorem uses the
specified polynomial localization, prime contraction, explicit extension qS,
every natural power, and the existing supremum definition of order. Every
hypothesis and conjunct matches the comparison above. The proof is the single
required `sorry`; there are no hidden hypotheses, auto-bound variables or
local notations. No mismatch was found. This is explicitly a self-check,
not an independent agent review: the dispatcher forbids starting other agents;
the maintainer supplies the independent delivery review.
