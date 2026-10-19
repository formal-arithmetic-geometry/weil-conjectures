## Worker report

The module `lean/Sheaf/Paper/IteratedWeilCocycle.lean` states
`WeilConjectures.TraceFormulaCoefficientConventions.iterated_weil_cocycle`.
It quantifies over a coefficient convention `T`, a strict Weil complex `K`, and
positive natural numbers `m,n` with witnesses `hm : 1 ≤ m` and `hn : 1 ≤ n`.
The left side is the hom of the specified positive iterate
`T.iteratedWeilIsomorphism K (m + n)`.  The right side first transports the
source along the canonical equality of endomorphism powers and the canonical
constant-coefficient pullback comparison, then applies the `m`-pullback functor
to the `n`-iterate and composes with the `m`-iterate.  The theorem proof is
`sorry`, as required for stage 2.

The Lean rendering of each clause is:

- The strict Weil pair is `K : T.strictWeilComplex`.
- The positive exponents are `(m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)`.
- The iterated Weil maps are `T.iteratedWeilIsomorphism K (m + n) (by omega)`,
  `T.iteratedWeilIsomorphism K n hn`, and `T.iteratedWeilIsomorphism K m hm`.
- The canonical pullback identification is the displayed `eqToIso` built from
  `pow_add` (with the category-endomorphism order represented by
  `pow_add ... n m`) followed by
  `proEtaleConstantRingPullbackComposition ... .symm`.
- The cocycle equality is the displayed equality of morphisms in the derived
  category, with `Functor.map` implementing `Lg_γ^{m*}`.

Dependency declarations read and used:

- `def-trf-strict-weil-complex`: `Sheaf.Paper.TraceFormulaStrictWeilComplex`,
  declarations `strictWeilComplex` and `strictWeilFrobenius`.
- `def-trf-scheme-frobenius`: `Sheaf.SixFunctors.SchemeFrobenius`,
  declaration `geometricGaloisFrobenius`.
- `def-trf-iterated-weil-map`: `Sheaf.Paper.IteratedWeilMap`,
  declaration `iteratedWeilIsomorphism`.
- `lem-weil-pbc-proetale-derived-pullback-composition`:
  `Sheaf.Paper.IntegralFinitePullbackComposition`, declaration
  `integralTowerGeneralPullbackComposition`; its public imports provide the
  canonical normalized pullback comparison used by
  `proEtaleConstantRingPullbackComposition`.
- Proof-only declarations were also read for the statement's canonical map:
  `AlgebraicGeometry.Scheme.proEtaleCoefficientInverseImageMap_comp`,
  `WeilConjectures.integralFiniteCanonicalPullbackComposition`, and
  `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback_composition_coherence`.

Edge cases checked: `m = n = 1` gives the two-factor composite; `m = 1` or
`n = 1` leaves one block with one factor; `m = n = 2` gives four successive
factors; the positivity witnesses exclude a zero iterate of the Weil map.  The
formula remains well-typed for a zero complex and for an empty scheme, where
all relevant morphisms are the unique ones.  Powers of the geometric Frobenius
are endomorphisms of the same geometric fibre, and the `pow_add` transport uses
`n,m` in the category composition order.

Searches made:

- `msearch.py ... leanfinder "cocycle identity iterated Weil isomorphism pullback composition"`:
  eight generic scheme-pullback cocycle hits, no Weil-complex match.
- `msearch.py ... loogle "proEtaleConstantRingPullbackComposition, iteratedWeilIsomorphism"`:
  no hits; service reported unknown identifier.
- `rg -n "iteratedWeil|cocycle|IteratedWeil"` over the source and project:
  no existing declaration of this item; unrelated cocycle declarations only.
- `rg -n "proEtaleConstantRingPullbackComposition|iteratedWeilIsomorphism"`
  located the recorded canonical comparison and iterated-map declarations.
- Mathlib/source searches for an exact iterated Weil cocycle found no match.

Compilation: `scompile.py NX lem-trf-iterated-weil-cocycle
lean/Sheaf/Paper/IteratedWeilCocycle.lean` passed with no errors or warnings
(the expected `sorry` warning is suppressed by the module option).

A near-match was found in
`WeilConjectures/WeilSheaf/StalkFrobenius.lean:350`,
`AlgebraicGeometry.WeilSheaf.upperStarFactor_hom_app_comp_frobeniusPowStr_add`.
It is a cocycle for the upstream stalk-level `WeilSheaf` construction, with
`upperStarFactor` and lower-star transport, and its hypotheses and coefficient
category differ from the strict derived fixed-pair statement here.  It therefore
does not state this node and is not recorded as `existing: true`.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
