## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleBaseChangeInertiaSquare` states
`AlgebraicGeometry.etale_baseChange_inertia_square`, with its sole proof `sorry`.
Its five auxiliary definitions give the specified action over the fixed ring, its
restriction to inertia, the right horizontal ring map, a transparent conjunction
of the assertions, and the canonical localization map. They contain real terms;
there are no postponed construction proofs, extra assumptions, new nodes or
repairs to dependencies. The node is unchanged except for `lean`.

Read the complete node and all five statement dependencies, their Lean records or
Mathlib matches, and the recorded declarations in the pinned source. Also read
all proof-dependency records. The mathematical source is
`literature/stacks-project/pione.tex`, labels `lemma-inertia-base-change` (0BSS)
and `lemma-inertia-invariants-etale` (0BST), especially lines 2636--2706.
The current blueprint's `rem-dl-a1-conventions` was read in
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-lem-wft-curve-heart/`:
its unramified-at-infinity equivalence is the ancestor served here.

Hypotheses and conclusions, clause by clause:

- Finite group: `(G : Type v) [Group G] [Finite G]`; no faithful-action assumption.
  Commutative ring and action: `(R : Type u) [CommRing R] [MulSemiringAction G R]`.
  `A` is literally `FixedPoints.subring R G`. The endomorphism family
  `inertiaSquareAction` is `MulSemiringAction.toAlgHom A R`, so it introduces no
  auxiliary action. The fixed-ring scalar commutation instance is already in
  Mathlib's `Subalgebra.Operations`.
- Prime `q`: `(q : Ideal R) [q.IsPrime]`. Its inertia is the existing
  `q.inertia G`, whose definition is the difference condition, not a private copy.
  For finite G that condition implies preservation of q (iterate the finite-order
  automorphism); identity on R/q is equivalent to identity on Frac(R/q), since the
  quotient embeds in its fraction field and generates that field by fractions.
- Etale A-algebra: `(B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]`.
  This is the allowed ring-level presentation of the recorded scheme notion;
  `HasRingHomProperty @Etale RingHom.Etale` and `RingHom.etale_algebraMap` give
  the affine equivalence. The bottom scheme arrow is also explicitly asserted etale.
- S is exactly `B ⊗[A] R`. `AlgHom.baseChangeFamily B (inertiaSquareAction G R)`
  is the canonical endomorphism `id tensor g`, sending b tensor r to b tensor g(r).
  Q is an ideal of this tensor ring with `[Q.IsPrime]`; `hQ` says its comap along
  `Algebra.TensorProduct.includeRight.toRingHom` equals q.
- Equality of inertia subgroups of the given G is expressed elementwise in the
  first conjunct of `InertiaSquareAssertions`: for every g, the difference
  condition on all s in S is equivalent to membership in `q.inertia G`. The
  tensor family consists of automorphisms with inverses indexed by g inverse,
  so this is exactly the same inertia criterion, not just prime stabilization.
- Full invariants: the first existential is a B-algebra equivalence
  `B ≃ₐ[B] AlgHom.fixedPoints (AlgHom.baseChangeFamily B ...)`.
  Any such B-algebra equivalence has underlying map the canonical `algebraMap`;
  the existential therefore asserts invertibility of precisely B -> S^G.
- Inertia invariants: `inertiaSquareRestrictedAction` restricts the original
  family to `q.inertia G`. Its fixed-point subalgebra is R^I with its canonical
  A-algebra structure. The second existential `e` is a B-algebra equivalence
  `B ⊗[A] R^I ≃ₐ[B] S^I`; its value after inclusion in S is explicitly prescribed
  for EVERY b and x as b tensor x. Thus the equivalence is the canonical map,
  not an arbitrary comparison.
- Cartesian square: `IsPullback` uses top arrow Spec of `inertiaSquareRightMap`,
  which is `e` composed with `includeRight`, left arrow Spec of B -> S^I,
  right arrow Spec of A -> R^I, and bottom arrow Spec of A -> B.
  All vertices are the actual fixed-point algebras. Both horizontal arrows have
  explicit `Etale` conjuncts.
- Point assertion: the last conjunct of `InertiaSquareAssertions` is comap of
  the contracted ideal Q cap S^I along R^I -> S^I equals q cap R^I. Since these
  contracted ideals are prime, this is exactly the assertion about the point
  under the spectrum map, without introducing an arbitrary point.
- Every principal localization: the outer universal quantifier ranges over ALL
  b in B whose image under B -> S is outside Q. This is precisely
  b not in Q cap B. The scalar ring is literally `Localization.Away b`.
  `inertiaSquareLocalizationMap` is the tensor of the structural map B -> B_b
  with the identity of R. The local ring is represented by `B_b ⊗[A] R`.
  The displayed existential ring equivalence from the literal `S_b` is pinned
  on EVERY original s by `e (algebraMap _ _ s) = inertiaSquareLocalizationMap ... s`.
  Localization's universal property makes this equivalence unique, and the
  transported G-action is therefore the canonical action fixing b. This is the
  standard fraction identification in proof step 6, not an arbitrary map.
  The extended prime is literally `Ideal.map ... Q`; its primeness and contraction
  to q are asserted before the same full `InertiaSquareAssertions` conjunction
  is repeated over B_b. Thus EVERY assertion, including both etale arrows and
  the point map, is retained after localization; the literal Q S_b transports
  to this prime under the pinned equivalence.
- There is no `[Module.Finite A R]`, division by |G|, characteristic restriction,
  Noetherian assumption, faithful-flatness assumption, or nontriviality assumption.
  The group universe v is independent of the ring universe u. Rings and their
  spectra use the common scheme universe u, the usual convention of `Spec`.

Dependency declarations used:

- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`; ring input `Algebra.Etale`, affine bridge as above.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` from
  `Mathlib.LinearAlgebra.TensorProduct.Defs` and its existing algebra structure,
  `Algebra.TensorProduct.includeRight` and `Algebra.TensorProduct.map`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its universal
  property, expressed by the equivalent `CategoryTheory.IsPullback` predicate on
  the specified square. `Mathlib.AlgebraicGeometry.Pullbacks` supplies pullbacks
  of schemes and `AlgebraicGeometry.pullbackSpecIso` with both projection formulas.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`, used directly on every canonical ring map.
- `def-weil-ring-localization-away`: `Localization.Away` from
  `Mathlib.GroupTheory.MonoidLocalization.Away`, with its ring structure and
  structural algebra maps from `Mathlib.RingTheory.Localization.Away.Basic`.
- `lem-dl-a1-flat-base-change-finite-invariants`: the record's audit resolves
  to `WeilConjectures.Mathlib.RingTheory.TotallySplit`,
  `AlgHom.tensorFixedPointsEquiv` and `AlgHom.coe_tensorFixedPointsEquiv_tmul`.
  Its already defined `AlgHom.fixedPoints` and `AlgHom.baseChangeFamily` are
  reused for the statement. No duplicate invariant-ring construction is made.
- Proof imports also provide `Algebra.Smooth.flat` from
  `Mathlib.RingTheory.Smooth.Flat`, the Etale base-change instance from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, localization etaleness from
  `Mathlib.RingTheory.Etale.Basic`, and localization/tensor comparison tools from
  `Mathlib.RingTheory.Localization.BaseChange`. Every proof dependency with an
  available declaration is covered by these imports; no import cycle is used.

Edge cases checked against the source and signature: trivial G; nonfaithful
G-action; I trivial or I=G; group order noninvertible and positive characteristic;
R not finite over A; B zero (no prime Q, so the quantified statement is vacuous);
b=1 (identity localization); b=0 excluded by the avoidance condition; zero divisors
in R or B (no fraction field of the whole ring is used); arbitrary nonmaximal
primes; and non-faithfully-flat etale B. The normalization formulas do not require
injectivity of A -> B or R -> S. No statement correction or dispute was found.

Searches actually run on 2026-10-24:

1. `msearch.py ... leanfinder`, query: `Etale scalar extension of a finite group
   action preserves inertia groups and gives a cartesian square of invariant
   subrings`. Eight hits on inertia degrees/Galois groups/Frobenius; none is this
   combined arbitrary-ring inertia and invariant-square statement.
2. `msearch.py ... loogle`, query `Ideal.inertia, TensorProduct`: zero hits.
3. `msearch.py ... grep`, query
   `inertia.*(baseChange|tensor)|fixedPoints.*baseChange`: zero hits.
4. `rg` in Mathlib for `inertia`, `fixedRing`, `FixedPoints.subring`,
   `MulSemiringAction.toAlgHom`, tensor maps and localization comparisons found
   the background definitions used, including the difference criterion and
   the fixed-ring scalar commutation instance, but no exact combined theorem.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for inertia, tensorFixedPoints,
   base-change invariants and fixed subrings located the exact upstream flat
   invariants comparison and the parent module `FiniteGroupInertiaInvariantsEtale`.
   The parent concludes etaleness of R^G -> R^I near q, not this scalar square.
6. Searching the exact item id in both project source trees found no declaration.

Compilation: prescribed `scompile.py` compiles sandbox and library forms cleanly.
The first pass found that `inertiaSquareRightMap` needed `noncomputable` because
its type uses the upstream noncomputable tensor family; this was fixed. The next
pass passed both forms (10.2 s and 8.9 s). Only the named main theorem is postponed.

## Second reading by Q40

This is the same worker's separate consistency pass: the dispatcher explicitly
prohibits starting other agents. The maintainer supplies the independent review.
Reopened the node and the final module and checked the hypothesis/clause mapping
above. The two equivalences are pinned as canonical maps (the first by its
B-algebra structure, the second by all pure tensors); the square has the correct
orientation; comap has the correct direction for the asserted image of the point;
and localization repeats the full conjunction instead of only inertia equality.
The localized ideal is an actual extension, not an arbitrarily selected prime.
The comparison with literal S_b is pinned on all original elements, so neither
the prime nor the action is silently changed. All helper definitions reuse the
existing fixed-point construction, and all declarations carry the item's source
and blueprint tag. The only implementation change during checking was the
`noncomputable` annotation noted above; no mathematical statement changed.
