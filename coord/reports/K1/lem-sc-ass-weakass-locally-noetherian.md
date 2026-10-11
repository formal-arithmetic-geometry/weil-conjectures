## Worker report

The module `Sheaf.AlgebraicGeometry.AssociatedPointsEqWeaklyAssociatedPoints` states
`AlgebraicGeometry.Scheme.associatedPoints_eq_weaklyAssociatedPoints`, with proof `sorry`.
The source read is Stacks Project, Divisors, Lemma 31.5.8, Tag 05AR
(https://stacks.math.columbia.edu/tag/05AR). The local literature file was absent, so the
published tag was opened. Its final assertion applies to the quasi-coherent structure sheaf.
No statement correction or disputed statement is needed.

Hypothesis and clause correspondence:
- “X a scheme” is `(X : Scheme.{u})`, with an explicitly declared universe `u`.
- “locally Noetherian” is `[IsLocallyNoetherian X]`. The recorded Mathlib class is the same
  notion as an affine Noetherian cover, by the existing affine-cover characterizations.
- The structure sheaf and its local ring at x are `X.presheaf` and `X.presheaf.stalk x`.
  No extra sheaf or module hypothesis is introduced.
- The associated-point set is the left set comprehension. Its witness `a` is an element
  of that same local ring, and the equality identifies its maximal ideal with
  `(⊥ : Submodule R R).colon {a}`, which is precisely `{r | r * a = 0}`.
- The weakly associated-point set is the right set comprehension. Membership of the stalk's
  maximal ideal in `Ideal.WeakAss R` means it is minimal among prime ideals containing the
  annihilator of some element of R, by the existing definition's full body.
- “exactly” and `Ass(O_X) = WeakAss(O_X)` are rendered as equality of these two subsets of X.

Dependencies read and used:
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  (and its `Hom` signature/docstring were read; this statement needs only Scheme).
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- Added the already landed definition node `def-sc-weakly-associated-primes` to `stmt_deps`:
  `Sheaf.RingTheory.WeaklyAssociated`, `Ideal.WeakAss`. No new node or duplicate definition.
  The original statement, proof, and proof dependencies remain verbatim.
- Mathlib's `Submodule.colon` and `Ideal.minimalPrimes` supply annihilators and minimality;
  their signatures and definitions were read. In particular, Mathlib's `IsAssociatedPrime`
  uses a radical, so it is not substituted for the node's literal annihilator equality.

Edge cases checked mathematically: the empty scheme has two empty point sets; a field stalk
has maximal ideal zero, the annihilator of 1, also minimal over that annihilator; zero cannot
be a witness at a scheme point since its annihilator is the top ideal whereas the maximal
ideal is proper. No reducedness, integrality, nonemptiness, dimension, finite type or global
Noetherian hypothesis is imposed. Nonreduced Noetherian stalks and embedded associated
points are included. `Scheme.{u}` permits every universe of schemes.

Searches actually run:
- msearch LeanFinder: “associated points equal weakly associated points of a locally
  Noetherian scheme”: 8 hits concerning generic points, quasi-sobriety, reduced schemes and
  germ injectivity; no exact statement.
- msearch Loogle: `Ideal.associatedPrimes, IsLocallyNoetherian`: unknown identifier
  `Ideal.associatedPrimes`, 0 hits; not an exact-match result.
- msearch Mathlib grep: `weaklyAssociated|weakly associated|associatedPoints|associatedPrimes`:
  25 hits, primarily ring/module associated-prime files, no scheme point equality.
- msearch LeanSearch: “associated points equal weakly associated points on a locally
  Noetherian scheme”: UNAVAILABLE, HTTP Internal Server Error; no negative search inferred.
- Direct rg in `WeilConjectures/` and `lean/Sheaf/` for association terminology found
  `Ideal.WeakAss` in the project's WeaklyAssociated module, used here, and the existing
  finitely generated-prime equivalence in AnnihilatorEqIffMinimalPrimeOfFG. No exact item.
- Direct grep by item id in `WeilConjectures/`: no match. Direct rg by item id and proposed
  declaration in `dag/lean_names_upstream.json`, `WeilConjectures/`, and `lean/Sheaf/`: no match.

The docstring records both node proof steps and their dependency ids for stage 3.

## Second reading by K1

I read the node statement and the Lean declaration side by side. The objects and
clauses match as follows:

- The scheme `X` is rendered by `(X : Scheme.{u})`; the explicit universe permits
  arbitrary scheme universes. The locally Noetherian hypothesis is exactly the
  instance `[IsLocallyNoetherian X]`, with no extra finiteness, separation,
  integrality, characteristic, or nonemptiness assumption.
- The structure sheaf and its local ring are rendered by
  `X.presheaf` and `X.presheaf.stalk x`. Thus the witness in the associated-point
  clause is `a : X.presheaf.stalk x`, the same local ring attached to `x`.
- The left set is exactly the associated-point condition: its maximal ideal is
  equal to `(⊥ : Submodule R R).colon {a}`, the annihilator of one stalk element.
- The right set is exactly the weak-association condition: membership in
  `Ideal.WeakAss R` expresses that the maximal ideal is prime and minimal among
  primes containing an element annihilator, using the dependency declaration.
- Equality of the two set comprehensions is the node's final assertion
  `Ass(O_X) = WeakAss(O_X)`, with the point quantifier and existential in the
  same positions. No clause is weakened or strengthened.

The empty scheme gives two empty subsets. A field stalk has maximal ideal zero,
which is the annihilator of `1` and is minimal over that annihilator. A zero
witness cannot satisfy the associated condition at a point because its
annihilator is top while a local maximal ideal is proper. Nonreduced stalks,
embedded associated points, and every scheme universe remain included; there is
no restriction on characteristic or on an index set (none occurs).

I searched Mathlib and the project with LeanFinder, Loogle, LeanSearch, and
direct `rg` searches for associated-point and weak-association terminology and
for the item/declaration names. The searches found only the project's existing
`Ideal.WeakAss` definition and related annihilator lemmas; no exact scheme
statement exists in Mathlib, `WeilConjectures`, or `lean/Sheaf`. LeanSearch was
unavailable and Loogle returned no exact match. The node's dependency record for
`def-sc-weakly-associated-primes` is therefore correctly used.

No mismatch was found. The module already compiles cleanly with
`scompile.py`; its theorem proof remains `sorry` as required for stage 2, and
the node's `lean.statement` is verbatim the theorem signature.
