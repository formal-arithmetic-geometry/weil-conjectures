## Worker report

The module `Sheaf.RingTheory.MonoidAlgebraDomainFraction` states
`AddMonoidAlgebra.domain_fraction_of_fg_generating_submonoid`, with its entire proof `sorry`.
No definitions or auxiliary theorems are introduced. Only the item's `lean` record changes.

Hypothesis-by-hypothesis correspondence:

- A field k: `(k : Type u) [Field k]`.
- A torsion-free abelian group G: `(G : Type v) [AddCommGroup G] [IsAddTorsionFree G]`.
  In an additive group Mathlib's injectivity of positive natural scalar multiplication is
  equivalent to the node's absence of nonzero torsion.
- A submonoid Q of G: `(Q : AddSubmonoid G)`. This includes the identity and is closed under
  addition, and its subtype carries the inherited cancellative commutative monoid structure.
- Finite generation: `(hfg : Q.FG)`, meaning generation by a finite set as an additive submonoid.
- Generation of G as a group: `(hgen : AddSubgroup.closure (Q : Set G) = ⊤)`.
- The additive conventions from `def-trf-fine-fan-blowup` are used via Mathlib's additive
  monoids and additive monoid algebras. Its recorded module is imported. Its `IsFine` definition
  is phrased multiplicatively using `Algebra.GrothendieckGroup`; this theorem does not need a
  separate fineness or group-completion predicate because Q is already embedded in G and the
  two node hypotheses specify its finite generation and generation of G. No duplicate notion
  of fine monoid or group completion is defined.

Clause-by-clause correspondence, in order:

- The specified monomial embedding is `mapDomainRingHom k Q.subtype`. Mathlib's definition
  extends the given additive homomorphism on exponents, preserving coefficients. It is a
  unital ring homomorphism, and `Function.Injective` asserts that it embeds the rings.
- `IsDomain (AddMonoidAlgebra k Q)` and `IsDomain (AddMonoidAlgebra k G)` assert both domains.
- The existential `e : FractionRing (AddMonoidAlgebra k Q) ≃+*
  FractionRing (AddMonoidAlgebra k G)` is accompanied by equality for every
  `f : AddMonoidAlgebra k Q` between `e (algebraMap ... f)` and the fraction-ring image of
  `mapDomainRingHom k Q.subtype f`. This specifies the equivalence induced by the inclusion,
  rather than merely the existence of an abstract field isomorphism. `FractionRing` is defined
  for any commutative ring, so these terms need no extra domain assumptions. The two domain
  conclusions ensure that these total fraction rings are precisely fraction fields. The
  compatibility determines the map on all fractions uniquely and also preserves k.
- The last clause quantifies over every `g : G` and supplies `a b : Q` with
  `single g (1 : k) * single (b : G) (1 : k) = single (a : G) (1 : k)`.
  This is exactly the quotient-of-monomials identity, written without introducing a field
  structure before the domain conclusion. A group monomial is a unit, with inverse indexed
  by its negative, and is nonzero since its coefficient is one over a field. Thus this
  cross-multiplied form includes the asserted nonzero denominator without an extra hypothesis.

Dependency declarations and inspected sources:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`: read its recorded declaration
  `AlgebraicGeometry.FineFan.SmoothFunctorialDesingularization` and the relevant monoid
  conventions, notably `AlgebraicGeometry.FineFan.IsFine` and `saturation`. Confirmed the
  current published source with `scompile.py --source`. This is a conventions-only statement
  dependency; none of the fan construction is copied or specialized.
- The proof dependency `lem-trf-affine-monoid-unique-sums` is already a Mathlib leaf:
  `AffineAddMonoid.to_twoUniqueSums` in `Mathlib.Algebra.AffineMonoid.UniqueSums`, with
  `[AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]`. Read the declaration and
  file docstring. The file is imported for the planned proof.
- Read `AddMonoidAlgebra.mapDomainRingHom` and `mapDomain_injective` in
  `Mathlib.Algebra.MonoidAlgebra.MapDomain`, and the monoid-algebra structures in
  `Mathlib.Algebra.MonoidAlgebra.Defs`.
- Read the `FractionRing` abbreviation, its module documentation and its domain-to-field
  instance in `Mathlib.RingTheory.Localization.FractionRing`.
- `Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors` is imported for the domain proof; its
  generated additive instance requires the coefficient domain and unique sums.

Source checked: the local ILO PDF, Exposé VIII 3.2.9 and 3.2.12, printed p.104, via
`pdftotext -layout`. The former uses the common dense group-algebra torus; the latter
explicitly uses the inclusion of the fine torsion-free monoid algebra in its group algebra
and integrality. The docstring carries all seven steps of the DAG's supporting algebra:
coefficientwise embedding, unique sums, the nonzero product coefficient, differences in Q,
finite-support denominator clearing including empty support, integrality of the group
algebra, and the induced bijection on fractions.

Edge cases checked mathematically:

- The trivial group and Q = {0}: both algebras are k, the embedding and fraction equivalence
  are identities, and the last clause uses a = b = 0. Finite generation permits the empty
  generating set in this case.
- Q = G when G is finitely generated: the identity inclusion is covered, including monoids
  with units; there is no sharpness or positivity assumption.
- A nonsaturated monoid such as the nonnegative submonoid of Z generated by 2 and 3 is covered.
  There is no added saturation, freeness, smoothness, order, or characteristic hypothesis.
- Empty support (the zero polynomial) is handled by denominator exponent zero in the proof;
  no nonzero numerator is assumed in the field-equivalence clause.
- Every field characteristic and independent coefficient/exponent universes u and v are
  included. The field assumption already excludes the zero coefficient ring.

Searches for an existing full statement:

- `msearch.py leanfinder`: "A finitely generated submonoid of a torsion free abelian group
  which generates it has an integral domain monoid algebra with the same fraction field as
  the group algebra". Eight hits included `Ring.instAlgebraFractionRing`,
  `AddMonoidAlgebra.finiteType_iff_group_fg`, `IsFractionRing`, and localization subalgebra
  results. None states the monoid inclusion plus domain conclusions and common fraction field.
- `msearch.py loogle`: `AddMonoidAlgebra, FractionRing`. Zero hits.
- `msearch.py grep`: `Fraction|IsDomain|mapDomain`, subdirectory `Algebra/MonoidAlgebra`.
  Nineteen hits included the domain instance and `mapDomainRingHom`; none matches all clauses.
- `msearch.py leansearch`: "The fraction field of an additive monoid algebra agrees with that
  of its group completion". Eight hits included `Algebra.GrothendieckGroup.instCommGroup`,
  localization subalgebra interfaces, and `FractionRing.algEquiv.congr_simp`; none matches.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for `AddMonoidAlgebra`, then for
  `AddMonoidAlgebra.*Fraction|Fraction.*AddMonoidAlgebra|monoid.*[Ff]raction|[Ff]raction.*monoid`:
  the first found monomial Cech maps and unrelated formal monoid models; the second found
  general localization prose and formal glueing, not this statement.
- `grep -rn lem-trf-monoid-algebra-domain-fraction` in upstream: no hits.
- Searched `dag/lean_names_upstream.json` and the source trees for
  `monoidAlgebraDomainFraction|monoid_algebra_domain_fraction`: no hits.

Validation: `scompile.py Q57 lem-trf-monoid-algebra-domain-fraction <file>` passed both the
sandbox probe and the library module compile, with no warnings or errors (2.7s and 3.3s).
The first attempt exposed that the recorded dependency is a non-`module` file. The delivered
file uses the compatible ordinary import format, matching its dependency and other nearby
stage-2 files; the corrected file is the one that passed. No live or upstream file was edited.
No node fault, statement correction, or disputed statement was found.

## Second reading by Q57

Performed a separate consistency pass with the node and completed Lean file open. Rechecked
field, torsion-free abelian group, finite submonoid generation, group generation, the exact
subtype-induced monomial map, its injectivity, both domain clauses, the compatibility equation
on the fraction equivalence, and the final monomial equation. There is no extra saturation or
sharpness hypothesis. The fraction equivalence extends the inclusion on every element,
which is essential for the node's word "identifies". The monomial equation uses elements of
Q, not arbitrary elements of G, on its numerator and denominator. No statement mismatch was
found and no mathematical clause changed. This is the worker's second pass; as directed by
the dispatcher, no other agent was started and the maintainer supplies the independent review.
