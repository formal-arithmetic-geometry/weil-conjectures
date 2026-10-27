## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteNormalizationCodimensionOnePurity` states
`AlgebraicGeometry.finite_normalization_etale_of_codimension_one_differentials_vanish`.
It introduces no definition. The theorem has exactly one postponed proof, `sorry`.
The node copy differs from the current accepted stage-1 split only in `lean`.
The earlier worker's stage-1 rejection does not apply to this stage-2 assignment:
coord/brief-stage2.md section 0 explicitly authorizes this handoff, and the item
appears in the stage-2 queue with no Lean record. No repair note was present.

Source read: Stacks Project, `pione.tex`, Lemma `purity`, Tag 0BMB, including
its five hypotheses at lines 5136–5146 and the beginning of its proof. The item's
five proof steps give the finite-normalization specialization and the separate
generic-point argument. The theorem docstring carries those steps, including the
chain-height argument and the equality of A-derivations and K-derivations on L.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A regular Noetherian integral domain: `(A : Type u) [CommRing A] [IsDomain A]
  [IsRegularRing A]`. Mathlib's `IsRegularRing` extends `IsNoetherianRing` and requires
  regularity at every prime localization, exactly the ring clause of
  `def-weil-regular-scheme`. There is no additional local, excellence, completeness,
  or henselian hypothesis.
- K = Frac(A): `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]`.
  This is an arbitrary model of the fraction field, not an arbitrary extension.
- L/K finite separable: `(L : Type u) [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]`.
  `[Algebra A L] [IsScalarTower A K L]` expresses the composite structural map
  A to K to L, not a second unspecified embedding. The fraction field has an
  independent universe; A and L inhabit a common ambient universe for the two
  spectra, as Mathlib's `Spec.map` requires. Any pair of such rings can be placed
  in a common ambient universe; no size bound, cardinality assumption, or finite
  dimension of A is imposed.
- C = the set of elements of L integral over A: every occurrence of C is the actual
  Mathlib `integralClosure A L`, whose carrier is `{z | IsIntegral A z}`.
  No abstract candidate normalization, choice, or extra property is substituted.
- C finite as an A-module: `[Module.Finite A (integralClosure A L)]`.
- Every height-one prime p of A: `∀ (p : Ideal A) [p.IsPrime], p ≠ ⊥ →
  (∀ r : Ideal A, r.IsPrime → r < p → r = ⊥) → ...`.
  Since A is a domain, the zero ideal is prime. The two conditions say precisely
  that p is nonzero and no prime lies strictly between zero and p. This uses the
  explicit parenthetical characterization in the node, without a height helper.
- Every prime q of C contracting to p: `∀ (q : Ideal (integralClosure A L))
  [q.IsPrime] (hpq : p = q.comap (algebraMap A (integralClosure A L))), ...`.
  The equality is oriented to fit Mathlib's canonical localization map.
- Omega(C_q/A_p) = 0: `Subsingleton (@KaehlerDifferential
  (Localization.AtPrime p) (Localization.AtPrime q) _ _
  (Localization.localRingHom p q (algebraMap A (integralClosure A L)) hpq).toAlgebra)`.
  Subsingleton means the module is zero. The displayed algebra structure comes
  from the canonical induced local ring homomorphism, with the supplied contraction
  equality. The underscores are synthesized commutative ring structures, not holes
  or implicit variables. There are no local instances, let binders, private notions,
  or arbitrary choices in the signature.
- The conclusion is finite AND etale for Spec(C) to Spec(A): `IsFinite
  (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L)))) ∧ Etale
  (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))`.
  Both clauses concern exactly the structural spectrum map of the node.
- The last sentence excludes additional assumptions: no such assumptions occur.

Dependency declarations read and used:

- `def-weil-regular-scheme`: the recorded Mathlib ring clause `IsRegularRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs` (and its parent `IsNoetherianRing`).
  The recorded `AlgebraicGeometry.IsRegularScheme` in module
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is the scheme clause; its source was read, but it is not a ring predicate and is not
  substituted for the node's already recorded ring match.
- `def-pc-field-extension`: `Algebra`, `algebraMap`,
  `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`; it implies algebraicity.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`; `FiniteDimensional` is the field specialization.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`, and its canonical
  induced map `Localization.localRingHom`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`,
  `Mathlib.RingTheory.Kaehler.Basic`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, exposed by the public morphism imports.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.

The additionally used fraction-field interface is Mathlib's `IsFractionRing` in
`Mathlib.RingTheory.Localization.FractionRing`. Each recorded proof-dependency module
is imported privately, including the live Q131 pointwise purity theorem
`AlgebraicGeometry.exists_etale_neighborhood_of_unramified_codimension_one` in
`Sheaf.AlgebraicGeometry.LocalQuasiFiniteBranchPurity`. For Mathlib proof leaves,
the corresponding source modules are imported privately as well. No unstated
prerequisite was needed to type this statement.

Edge cases checked before writing:

- A a field: there is no nonzero prime of A, hence the codimension-one condition is
  vacuous. Its integral closure in the finite extension is L, and separability gives
  the asserted finite etale morphism; the generic-point proof handles this case.
- L = K: regularity makes A integrally closed, so its normalization is A and the
  conclusion is the identity case, with all differentials zero.
- Dimension one: the condition includes every nonzero prime, and includes each
  q above it; no base localness or uniqueness of q was imposed.
- Ramification is not accidentally admitted: for A = Q[t] in L = Q(s), t = s^2,
  with K = Q(t), C = Q[s] is finite, but at p = (t), q = (s) the local relative
  differential module is generated by ds with relation 2s ds = 0, and is nonzero.
  Thus this standard ramified cover fails the hypothesis.
- A zero ring is correctly excluded by `IsDomain A`; a purely inseparable field
  extension is correctly excluded by `Algebra.IsSeparable K L`.

Searches for an existing exact statement (2026-10-24):

- `msearch.py`, LeanFinder: "Finite normalization of a regular Noetherian domain in
  a finite separable field extension is etale if the local Kahler differentials
  vanish over all height one primes". Eight hits: `Algebra.Etale`,
  `Algebra.FormallyEtale.of_isSeparable_aux`, the source/target localization-span
  etale criteria, standard etale algebra instances, and `Algebra.IsEtaleAt`.
  None is codimension-one purity.
- `msearch.py`, Loogle: `"IsRegularRing", "Etale"`. Zero hits.
- `msearch.py`, grep: `purity|ramificationLocus`. Zero hits.
- `msearch.py`, LeanSearch: "Finite integral closure of a regular Noetherian domain
  is etale if unramified over all height one primes". Eight hits, including
  `IsIntegralClosure.finite`, normality of integral closure, separability and formal
  etaleness criteria, and Dedekind ramification-index lemmas. None is the statement.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for branch-locus purity,
  `finite_normalization`, `0BMB`, and the proposed declaration name: the nearby
  statements concern flat morphisms and etale neighbourhoods or other normalizations.
  The Q131 local-purity theorem is the general proof prerequisite, not this finite
  normalization statement. No duplicate exact statement was found.
- Direct search for this node id in `lean/WeilConjectures`: no hits.
- Direct `rg` in Mathlib's AlgebraicGeometry and RingTheory for
  `purity.*branch|branch.*locus|codimension.*[ée]tale`: no exact purity theorem found.

Validation: the required `scompile.py Q116` wrapper compiled both its sandbox form
and the library-named module successfully (2.0 and 2.1 seconds), with no errors or
unexpected warnings. Every variable and universe is explicitly bound, with
`set_option autoImplicit false`. No line exceeds 100 characters. There are no
statement disputes, corrections, new nodes, or dependency repairs.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
