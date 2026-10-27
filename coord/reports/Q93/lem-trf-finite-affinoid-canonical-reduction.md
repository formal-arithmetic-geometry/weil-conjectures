## Worker report

The module `Sheaf.RingTheory.FiniteAffinoidCanonicalReduction` states
`RestrictedSeries.finite_canonicalReduction`, with one `sorry` and no new definition.
The source node is unchanged except for its `lean` record. No statement correction,
dependency repair, or new node is needed.

Hypotheses and clauses, in order:

- `K : Type u`, `[NontriviallyNormedField K]` supplies the field and nontrivial
  real-valued multiplicative absolute value. `[IsUltrametricDist K]` is the
  nonarchimedean condition, `[CompleteSpace K]` completeness, and `[IsAlgClosed K]`
  algebraic closedness. `NontriviallyNormedField` extends Mathlib's `NormedField`.
- `A : Type v` and `B : Type w` are normed commutative rings and unital K-algebras;
  `[Nontrivial A]`, `[Nontrivial B]` impose nonzero, and `[IsReduced A]`,
  `[IsReduced B]` impose reducedness. The two universes are independent of K
  and of one another.
- `hA`, `hB` use exactly `RestrictedSeries.IsAffinoidQuotient` from the dependency
  `def-trf-restricted-series-presentation`. This supplies completeness, a finite
  restricted-series presentation with a surjective ring map commuting with
  constants, and its quotient Gauss norm. We choose these quotient norms to
  represent the affinoid Banach topologies; no isometry condition is imposed on
  the map φ. The predicate allows every finite number of variables, including zero.
- `φ : A →ₐ[K] B` is the unital scalar-compatible map; `hφ : φ.Finite` means B is
  finitely generated as A-module with action through φ, by Mathlib's
  `AlgHom.Finite` / `RingHom.Finite`. There is no injectivity or surjectivity binder.
- `Continuous φ` is the first conclusion, not a hypothesis.
- The existential `ρA`, `ρB` are uniquely fixed functions by their pointwise
  equalities to `sSup {r | ∃ χ : H →ₐ[K] K, Continuous χ ∧ r = ‖χ h‖}`.
  These are precisely the character suprema in the node. Their existence as
  functions is not an added hypothesis. `∀ a, ρB (φ a) ≤ ρA a` is contraction.
- `A₀`, `B₀` are actual Mathlib subrings, specified by the exact membership
  equivalences `a ∈ A₀ ↔ ρA a ≤ 1` and `b ∈ B₀ ↔ ρB b ≤ 1`.
  `IA`, `IB` are actual ideals of these rings, specified by membership iff the
  corresponding spectral value is strictly less than one. Thus `A₀ ⧸ IA` and
  `B₀ ⧸ IB` are exactly the two canonical reductions, not presented substitutes.
- `V : Subring K` and `m : Ideal V` have exact membership predicates `‖c‖ ≤ 1`
  and `‖c.val‖ < 1`. Their quotient is the stated residue scalar ring κ.
- `sA`, `sB` are ring homomorphisms from this same quotient κ to the two
  reductions. For EVERY c in V the formula provides a representative equal
  to `algebraMap K H c.val` and specifies the image of its residue class.
  These formulas fix the scalar maps on all representatives.
- `f` is a ring homomorphism between the two reductions. For EVERY a in A₀
  the formula supplies b in B₀ whose underlying element is `φ a.val`, and
  imposes `f ([a]) = [b]`. Consequently f is the canonical induced map,
  uniquely specified on all quotient classes, not an arbitrary finite map.
- `f.comp sA = sB` expresses exactly that f is a κ-algebra homomorphism.
  Ring maps from κ encode the scalar algebra structures without selecting
  local algebra instances. `f.Finite` is exactly finite generation of the
  second reduction as module over the first, using f as its scalar action.

The functions, subrings, ideals and maps in the conclusion are existentially
specified by exact formulas; no data are taken from an unconstrained existence
axiom and no object is defined by `sorry`. This is a direct proposition stating
existence of the canonical quotient construction together with the required
properties. Extensionality and surjectivity of the quotient projections determine
all its objects and maps uniquely. No separate independent notion is introduced.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`, for `def-weil-field` (inherited through
  `NontriviallyNormedField`). Its full class signature and docstring were read.
- `RestrictedSeries.IsAffinoidQuotient`,
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, for
  `def-trf-restricted-series-presentation`. The entire module, including
  `constants`, quotient norm and completeness clauses, was read.
- `AlgHom.Finite`, `RingHom.Finite`, `Mathlib.RingTheory.Finiteness.Defs`;
  their full definitions specify the module action through the supplied map.
- Proof-only imports follow the already recorded proof leaves:
  `Ideal.exists_le_maximal` (`Mathlib.RingTheory.Ideal.Maximal`),
  `minimalPrimes.finite_of_isNoetherianRing`
  (`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`),
  `Ideal.exists_minimalPrimes_le` (`Mathlib.RingTheory.Ideal.MinimalPrime.Basic`),
  `Algebra.finite_adjoin_of_finite_of_isIntegral`
  (`Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`), and
  `fg_of_fg_of_fg` (`Mathlib.RingTheory.Adjoin.Tower`).
  The other seven analytic/algebraic proof dependencies have no Lean record in
  the supplied DAG, so no module import is invented for them. They are each named
  in the eight-step natural-language proof docstring for later proof work.

Edge cases checked before drafting:

- A and B cannot be zero, exactly as in the node. Zero-variable Tate presentations
  remain allowed by the dependency predicate. In particular A = B = K and φ = id
  yield κ = both reductions and the identity finite map.
- Quotient maps A → A/I with a nonzero reduced quotient are included even with
  nonzero kernel. The map on reductions is not assumed onto; finite extensions
  and products are also allowed, including finite maps that are not injective.
- Closed versus open inequalities are kept distinct: norm-one representatives
  lie in the closed ball and do not lie in the reduction ideal merely by having
  norm one. Zero lies in all relevant ideals.
- Nontriviality of the absolute value is explicit. No characteristic restriction
  or discrete valuation hypothesis is imposed. No normed-algebra compatibility
  class beyond the recorded scalar-compatible quotient presentation is required.
- The character supremum is a real `sSup`, exactly the node's real-valued supremum;
  boundedness and existence of characters are consequences of the affinoid
  hypotheses in the supplied proof, not extra assumptions.
- Scalar maps and f are constrained on every representative, including scalars,
  zero and one. The final square expresses residue-field compatibility even
  though quotient algebra structures are encoded by ring maps rather than
  additional typeclass choices.

Searches for an existing statement (2026-10-24 UTC):

- `msearch.py ... leanfinder "A finite homomorphism of reduced strict affinoid
  algebras induces a finite map on canonical reductions"`: eight hits, led by
  `AlgebraicGeometry.IsFinite.finite_app` and `IsFinite.SpecMap_iff`, concern
  affine scheme rings, not spectral canonical reductions; no match.
- `msearch.py ... leansearch "Canonical reduction of a strict affinoid algebra
  is finite under a finite algebra homomorphism"`: eight hits, including
  `AlgHom.Finite` and scheme finiteness; no affinoid reduction statement.
- `msearch.py ... loogle "AlgHom.Finite, Ideal.Quotient"`: unknown identifier
  `Ideal.Quotient`, zero hits. Repeated as `loogle "RingHom.Finite"`: twelve
  hits including the needed finite ring-map definition, no analytic theorem.
- `msearch.py ... grep "affinoid|TateAlgebra|canonical.?reduction"`: zero hits
  in Mathlib. Direct Mathlib searches located ordinary quotient rings, unit
  balls and algebraic extension `spectralNorm`; none is the character supremum
  reduction of a reduced strict affinoid.
- `rg` for `IsAffinoidQuotient`, `canonicalReduction`, `CanonicalReduction`,
  `characterSup`, `spectralNorm`, `spectralSeminorm` in `lean/Sheaf` and
  `lean/WeilConjectures`: the recorded restricted-series definition is usable;
  algebraic field spectral norms and integral coefficient reductions are
  different notions. No duplicate statement was found.
- `rg` for the item id in `lean/WeilConjectures`: no match.
- DAG grep for canonical reduction and `tools/blueprint_refs.py search
  'canonical reduction'`: no existing definition of this spectral reduction;
  the related analytic statements introduce their own reduction notation.
  This delivery likewise states its construction by exact formulas, adding no
  independently named definition.

No statement dispute or node fault was found. The CompactObject example path is
withdrawn in the current clone; its node points to the upstream
`WeilConjectures.CategoryTheory.CompactObject`, which was read for conventions.
The Temkin PDF web fetch returned HTTP 502; this delivery makes no source-based
statement correction and follows the node's supplied source and proof verbatim
in mathematical content.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
