## Worker report

The new module `Sheaf.AlgebraicGeometry.AffineMPseudoCoherentCriterion` states
`AlgebraicGeometry.affine_mPseudoCoherent_iff`, with its whole proof `sorry`.
The node is unchanged except for `lean`. There are no new definitions, dependency
repairs, statement corrections, or disputed statements.

The source was read in `literature/stacks-project/perfect.tex`,
`lemma-pseudo-coherent-affine` (Tag 08E7), including both directions of the proof.
The seven-step proof docstring follows the accepted DAG proof, including the exact
restriction/derived-pullback comparison added by the stage-1 reviewer.

Hypothesis and clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`. There is no nontriviality,
  Noetherian, finiteness, or characteristic assumption.
- Y = Spec A: every scheme expression is `Spec (.of A)`, so no arbitrary scheme
  or extra identification datum is substituted for the specified affine scheme.
- An integer m: `(m : ℤ)` is arbitrary and is the same parameter of both predicates.
- An arbitrary object M of D(A): `(M : DerivedCategory (ModuleCat.{u} A))`.
  There is no bound on M and no bounded-complex input.
- The image under the termwise associated-sheaf equivalence: the image is
  `(exists_affineQCohDerivedEquivalence.{u, wA, wY} A).choose.functor.obj M`.
  This is an object of the recorded `schemeDerivedQCohCategory`.
  The recorded existence theorem's first conjunct specifies its functor by the
  natural comparison `Q ⋙ e.functor ⋙ inclusion ≅ termwiseTilde ⋙ Q`.
  Thus this uses the prescribed affine equivalence, not an arbitrary equivalence
  of categories. The localization universal property determines this functor up
  to natural isomorphism. The choice takes existing canonical-equivalence data;
  this delivery introduces no new choice-based definition.
- The underlying object in D(O_Y) is obtained by the recorded full-subcategory
  inclusion `(schemeDerivedQCohProperty (Spec (.of A))).ι.obj`.
- The left clause is precisely `Scheme.IsMPseudoCoherent (Spec (.of A)) m` of
  that image. It uses the landed local strictly-perfect approximation predicate
  with derived pullback along each open inclusion.
- The right clause is precisely `DerivedCategory.IsMPseudoCoherent m M`, using
  the landed bounded finite-free approximation predicate, including isomorphisms
  in degrees strictly above m and an epimorphism in degree m.
- “If and only if” is `↔`; it is a fixed-m equivalence, not the all-m assertion.
- The `HasDerivedCategory` instances choose the required localizations. Their
  morphism universes `wA` and `wY` are independent; the open-subscheme instances
  are exactly those required by the sheaf predicate. These are size/construction
  data, not extra geometric hypotheses. No equality of derived morphism universes
  is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`,
  `schemeDerivedQCohCategory`.
- `WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `AlgebraicGeometry.exists_affineQCohDerivedEquivalence`, including its full
  comparison, inverse, triangulatedness, and shifts clauses.
- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`.
- `WeilConjectures.RingTheory.MPseudoCoherent`:
  `DerivedCategory.IsMPseudoCoherent`.

The modules of recorded proof dependencies are imported without `public` unless
already a public statement dependency. Mathlib matches without a `lean` record
are used through their recorded Mathlib modules: `OpenImmersion` and
`RingTheory.Spectrum.Prime.Topology`. No proof import was omitted for a cycle.

Edge cases checked against the definitions and the source:

- A = 0 is allowed. Spec A is empty; the pointwise sheaf predicate has no points
  to check. D(A) is zero, and the zero finite-free complex is an approximation.
- m = 0, negative m, and positive m all use the same strict inequality `m < j`
  and degree-m epimorphism in the existing definitions.
- M = 0 and rank-zero approximation terms are allowed. Neither definition forces
  a nonempty cover, positive rank, or a nonzero complex.
- Unbounded representatives are allowed; only the approximating witnesses in the
  existing predicates are bounded. No assumption was inferred from the full
  pseudo-coherence criterion.
- Non-Noetherian rings remain in scope. In particular the statement does not
  replace pseudo-coherence by finite or coherent cohomology.

Searches for a duplicate:

- `msearch.py ... leanfinder` with “affine scheme derived equivalence m pseudo
  coherent complex if and only if module complex”: 8 hits concerning abelian
  modules, affine-site sheaf equivalence, and derived t-structures; none states
  the fixed-m affine criterion.
- `msearch.py ... loogle 'IsMPseudoCoherent'`: 0 hits (identifier unknown to the
  Mathlib service).
- `msearch.py ... leansearch 'm pseudo coherent affine scheme module derived
  category'`: hits concerned quasi-coherent sheaves, not this fixed-degree theorem.
- `msearch.py ... grep 'MPseudoCoherent|mPseudoCoherent|m_pseudo_coherent'`: 0
  Mathlib hits.
- `rg -n 'MPseudoCoherent|mPseudoCoherent|m_pseudo_coherent'` over both
  `lean/WeilConjectures` and `lean/Sheaf`: found the two recorded predicates and
  ring approximation/shift/localization results, but no fixed-m affine criterion.
- `grep -rn 'lem-sfb-affine-m-pseudocoherent-criterion' lean/WeilConjectures`:
  no existing node attachment.
- `rg -n 'isMPseudoCoherent_affine_iff'` over both Lean roots and
  `dag/lean_names_upstream.json`: no name collision.
- Read `WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion`:
  `isPseudoCoherent_affine_iff` concerns full pseudo-coherence, so is not this
  fixed-m theorem. Read `AffineDerivedTildeHomologyComparison`: it compares
  homology functors and does not assert pseudo-coherence.

Validation: the final module compiled through `scompile.py Q30
lem-sfb-affine-m-pseudocoherent-criterion .../AffineMPseudoCoherentCriterion.lean`
as both a sandbox module and its library module. Both completed cleanly. The
only postponed declaration is `AlgebraicGeometry.affine_mPseudoCoherent_iff`.

## Second reading by Q30

I re-opened the node and final module and checked the correspondences above.
This was a self-check, not a claim of independent review: the dispatcher explicitly
prohibits starting other agents and assigns independent delivery review to the
maintainer. The independent maintainer review remains the delivery gate.

The initial elaboration check found two interface mistakes: a missing m argument
on the sheaf predicate and an over-site localization binder where this recently
landed predicate requires localization on the open subscheme itself. Both were
corrected to match the exact recorded predicate before the successful compile.
The final comparison has the same m, the specified affine-derived image of M,
and both directions of the criterion. The proof docstring now explicitly covers
all seven DAG steps, including the finite standard subcover, the localized
complex comparison and the lower bound on the lifted finite-free approximant.
No mathematical hypothesis or clause of the node was changed or omitted.
