## Worker report

Verification on 2026-10-21: retained the saved Lean source and first ran the
prescribed `deliver2.py N9 lem-weil-pbc-finite-basis-cech-first-limit --no-push`.
It printed `OK (dry run)`: preflight passed, and both the sandbox and the actual
`Sheaf.AlgebraicGeometry.FiniteBasisCechFirstLimit` module compiled cleanly.
The earlier published-artifact failures have resolved. No shared source, launcher
file, tool or published artifact was edited.

Final self-check: read the current item, all four statement-dependency records,
their declaration signatures and docstrings, and the first-limit calculation in
Stacks 099S/099U. The node copy differs from the current node only in `lean`.
Its `lean.statement` equals the theorem signature verbatim. Every variable and
universe is explicitly bound, `autoImplicit` is false, no line exceeds 100
characters, and the only sorry is the proof of `finite_basis_cech_first_limit`.
No mathematical statement or dependency change is needed.

The proposed statement constructs a complex diagram and cocone with actual
restriction-map coordinates, and asserts that the canonical colimit.desc maps
are isomorphisms on integer complexes and on every nonnegative cohomology group.
Its auxiliary definitions bundle existing stage schemes and their given arrows;
they neither choose arbitrary maps nor introduce a second Čech construction.

Hypothesis and clause correspondence:

- Affine X: `(X : Scheme.{u}) [IsAffine X]`.
- Finite discrete, possibly noncommutative ring: `Λ : Type (u + 1)` with
  `Ring`, `Finite`, `TopologicalSpace`, `DiscreteTopology` instances.
- Arbitrary étale left module sheaf, with no injectivity assumption:
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
- M = ν_X^*F: `firstLimitClassicalPresheaf` restricts the underlying abelian
  presheaf of `(ProEtale.finiteCoefficientComparison X Λ).obj F` to the
  affine ind-étale basis through the existing `AffineProEt.toProEt` functor.
- U in the basis: `U : X.AffineProEt`. The finite nonempty basis covering is
  `V : Fin m → X.AffineProEt`, `f : ∀ a, V a ⟶ U`, `hm : 0 < m`, and
  `hcover : Sieve.ofArrows V f ∈ topology X U`.
- Chosen first-limit systems: `J`, its coordinate preorder/nonempty/directed
  instances, the over-U diagrams `D`, and the presentation cones `q`. Their
  hypotheses `hD`, `hstage`, `hlimit`, `htransition`, `hprojection`, and
  `hstagecover` are the corresponding conjuncts in the recorded
  exists_finite_intersection_limit_compatibility signature. The stage helper
  uses that dependency's actual `firstLimitCoordinate`, not a private reindexing.
  The intersection identifications and deletion compatibilities in that theorem
  follow for these systems and are used in the proof plan; they are not extra
  hypotheses on F.
- Ordered alternating complexes with repeated indices: `S` and `Sj` are the
  recorded `SiteCechComplex` data on the original and stage coverings, and
  `.complex` is the existing nonnegative alternating construction. Its tuple
  index is `Fin (p + 1) → Fin m`, with no injectivity constraint on the tuple.
- Canonical transitions: the first coordinate formula characterizes C.map h
  after the object identifications e by restriction along every morphism b
  with the specified product projections. Such b exists uniquely by the
  SiteCechComplex universal property and the given over-U transitions.
- Canonical cocone: the second formula characterizes its legs by restriction
  along every projection-compatible map from an original intersection to its
  stage intersection, using the supplied presentation q. Universality makes
  the characterization nonvacuous and unique.
- Canonical complex comparison isomorphism: the first `IsIso (colimit.desc ...)`
  uses the zero-extension functor `ComplexShape.embeddingUpNat.extendFunctor`
  on this same diagram and cocone. This is exactly the integer-indexed complex
  used by SiteCechComplex.integerComplexFunctor and coverComplex.
- Canonical cohomology comparison for every q ≥ 0: `∀ q : ℕ, IsIso ...`, using
  the homologyFunctor of the same nonnegative diagram and cocone. This is the
  coverCohomology convention; q=0 has zero incoming differential.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison:
  AlgebraicGeometry.Scheme.proEtaleSiteComparison and
  proEtaleSiteComparisonModules, the canonical inverse-image adjunctions.
- Sheaf.AlgebraicGeometry.ProEtaleFiniteModules:
  AlgebraicGeometry.ProEtale.FiniteCoefficientModules and
  finiteCoefficientComparison; their underlying abelian presheaf is used.
- Sheaf.AlgebraicGeometry.FiniteIntersectionLimitCompatibility:
  AlgebraicGeometry.Scheme.AffineProEt.firstLimitCoordinate and
  exists_finite_intersection_limit_compatibility; read the full statement,
  all its limit, affine and projection equations and its six-step docstring.
- Sheaf.AlgebraicGeometry.CoverCech and the upstream
  WeilConjectures.CategoryTheory.SiteCechComplex:
  CategoryTheory.SiteCechComplex, complex, cochains, integerComplexFunctor,
  cohomologyFunctor, coverComplex and coverCohomology.

Proof imports include ProEtaleComparisonSections (classical continuity),
Mathlib.Algebra.Category.Grp.AB (exact filtered abelian colimits),
Mathlib.Algebra.Category.ModuleCat.FilteredColimits (elementwise colimits),
Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit, and
WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits (homology and
exact colimits). The declaration docstring records all six DAG proof steps.

Edge cases checked mathematically: m=1 retains all repeated tuples; singleton
coordinate index sets give the original diagram; an empty U or empty
intersection gives zero section groups; F=0 gives zero complexes. No positive
characteristic, commutativity, injectivity, acyclicity, or étaleness over X is
assumed. Ind-étale first stages are permitted. Universes match the recorded
small-site and module interfaces (J_a : Type u, coefficients/sections at u+1).

Sources read: Stacks proetale.tex, lemma-limit-pullback (099S), lines 3841ff,
and lemma-affine-vanishing (099U), lines 3866ff, through the first two limit
calculations. The first calculation uses only section continuity and exact
filtered colimits; its initial injective-sheaf hypothesis is used later for
vanishing, so it does not belong in this node.

Searches actually run with msearch.py:

- leanfinder: `For a finite affine ind etale covering, canonical restriction maps
  identify filtered colimits of Cech complexes and Cech cohomology with the limit
  covering`: eight related affine-transition-limit declarations, no exact match.
- loogle: `CategoryTheory.SiteCechComplex, CategoryTheory.Limits.colimit`:
  zero hits, unknown identifier CategoryTheory.SiteCechComplex in the service.
- grep in CategoryTheory: `cechComplex|[Cc]ech.*[Cc]olimit|[Cc]olimit.*[Cc]ech`:
  two hits in Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean defining
  cechComplexFunctor; neither states this comparison.
- leansearch: `Cech cohomology finite covering classical proetale sheaf inverse
  limit`: eight general Čech-nerve, sheaf-limit and profinite-limit hits,
  no exact match.

Local rg searches in WeilConjectures and Sheaf included the exact item id,
Cech/colimit combinations, firstLimit, and refinement/restriction. The item id
has no upstream match. Nearby EtaleLimitFiniteCechComplexColimit changes the
base scheme and coefficient system and does not state this fixed-X pro-étale
first limit. AffineComparisonCechCocycleDescent combines both reductions and
only descends cocycles; it does not state the canonical complex and cohomology
isomorphisms here. The original CompactObject example is withdrawn; its node
now records the identical upstream definition.

No new nodes, dependency modules, statement corrections or mathematical disputes
are proposed. The only remaining theorem proof is the required sorry in
finite_basis_cech_first_limit. The prescribed dry run has verified the entire Lean module.

## Second reading by N9

This is the dispatcher's required sole-worker self-check, not an independent
approval; the maintainer independently reviews the delivery. With the current
node and saved file open, checked each binder and clause against the mapping
above: affine X; arbitrary finite discrete ring and left module sheaf; nonempty
finite basis cover; small nonempty directed coordinate presentations with their
original affine, étale and limit properties; ordered tuples with repetitions;
actual restriction transitions and cocone legs; the canonical integer-complex
colimit comparison; and every nonnegative cohomology comparison, including zero.
The SiteCechComplex universal property supplies the unique projection-compatible
maps quantified in the coordinate formulas, so neither formula is vacuous.
The stage helpers reuse firstLimitCoordinate and the supplied presentation cone.
No mismatch was found, no hypothesis was added, and the Lean source was retained
unchanged. The saved signature and node record agree verbatim. Only stale
verification metadata and this report were updated after the successful dry run.
