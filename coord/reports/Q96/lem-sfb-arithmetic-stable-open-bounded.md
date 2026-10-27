## Worker report

The module `Sheaf.AlgebraicGeometry.ArithmeticStableOpenBounded` states
`AlgebraicGeometry.arithmetic_stable_open_bounded`, with proof `sorry`. Its two
helper predicates give real formulas for the particular scheme-test comparison
and stable geometric-fibre condition that this theorem introduces. Neither
constructs an object using `sorry`, nor chooses a representative of an existence
theorem. There are no new independent notions or new nodes, no dependency-module
repairs, and no statement correction.

Read the five original stmt_deps, their records, and the declarations and
docstrings in ProperCurveModuli, CurveModuliGroupoids,
StablePointedModuliGroupoids, AlgebraicModuliStack, and Mathlib OpenImmersion.
Also read StablePointedCurve, NodalGeometricFibres, ProjectiveBundleMorphism,
OpenModuliSubstack, DmStackMorphismProperties, StackPointTopologyFlatLfpOpen,
and StackPointTopology to check the meanings used below. The source places read
were Stacks moduli-curves.tex, lemma-stable-curves (0E76),
lemma-stable-one-piece-per-genus (0E78), and lemma-stable-quasi-compact (0E9B),
with their proofs. The accepted eight-step DAG proof is transcribed into the
main theorem's docstring. The statement and proof of the DAG node are unchanged.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arithmetic base, no field-base assumption | `Spec (.of (ULift.{u} ℤ))`; the lift permits every scheme universe. |
| Integer genus at least two | `(g : ℕ) (hg : 2 ≤ g)`. Natural numbers cover exactly the integers satisfying this bound. |
| Existing proper, flat, finitely presented algebraic-space curve families, cartesian arrows | `ProperCurveModuli.category` and its `ProperCurveFamily` and `Hom`; these are imported unchanged. |
| Full subcategory with connected stable genus-g geometric fibres | `U : OpenModuliSubstack ...` and `∀ X, U.property X ↔ X.family.HasStableGeometricFibres g`. The helper quantifies over every algebraically closed `Ω : Type u` and every `a : Spec Ω ⟶ X.base.left`, then requires the actual presheaf pullback to be represented over that field by a `StablePointedModuli ... g 0` object. |
| Connectedness, nonemptiness, nodal stability, arithmetic genus | The representative is the recorded `StablePointedModuli`; its `.stable` uses `IsStablePointedCurve`, whose `HasNodalGeometricFibres` includes `ConnectedSpace` and dimension one, while `.genus` uses the finite dimension of Zariski H1 of the structure sheaf. No smoothness of the family is imposed. The label set is `Fin 0`. |
| Open substack in the scheme-pullback sense | The existing `OpenModuliSubstack` includes full inclusion, closure under cartesian arrows, and representation of every scheme 2-pullback by an open immersion, with projection comparison. |
| Algebraicity | `IsAlgebraicModuliStack U.category`, the imported etale-stack, algebraic-space-diagonal, smooth-surjective-atlas predicate. |
| Containment in the nonempty nodal locus | `∀ X, U.property X → X.family.HasNonemptyNodalGeometricFibres`. |
| An open for each ambient family | `∃ W : ∀ X : ProperCurveModuli ..., X.base.left.Opens`. |
| Every test map factors through the open exactly when its pullback is a stable unpointed genus-g family | For every `T' : Over ...` and `a : T' ⟶ X.base`, `(∃ b : T'.left ⟶ (W X).toScheme, b ≫ (W X).ι = a.left) ↔ ∃ Y : StablePointedModuli ... g 0, Y.RepresentsProperCurvePullback X.family a`. The helper is an isomorphism to `Limits.pullback X.projection (yoneda.map a)` commuting with its second projection, not an arbitrary unrelated stable family. |
| Compatibility with every base change | For every cartesian arrow `a : X ⟶ Y`, `W X = TopologicalSpace.Opens.comap ⟨a.base.left, a.base.left.continuous⟩ (W Y)`. The preceding factoring criterion also quantifies over every base map, independently of a choice of pullback object. |
| Over this open, the algebraic space is a scheme | For each X, `∃ Y : StablePointedModuli ... g 0` representing the presheaf pullback along `(W X).ι`. The actual total space is represented by `Y.curve`, not merely its set of points. |
| Global closed embedding in a projective bundle of a finite-rank locally free module | For that same Y, `∃ (E : Y.base.left.Modules) (hE : E.IsQuasicoherent), E.IsFiniteLocallyFree ∧ ∃ i : Y.curve ⟶ (...gradedAlgebraData ...).relProj, IsClosedImmersion i ∧ i ≫ ...relProjHom = Y.projection`. This is the canonical symmetric-algebra projective bundle used by the recorded stable-family definition. The base isomorphism in the representing witness identifies Y's base with the open. No trivialization or constant rank is assumed. |
| Equivalence over schemes with the unpointed stable moduli groupoid | An existential `BasedFunctor (BasedCategory.ofFunctor (StablePointedModuli.forget ... g 0)) U.category` with `.toFunctor.IsEquivalence`. The based-functor equation respects the projections to `Over (Spec ℤ)` and the categories retain all arrows and automorphisms. |
| Quasi-compact field-valued point space, using the smooth-atlas topology | `CompactSpace (ModuliPoints U.category)` with the existing `moduliPointTopologicalSpace` instance from StackPointTopologyFlatLfpOpen. This means every open cover has a finite subcover; the quotient uses field objects and common-extension isomorphisms, not just algebraically closed points or isomorphism classes over a fixed field. |
| Disconnected, nonreduced, non-Noetherian and empty test bases | No hypothesis at all is imposed on `X.base`, `T'`, or the cartesian arrow `a`; all these cases occur in the binders. |

`RepresentsProperCurvePullback` includes a base isomorphism because the existing
stable-family structure bundles its base. Its sheaf isomorphism has domain the
Yoneda presheaf of the *total curve* over the arithmetic base, and its equation
identifies the structural morphisms to the actual test scheme. Thus it is exactly
scheme representability over the specified base; it neither confuses the base
with the total space nor changes the family. The geometric helper only tests
individual geometric fibres. It does not assume the schematic or projective
nature of the total family which the theorem must conclude.

Dependency declarations used (module — names):

- `Sheaf.AlgebraicGeometry.ProperCurveModuli` — `ProperCurveFamily`,
  `ProperCurveModuli`, `ProperCurveModuli.category`, cartesian `Hom`.
- `Sheaf.AlgebraicGeometry.CurveModuliGroupoids` —
  `ProperCurveFamily.HasNonemptyNodalGeometricFibres`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` —
  `StablePointedModuli`, `StablePointedModuli.forget`, and its category instance.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack` —
  `CategoryTheory.IsAlgebraicModuliStack`.
- `Mathlib.AlgebraicGeometry.OpenImmersion` — `AlgebraicGeometry.IsOpenImmersion`
  (in the existing open-substack notion), and open subschemes and their inclusions.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack` —
  `CategoryTheory.OpenModuliSubstack` and `.category`. Its already-landed owning
  node `def-sfb-open-moduli-substack` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen` —
  `CategoryTheory.moduliPointTopologicalSpace`, using `ModuliPoints` from
  `DmStackMorphismProperties`. The already-landed owning definition node
  `def-sfb-stack-point-topological-space` is added to stmt_deps.
- The stable-family imports already provide `IsStablePointedCurve`, the canonical
  `SymmetricAlgebraSheaf.gradedAlgebraData` projective bundle, and module notions.
- Mathlib supplies `BasedCategory.ofFunctor`, `BasedFunctor`,
  `Functor.IsEquivalence`, `TopologicalSpace.Opens.comap`, `Limits.pullback`,
  `yoneda`, `IsClosedImmersion`, and `CompactSpace`.

The available proof dependencies are imported with plain `import`:
OpenStackAlgebraicLfp, ProjectiveHilbertPolynomialRepresentability,
StackPointTopology, ProjectiveBundleProper, and Mathlib Noetherian (the two
Noetherian Mathlib leaves). StablePointedCurve and
StablePointedModuliGroupoids are already public transitive/direct imports.
The following proof nodes have no Lean record or usable Mathlib declaration in
the read clone and therefore no module to import: the arithmetic nodal-stack
lemma, curve-H0/genus strata, fibrewise very-ample evaluation, nodal canonical
positivity/tricanonical lemma, nodal relative-dualizing line, projective
Hilbert-polynomial dimension, space-relative-ample locus, and stable-curve
pluricanonical linear series. These are proof-only prerequisites; the statement
does not assume their conclusions. The maintainer can add their proof imports
when they are stated, according to the project contract.

Searches actually run using `msearch.py Q96 lem-sfb-arithmetic-stable-open-bounded`:

- LeanFinder: `The arithmetic stable genus g locus in the moduli stack of proper curve families is open algebraic and quasi compact` — 8 hits, on universally open/proper/quasi-separated scheme morphisms and local morphism properties; no moduli statement.
- Loogle: `"StablePointedModuli"` — 0 hits.
- Mathlib grep: `[Ss]table.*genus|genus.*[Ss]table`, subdirectory `AlgebraicGeometry` — 0 hits.
- LeanSearch: `Stable genus g curves form a quasi compact open substack of proper curve families` — 8 hits on scheme quasi-compact covers and morphisms; no stable-curve moduli statement.
- Direct `rg` in `lean/WeilConjectures` for the item id, stable moduli and stable genus found no statement. Direct `rg` in `lean/Sheaf/AlgebraicGeometry` for stable openness, arithmetic stability, full moduli subcategories and point spaces found the existing ingredients listed above and field-only consumers, not this arithmetic theorem. The existing nodal_curve_stack_smooth theorem is over a field, not an exact match. The helper names were also searched; no declaration was found.

Edge cases checked before writing: g=2 gives the tricanonical dimension n=4
and polynomial 6t-1; characteristic 2 and 3 are included since no invertibility
condition is imposed; empty test bases have the vacuous geometric-fibre condition
and the unique factorization through their open; disconnected bases permit all
components and locally varying bundles; nonreduced and non-quasi-compact bases
are allowed in every test. Unstable curves are not accidentally admitted through
an unrelated model, because the presheaf isomorphism preserves the projection.
Nontrivial automorphisms are retained by using the full category and a based
categorical equivalence. No STATEMENT-DISPUTED issue or source-based correction.

Validation: `scompile.py` compiled both the sandbox module and its intended
library module, with no errors or warnings, after correcting one syntax typo.
There are no auto-bound implicits (`set_option autoImplicit false`). All
universes and every binder are explicit. Only the main theorem is postponed.

## Second reading by Q96

A separate reading pass by the same dispatcher worker reopened the item and
final Lean file. No additional agent was started, as the dispatch brief forbids
it; the maintainer supplies the independent review. I checked every row above
against the actual signature. In particular, `RepresentsProperCurvePullback`
uses the second pullback projection and the test-base isomorphism, so neither
the global scheme conclusion nor the genus condition is assumed at the ambient
family level. The full subcategory predicate is exactly the all-geometric-fibre
condition, the nodal containment is a separate conclusion, and openness is
scheme-test openness. The explicit W criterion covers every test map and its
cartesian-arrow equality supplies arbitrary-base-change compatibility. The
embedding witness belongs to the same representative family restricted to W.
The equivalence is a functor over schemes rather than an equivalence of point
sets. Compactness uses the already-landed smooth-atlas topology; no replacement
topology was defined. The only change to the original node beyond lean is adding
the two already-landed definition owners required by the signature. No
mathematical mismatch was found, and no statement was changed.
