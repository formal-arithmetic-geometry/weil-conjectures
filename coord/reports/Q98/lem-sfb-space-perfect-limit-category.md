## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectLimitCategory` states
`AlgebraicGeometry.AlgebraicSpace.isPerfect_spaceDerivedPullback` and
`AlgebraicGeometry.AlgebraicSpace.perfect_descent_affineLimit`, both with `sorry`.
It constructs `perfectLimitPullbackComparison` from the existing normalized derived
composition isomorphism and the cone equation. This helper has real data and is listed
in the owning node's `lean.declarations`. No independent notion is introduced.

Source read: `literature/stacks-project/spaces-perfect.tex`, Situation 09RH
(`situation-descent`) and Lemma 09RJ (`lemma-perfect-on-limit`), including its proof.
The pullback clause is the local strict-perfect argument of sites-cohomology Tag 08H6.
The item's original mathematical statement is unchanged. Five already landed definition
owners are added to `stmt_deps` so the notions actually used in the signature are cited.

Hypothesis and clause correspondence:

- The base is exactly `Spec (.of (ULift.{u} ℤ))`. The lift places the same integer ring
  in the universe of the schemes; it does not replace the coefficient ring of any module.
- Schemes and algebraic spaces are the existing `Scheme` and `AlgebraicSpace`.
  `D : Iᵒᵖ ⥤ AlgebraicSpace ...` supplies every stage, transition and compatibility law.
- A small nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. The index universe is the scheme universe, and a preorder
  does not impose an extra antisymmetry hypothesis.
- `hqc` is literally existence of a quasi-compact scheme `U` and a surjective etale
  atlas `yoneda.obj U ⟶ (D.obj i).obj.obj` at every stage.
- `hqs` uses `IsAbsolutelyQuasiSeparated`, whose definition quantifies over two affine
  scheme tests and asserts compactness of the point space of their fibre product.
  Over Spec Z this is the absolute quasi-compact diagonal criterion in the statement.
- `haff` uses `MapIsAffine`: every affine scheme test has a cartesian representing
  affine scheme. This is the recorded affine morphism notion, with no flatness assumed.
- `(c : Cone D) (hc : IsLimit c)` is the specified limit and its projections `c.π.app`.
- `DerivedModules` is the unbounded `DerivedCategory` of `SmallModules`.
  `SmallModules` is the recorded small affine-etale model, equivalent by actual
  chart restriction to the original small-etale module category. It retains the
  original section and module universe `u`, and the same regular-function ring sheaf.
- `[∀ i, HasDerivedCategory.{w} (D.obj i).SmallModules]` and the analogous instance
  on `c.pt` specify the common localization morphism universe. No equality between
  `u` and `w`, boundedness of derived objects, or extra geometric assumption occurs.
- Every occurrence of perfectness is the existing
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}` applied to the small
  structure sheaf. Its definition is an isomorphic representative complex with local
  bounded models, degreewise finite-free-retract splittings, and quasi-isomorphisms.
  Cover members may have different ranks and bounds. The small-model equivalence
  identifies these models with the same local models on the small-etale site.
- `spaceDerivedPullback` is the recorded total left derived functor of the specified
  module tensor pullback, computed on K-flat resolutions with flat terms. Its
  comparisons are fixed by the ordinary tensor formula and derived counits.
- Preservation of perfectness is `isPerfect_spaceDerivedPullback`, for any space
  map `f` over Spec Z and any perfect derived `E`; the conclusion is perfectness of
  `(spaceDerivedPullback f).obj E`. There is no affine or qcqs restriction here.
- The first conjunct of `perfect_descent_affineLimit` quantifies over every perfect
  `E : c.pt.DerivedModules`, and produces `i`, perfect `E_i`, and
  `Nonempty ((spaceDerivedPullback (c.π.app (op i))).obj E_i ≅ E)`.
  This is an isomorphism of derived objects, not just cohomology isomorphisms.
- For each fixed perfect pair `E_i,F_i`, the next conjunct quantifies over each
  derived morphism between their pullbacks to the limit and produces a stage
  `j ≥ i` and a morphism `f_j` between their transition pullbacks. The displayed
  equation says its canonical pullback equals the given morphism. This is
  surjectivity of the directed Hom-colimit map.
- The last conjunct states that two morphisms `f,g : E_i ⟶ F_i` whose pullbacks to
  the limit agree become equal after a transition `i ≤ j`. This is the elementwise
  injectivity assertion, applied at every stage. To compare representatives originally
  at two different later stages, first move both to a common stage `k`. Their objects
  are still perfect by the preservation theorem. Apply this same clause at `k` to
  the two transported maps. The resulting eventual equality is precisely equality
  in the directed colimit of sets. Conversely a bijective canonical Hom-colimit map
  immediately gives both displayed clauses. Thus this formulation neither drops nor
  strengthens the stated Hom bijection.
- `perfectLimitPullbackComparison` is the inverse of
  `spaceDerivedPullbackComp` evaluated at the stage object, followed by `eqToIso`
  for `c.w`. The equation conjugates `(Lq_j*).map f_j` by these comparisons, in the
  direction from `Lq_i* E_i` to `Lq_i* F_i`. No arbitrary isomorphism is a parameter.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, `EtaleSite`, `structureSheaf`, and `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  Mathlib `SheafOfModules.IsQuasicoherent`; its slice sheafification instances are
  reused. The module is publicly available through the small-model dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImage`, `moduleTensorPullback`, and their specified adjunction.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`. `def-weil-size-convention` is the metatheoretic convention,
  realized by the explicitly bound universes and localization assumptions.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback` and
  `spaceDerivedPullbackComp`; this imports the existing tensor pullback, its
  universal-property construction and ordinary tensor-normalized comparison.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`.
  Its public `AlgebraicSpaceSmallRingedModel` supplies `SmallModules`,
  `smallStructureSheaf` and `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `IsPerfectOnRingedSiteOfUniverses` and its local strict-perfect predicate;
  the latter uses `StrictPerfectCoefficientPackageOnSite`.

The nine already recorded proof-dependency modules are imported privately:
`StrictPerfectRingedPullbackModel`, `SheafSliceDerivedComparison`,
`SpaceQcqsDistinguishedSquareInduction`, upstream `LimitAffineTransition`,
`DerivedEtaleZariskiEquivalence`, upstream `PerfectAffineBoundedProjective`,
upstream `AffinePerfectColimitDescent`, upstream `AffineDerivedPullbackTensorTilde`,
and `ProjectionMateExact`. The other five proof nodes currently have no Lean record:
`lem-sfb-space-perfect-objects-compact`, `lem-sfb-space-perfect-source-hom-continuity`,
`lem-sfb-space-affine-limits-schematic-stages`, `lem-sfb-etale-detects-perfect`, and
`lem-sfb-space-distinguished-derived-gluing`. They are named in the proof docstring;
no unstated proof dependency is needed to type this statement. Their modules can be
added as proof imports when available. The full seven-step mathematical proof route
is carried by the main theorem docstring; preservation has its own proof docstring.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with “Perfect derived objects on inverse limits of qcqs
  algebraic spaces with affine transitions descend to a stage and Hom sets commute
  with filtered colimits”: 8 hits, scheme affine-transition/section-continuity lemmas;
  none is the algebraic-space perfect-category result.
- `msearch.py ... loogle '"Perfect", "colimit"'`: 0 hits.
- `msearch.py ... leansearch` with “Perfect derived complexes on an inverse limit of
  algebraic spaces descend and their morphisms are filtered colimits”: 8 generic
  complex-limit/localization hits, no match.
- `msearch.py ... grep 'perfect.*(limit|descen)|AlgebraicSpace' AlgebraicGeometry`:
  0 Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for perfect descent/limits found
  scheme perfect Hom continuity and affine ring-complex descent, plus the existing
  small-model and derived tensor pullback interfaces, but not this statement.
  The exact node-id search in `lean/WeilConjectures` found no declaration.
- Exact proposed declaration-name searches in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.
- Searches of `dag/nodes` for the perfectness and pullback-composition declarations
  identified the existing definition owners cited above; none was copied or replaced.

Edge cases checked: the index is required nonempty, exactly as in the source; no
least element is required. Singleton and constant diagrams remain allowed. Empty
spaces and zero complexes are allowed, since covering sieves, zero ranks, and local
bounded models do not demand a point or positive rank. The proof explicitly uses the
zero model for the empty affine. Ranks and bounds are local; no uniform amplitude is
added. All complexes and Hom sets are derived and unbounded. Transitions may be
nonflat. The helper works at `i = j`; its canonical identity transport does not assume
strict equality of identity pullback with the identity functor.

Compilation: `scompile.py Q98 lem-sfb-space-perfect-limit-category` compiled both the
sandbox and final library module cleanly, with no warnings, on 2026-10-24. Initial
elaboration required explicitly setting `(X := c.pt)` on projection pullbacks:
Lean otherwise attempted to infer the localization instance on an unreduced constant
functor object. This is an elaboration annotation only; no mathematical interface or
universe was changed.

No statement dispute, statement correction, new node, or dependency repair is needed.

## Second reading by Q98

A second pass by the same dispatcher worker reopened the item and the finished module;
no other worker was started, as this assignment forbids delegation. The maintainer's
independent reading remains separate. Checked the Spec Z base, the explicit nonempty
directed preorder, the literal atlas compactness hypothesis, the recorded absolute
diagonal criterion and affine-test condition, and the limit cone. Checked every
perfectness predicate against the existing local finite-free-retract definition and
the small-ringed-model equivalence. Checked that derived localization size `w` remains
independent of site size `u`, and only the participating categories are assumed to
exist. Checked the comparison orientation: inverse comparison on the source, pulled
back map, forward comparison on the target. Checked the Hom-colimit translation,
including comparison of representatives from two different later stages by moving to
a common perfect pair. The preservation theorem supplies the needed perfectness.
No mathematical mismatch was found. The explicit `X := c.pt` annotations fixed only
elaboration; the five landed definition-owner edges make the dependency record explicit.
