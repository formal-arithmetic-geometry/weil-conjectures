## Worker report

Q40 states `lem-sfb-smooth-jacobian-canonical-line` in
`Sheaf.AlgebraicGeometry.SmoothJacobianCanonicalLine`, declaration
`AlgebraicGeometry.AlgebraicSpace.smoothJacobian_canonical_line`.
Its only postponed proof is the named theorem, with the source and all five
natural-language proof steps in its docstring. Definitions have actual data.
The original item statement, source, proof and proof dependencies are unchanged.
The only added statement dependency is the new definition node described below.

The auxiliary module `SmoothJacobianDiagonalData` defines the missing curve theta
normalization, diagonal construction and coherent comparison predicates, using
the existing Poincare and module machinery. It does not assume existence of the
polarization or of a coherent assignment: those are in the theorem's conclusion.

Clause correspondence:

- A scheme and a locally Noetherian base: the arbitrary `S : Scheme.{u}` is a
  common ambient scheme. Each `I : Input S` has its actual scheme base
  `I.family.base.left` and `I.noetherian : IsLocallyNoetherian ...`. Taking that
  base over itself recovers any base in the node. Allowing all schemes over the
  ambient base expresses its arbitrary iterated base changes in one category.
- Genus at least two and stable unpointed genus-g family: `Input.genus` and
  `Input.family : StablePointedModuli S genus 0`; its published
  `genus_at_least_two`, `stable` and `genus` fields have precisely those meanings.
  `Input.smooth` is `Smooth family.projection`. `proper` and
  `finitePresentation` merely record consequences of stability needed as
  instances by the upstream degree-zero functor; neither restricts the family.
- Represented degree-zero relative Picard fppf sheaf: `Input.J` is an algebraic
  space and `Input.representation` is an isomorphism of functors with
  `totalPicardZero`. At a test scheme that functor is the sigma of its actual
  base map and the published `picardDegreeSubfunctor ... 0`. The lift only matches
  the published Picard value universe. The functor is the underlying fppf sheaf;
  its restriction maps are the actual published ones. `GroupData` fixes every
  group map on every test by trivial class, tensor product and inverse class.
- Canonical theta principal polarization: `Polarization` supplies `D`, `P`,
  `axes`, `represents`, and an identity-preserving isomorphism `lambda` over the
  actual base. `Represents` is exactly the existing universal property for
  fibrewise algebraically trivial lines with identity rigidification, not a
  chosen unrelated dual. `ThetaPolarization` fixes the isomorphism by the local
  normalized difference of the degree-(g-1) effective-divisor theta line. It
  quantifies every etale base and every such Picard class. `AbelTest` uses actual
  finite flat Hilbert divisors, their line classes and Picard restriction maps.
  `ThetaIdeal` is the scheme-theoretic image characterization on all scheme
  tests, including nilpotents; `ThetaLine` is the dual ideal on every etale chart.
  `IsLocalAddition` and the two equations for `q` fix the actual maps in the
  difference formula. No global theta representative is assumed.
- A line module on the small etale site: `IsLine I.J (line ...)` is the published
  line predicate under the existing small ringed model equivalence. It occurs in
  the theorem conclusion, not as an assumed property of the constructed line.
- Diagonal Poincare normalization: `diagonal` is `pair (𝟙 _) lambda.hom ...`;
  `line` is exactly its tensor pullback of `P`. Thus B has real prescribed data.
  `IsDiagonalRigidification` makes the specified identity trivialization equal
  to the axis-induced `rigidificationPullback`, including its compositors.
- Symmetry: the first existential in the theorem is an isomorphism from the
  inversion pullback of this same line to itself. Its displayed equation says
  that it preserves the specified identity trivialization via the existing
  normalized rigidification pullback.
- Relative ampleness: `∃ M : Model ..., RelativelyAmple M`. `Model` is a scheme
  representing the given space over the actual base. `ordinaryLine` restricts
  the transported small-site module on the represented scheme's identity chart.
  For every affine open U, `RelativelyAmple` states invertibility and exactly
  `Scheme.Modules.IsAmple` of the restriction to the inverse image of U.
- Every locally Noetherian base change and every family isomorphism:
  `Assignment` quantifies all `Input S` and all `CurveArrow I' I`, with actual
  base arrow and cartesian curve square, without flatness/etaleness assumptions
  on that arrow. Base change gives such a square; an isomorphism of families
  gives one over the identity. `canonical` fixes the Jacobian map on every
  Picard class using `picardFunctorIsoOfIsPullback` of precisely that square.
  `comparison` is the required pullback line isomorphism and `normalized` makes
  it preserve the specified identity rigidifications. `map_id`, `map_comp`,
  `comparison_id`, and `comparison_comp` are explicit identity/composition
  equalities with the published tensor pullback comparators. They apply in
  particular to the three projections of triple fibre products.

Dependency declarations read and used:

- Mathlib `AlgebraicGeometry.Scheme`, `IsLocallyNoetherian`, `Smooth`, `IsProper`,
  `LocallyOfFinitePresentation`, `IsPullback`, and the Over category.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `AlgebraicGeometry.StablePointedModuli` (including its full genus/stability
  signatures), `IsStablePointedCurve`.
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`: `picardFunctor`,
  `picardFunctorGrp`, `toPicardFunctor`, `picardFunctorIsoOfIsPullback`;
  `Picard.Degree` and `Picard.DegreeMorphism`: `picardDegree`,
  `picardDegreeSubfunctor`. The recorded upstream relative APIs are used directly.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AbelianSpacePoincareData`:
  `Poincare.Pointed`, `product`, `fst`, `snd`, `pair`, `Axes`, `Represents`,
  `AxisEquivalent`, `IsLine`, `dual`, `schemeModule`, `pullbackComp`,
  `rigidificationPullback`, and `Pointed.baseChange`/`baseChangeMap`.
  All existing notions retain their original definitions and universe sizes.
- `WeilConjectures.AlgebraicGeometry.Hilbert.Defs`: `IsHilbertSubscheme`, the
  existing predicate defining the recorded `hilbertPresheaf` of
  `def-pc-hilb-functor`; `EffectiveCartier`: `Scheme.IdealSheafData.toModules`,
  `IsInvertible.isInvertible_dual_toModules`; `Scheme.Pic.ofIsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` and `Ample`:
  `Scheme.Modules.IsInvertible`, `Scheme.Modules.IsAmple`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`:
  `smallModuleTensorPullbackId` (only its ordinary, normalized identity map).
- Proof imports: `Sheaf.AlgebraicGeometry.AbelianSpacePoincareCalculus` and
  `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`. The theta existence and
  relative ample-locus proof nodes currently have no usable recorded modules;
  they are named in the postponed theorem's proof docstring and are not
  hypotheses of its Lean statement. Nothing waits on their future proofs.

Edge cases checked: empty base (all pointwise degree conditions are vacuous,
with the usual empty models); genus two (divisors of degree one); characteristic
2 (no division by 2, theta characteristic or square root); nonreduced bases and
scheme tests (scheme-theoretic image kernels, not geometric point sets); lack of
a global degree-(g-1) representative (only local theta characterization);
arbitrary nonflat base change; the identity base change and identity family
isomorphism; repeated base change and triple products. The ambient scheme has
no Noetherian requirement and adds no condition to the actual base. There is no
forced equality of independent site/coefficient universes and no replacement
of a canonical map by an arbitrary map or choice from a mere existence axiom.
No disputed statement or source correction was found.

Searches: all actual Mathlib search outputs are logged in `searches.jsonl` and
reproduced in the new node's `mathlib_searches`. LeanFinder for the canonical
relative Jacobian diagonal line returned eight irrelevant scheme-diagonal hits;
Loogle `"Picard", "polarization"` returned zero; Mathlib grep
`(Jacobian|theta|Poincare|picardFunctor)` in AlgebraicGeometry returned eighteen
Weierstrass-coordinate hits. LeanSearch for the canonical theta/coherent ample
line returned root-system polarization and analytic Jacobi theta hits.
LeanFinder for the degree-zero representation, translated Abel image and local
theta comparison returned affine-space and local-representability hits.
Project `rg` in both `lean/WeilConjectures` and `lean/Sheaf` found the existing
generic Poincare interfaces, which are reused, but no exact theorem or missing
curve-specific definition. Exact searches for `JacobianDiagonal`,
`ThetaPolarization`, `totalPicardZero` found zero. DAG text searches and
`tools/blueprint_refs.py search` for `Jacobian theta`, `rigidified diagonal` and
`diagonal Poincare` found no existing definition of this interface.

Primary source read: Deligne, Le lemme de Gabber, Section 4.1, printed pp.141--142,
https://www.numdam.org/item/AST_1985__127__131_0.pdf (PDF pages 11--12, zero based).
The diagonal autoduality pullback, ample symmetric line, identity normalization
and arbitrary-base-change formation match the node. The effective-divisor
normalization is the standard theta characterization already spelled out by
the node and its theta-polarization proof dependency.

Validation: both complete delivered modules compiled on the prescribed server
via `scompile.py`, individually and together in dependency order. There were no
errors or unexpected warnings. The helper file contains no `sorry`; the main
file has exactly the one requested named theorem with its postponed proof.

## New nodes

`def-sfb-smooth-jacobian-diagonal-data` owns
`Sheaf.AlgebraicGeometry.SmoothJacobianDiagonalData`. It defines represented
relative degree-zero inputs, the actual Picard group maps, the local
scheme-theoretic effective-divisor theta characterization of the polarization,
the actual diagonal Poincare line and induced rigidification, scheme models and
ordinary relative ampleness, and canonical coherent comparisons on all
cartesian family arrows. Sources are Deligne Section 4.1 and the usual Abel
image/theta and normalized-difference definitions (Milne, Jacobian Varieties
Sections 5--6 and Abelian Varieties I Section 8). The existing generic Poincare,
Hilbert, Picard, divisor-line and ampleness notions are imported rather than
copied. The searches above establish that the extra curve-specific interface
has no existing definition node or declaration. Its predicates merely specify
the normalization; the theorem asserts existence and all required properties.

## Second reading by Q40

The dispatcher explicitly started a single worker and forbids starting other
agents; the brief provides the maintainer's independent delivery review.
Accordingly this section records a final self-reread, not an invented independent
reader. I reread the node against both full files: every input and conclusion
has the correspondence listed above, including the rigidification formula,
theta definition on nonreduced tests, genuine ordinary ampleness, arbitrary
base changes, family isomorphisms and all cocycle equations. No mismatch or
statement change remains. Independent review is left to the assigned maintainer.
