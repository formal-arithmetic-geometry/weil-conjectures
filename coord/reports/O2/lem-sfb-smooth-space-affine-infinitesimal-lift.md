## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothSpaceAffineInfinitesimalLift` states
`AlgebraicGeometry.AlgebraicSpace.smooth_affine_infinitesimal_lift`, with its sole
proof postponed by `sorry`. It defines no new notion. The node's mathematical
statement and proof remain unchanged. The already landed definition node
`def-sfb-space-morphism-properties` is added to `stmt_deps` to use its generic
compatible-etale-chart test rather than duplicate that test.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`.
- The algebraic spaces over S are `{X Y : AlgebraicSpace S}`, and the S-morphism
  between them is `(f : X ⟶ Y)`. This is the recorded full subcategory of fppf
  sheaves over S, with its natural-transformation morphisms.
- Smoothness tested on etale scheme charts is `(hf : MapIsLocally (@Smooth) f)`.
  The existing `MapIsLocally` quantifies over *every* compatible pair of
  representable etale scheme charts and applies the supplied scheme morphism
  property to their map. With Mathlib `Smooth` this is exactly Stacks
  spaces-morphisms, definition-smooth and lemma-local-source-target.
- The two affine S-schemes are `(T₀ T : Over S)` with `[IsAffine T₀.left]` and
  `[IsAffine T.left]`. The immersion over S is `(j : T₀ ⟶ T)`, and
  `(hj : IsFirstOrderThickening j.left)` is the recorded conjunction of closed
  immersion and `j.left.ker ^ 2 = ⊥`. No merely topological thickening is used.
- The S-morphisms from the schemes are
  `(a₀ : yoneda.obj T₀ ⟶ X.obj.obj)` and
  `(b : yoneda.obj T ⟶ Y.obj.obj)`. These are exactly maps from their represented
  functors to the algebraic spaces. The representables use Yoneda on `Over S`,
  so all components and naturality are over S; there is no forgotten base map.
- The solid square is `(hcomm : a₀ ≫ f.hom.hom = yoneda.map j ≫ b)`, namely
  f composed after a₀ equals b composed after j.
- Existence of a global S-morphism is
  `∃ a : yoneda.obj T ⟶ X.obj.obj, ...`. The first conjunct
  `a ≫ f.hom.hom = b` gives f composed after a equals b; the second conjunct
  `yoneda.map j ≫ a = a₀` gives its exact restriction. No uniqueness or local-only
  existence replaces the existential.
- There is no separatedness, quasi-compactness, representability of f, or
  finiteness hypothesis in the Lean signature.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, through the public imports; the scheme and morphism signatures
  and docstrings were read directly.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, and `AlgebraicSpace.IsEtale`, through the
  public morphism-properties module. Its fppf-sheaf, diagonal, atlas and chart
  definitions were read in full.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  public; its affine-local smooth ring-map condition is the existing scheme
  notion recorded on `def-sbc-smooth-morphisms`.
- `WeilConjectures.AlgebraicGeometry.Thickening`:
  `AlgebraicGeometry.IsFirstOrderThickening`, public; its closed immersion and
  square-zero kernel conjunction was read in full.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`, public; the owning node's
  statement and recorded declaration were read before adding its dependency.

All currently stated proof-dependency modules are imported privately:
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`,
`WeilConjectures.CategoryTheory.Sites.Torsor` (owns both torsor inputs), and
`WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift`.
`lem-sfb-space-infinitesimal-lift-pseudotorsor` has no Lean record at this reading;
its future proof-only import is therefore absent. It is not needed to state the
item. The theorem docstring includes all five DAG proof steps with their node
names and explains the relative differentials/translation-module torsor route.

Source checks: read `literature/stacks-project/spaces-more-morphisms.tex`,
`definition-formally-smooth-etale-unramified`, `definition-formally-smooth`, and
`lemma-smooth-formally-smooth`, including both parts of the converse-direction
torsor proof. Also read `literature/stacks-project/spaces-morphisms.tex`,
`definition-smooth`. These give global existence for affine square-zero tests,
without separatedness or quasi-compactness. The source's Omega_X/S typo in the
finite-presentation paragraph does not occur in our statement or docstring.

Edge cases checked before drafting: the empty affine scheme is permitted (no
nonempty or nontrivial binder); j = identity is permitted (zero kernel) and the
conclusion allows a = a₀; f = identity requires precisely a = b and the square
supplies its restriction; the zero ideal and nonzero square-zero ideals are
both permitted; positive/mixed characteristic and non-Noetherian bases are
unrestricted. No uniqueness is asserted, since smooth affine lines allow many
lifts differing by the nilpotent ideal. Source/target charts need not themselves
be affine or quasi-compact. All schemes and their test schemes live in the same
universe u, as in the recorded algebraic-space fppf-site convention, so the test
universe is not smaller than the spaces' scheme universe. `autoImplicit false`
is set and the only universe u is explicitly bound.

Searches made (2026-10-24):

- `msearch.py ... leanfinder "Smooth morphisms of algebraic spaces admit lifts
  across square zero thickenings of affine schemes"`: eight hits, including
  scheme `IsSmooth`, `Algebra.Smooth.formallySmooth`, and
  `FormallyUnramified`; none states the algebraic-space lifting result.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace,
  AlgebraicGeometry.Smooth"`: zero hits, unknown Mathlib identifier
  `AlgebraicGeometry.AlgebraicSpace`.
- `msearch.py ... grep "FormallySmooth|IsSmooth|AlgebraicSpace"
  AlgebraicGeometry`: eight hits on scheme smoothness and ring formal
  smoothness, no algebraic-space result.
- `rg` in both `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry`, for `Smooth`, `Chartwise`, `IsSmooth`,
  `smooth.*lift` and `affine.*lift`: found the generic `MapIsLocally` chart
  test and existing stack tests, scheme infinitesimal criteria and references
  to this item, but no existing statement of the present lifting theorem.
- `rg` for the item id in `lean/WeilConjectures`: no hits.
- `rg` in `dag/lean_names_upstream.json` for smoothness names: scheme/formal
  scheme smoothness and curve notions, no algebraic-space lifting result.

No statement correction, new node, unusable dependency, or mathematical dispute
was needed. The sole dependency-list addition reuses an existing definition.

## Second reading by O2

The dispatcher explicitly forbids starting another agent; the delivery is for
independent review by the maintainer. No independent worker reading is claimed.
As a self-check, reread the complete node against the final signature: checked
base S; both algebraic spaces; the all-compatible-etale-chart smoothness
hypothesis; both affine tests; the actual square-zero closed immersion over S;
both natural-transformation test maps; the commuting solid square; existence of
one global map with each of the two exact equalities; and the absence of
separatedness or quasi-compactness hypotheses. The existing chart-test
predicate made a new smoothness definition unnecessary. No mathematical clause
was changed in this check.

Validation: prescribed `scompile.py O2
lem-sfb-smooth-space-affine-infinitesimal-lift <module>` completed successfully;
sandbox check 3.1 s, library-module check 3.2 s, with no errors or warnings.
