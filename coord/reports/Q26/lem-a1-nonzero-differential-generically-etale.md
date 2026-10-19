## Worker report

The delivery states `AlgebraicGeometry.nonzero_differential_iff_exists_nonempty_etale_open`
with a sorry proof and supplies the missing canonical differential map. The mathematical
statement of the item is unchanged. Its stmt_deps gains only the new definition node below.

I read Stacks `curves.tex`, lemma-generically-etale, Tag 0C1C, including its proof,
and `morphisms.tex`, lemma-functoriality-differentials, Tag 01UV, including the unique
characterization on local functions. The latter is the map appearing in 0C1C.

Hypothesis and clause correspondence:

- The arbitrary field is `{k : Type u} [Field k]`. There is no perfection, algebraic
  closure, or characteristic assumption.
- The k-schemes are `X Y : Over (Spec (.of k))`. Their structure maps are `X.hom`
  and `Y.hom`. `IsIntegralCurve X.hom` and `IsIntegralCurve Y.hom` use precisely
  def-pc-curve: integral, separated, locally of finite type and quasi-compact,
  with topological Krull dimension exactly one. This does not use the weaker IsCurve.
- The two smoothness assumptions are `Smooth X.hom` and `Smooth Y.hom`.
- An arbitrary k-morphism is `h : X ⟶ Y`. Its underlying map is `h.left` and its
  structure-map equation is `h.w : h.left ≫ Y.hom = X.hom`.
- The affine meaning of Ω is the existing `Scheme.Hom.relativeDifferentials`.
  Its docstring and full signature, universal derivation, and affine comparison
  `relativeDifferentialsSpecIso` were read in Modules/Differentials.lean.
  On Spec B the latter identifies Ω with tilde of `CommRingCat.KaehlerDifferential`;
  this is `KaehlerDifferential` for the ring-map algebra structure. The node's
  explanatory affine clause introduces this sheaf; it is not an extra hypothesis.
- The domain of `Y.hom.relativeDifferentialsPullbackMap h.left` is
  `(Scheme.Modules.tensorPullback h.left).obj Y.hom.relativeDifferentials`, using
  the dependency's actual tensor-formula pullback. The codomain initially uses
  the composite structure map. Composition with
  `(Scheme.Hom.relativeDifferentialsCongr (h.left ≫ Y.hom) h.w).hom` identifies it
  with `X.hom.relativeDifferentials`, without an arbitrary map or isomorphism.
- The local formula da ↦ d(h-sharp a) is the unique defining formula in the new
  map node. Its generator is explicitly the image of `1 ⊗ η(da)` under module
  sheafification, using the canonical abelian inverse-image unit.
- Nonzero means `... ≠ 0` in the module-sheaf Hom group. The biconditional is `↔`.
- The open subscheme is `V : X.left.Opens`; nonemptiness is
  `(V : Set X.left).Nonempty`. Its restricted morphism is `V.ι ≫ h.left`, and
  the final property is exactly `Etale (V.ι ≫ h.left)`.

Dependency declarations used, with their recorded modules:

- def-pc-curve: `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`,
  `AlgebraicGeometry.IsVariety` and `AlgebraicGeometry.IsIntegralCurve`; read the
  complete classes and their dimension and integrality fields in the shared source
  and confirmed the current source using `scompile.py --source`.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` (and relative-dimension definition for the proof plan).
- def-weil-pbc-kahler-differentials: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`.
- def-weil-etale-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (affine-local étale ring maps).
- def-pc-module-pullback: `WeilConjectures.AlgebraicGeometry.TensorPullback`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, with `tensorPullbackRingMap`;
  the current published source was read through `scompile.py --source` because
  the older upstream checkout has no such file.
- The new node imports and uses def-sc-relative-differential-sheaf's existing
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, its universal derivation,
  and its congruence isomorphism. No differential sheaf is defined again.

All recorded proof-dependency modules are imported as non-public imports unless
already public statement imports. This includes function fields, dimension/trdeg,
local finite presentation/type, tensor-pullback tilde comparison, Kähler localization,
module localization exactness, the unramified algebra product theorem, and normality.
`lem-a1-nonconstant-normal-curve-map-flat` has neither a Lean record nor mathlib_match;
it is a proof-only prerequisite, so there is no module to import. It is explicitly
named, with its role, in the theorem's proof docstring. No missing statement notion
is left unresolved.

Edge cases checked mathematically before writing:

- Empty schemes and dimension-zero schemes are excluded exactly by IsIntegralCurve;
  an empty open is excluded only in the conclusion. There is no rational-point assumption.
- For the identity, dh is an isomorphism and V may be the whole curve.
- A constant k-morphism between smooth curves has zero differential and has no
  nonempty étale restriction, for example a rational constant map of affine lines.
- In characteristic p the Frobenius of the affine line has zero differential and
  no étale open. Separable maps with ramification have nonzero differential and
  become étale after deleting the ramification locus; global étaleness is not asserted.
- Imperfect fields are retained. Geometric integrality and properness are not assumed.
- The new map is defined for arbitrary schemes over one base, including empty
  schemes and identity maps. Its uniqueness condition uses all local functions,
  not just global sections or an affine chart chosen in advance.
- All universes and binders are explicit; a single universe for schemes and field
  is the existing Scheme/Spec convention. No test-object quantifier is made vacuous.

Searches actually run with msearch.py under this item:

- LeanFinder: `A morphism of smooth integral curves over a field has nonzero differential
  if and only if it is etale on a nonempty open subset`: eight hits for general
  étaleness and étale loci, none the curve criterion.
- LeanSearch: `A morphism of smooth curves is generically etale if and only if its
  differential is nonzero`: eight general smoothness, formally-étale and unrelated
  manifold hits; no matching statement.
- Loogle: `AlgebraicGeometry.Etale, KaehlerDifferential`: zero hits.
- grep: `generically.?[eé]tale|relativeDifferentials.*[mM]ap|differentialMap`: four
  presheaf-differential restriction hits, no curve theorem or sheaf pullback map.
- For the missing map, LeanSearch queried `The canonical map from the pullback of
  the relative differentials of Y over S to the relative differentials of X over S
  sends db to d of its image`: algebraic KaehlerDifferential.map_D/map_d, derivation
  desc, and presheaf construction hits. These do not provide the scheme tensor map.
- For the map, LeanFinder queried `Canonical morphism h pullback Omega Y S to Omega
  X S defined on functions by db maps to d h b`: eight unrelated pullback/limit hits.
- grep: `tensorPullbackSection|relativeDifferentialsMap|differentialsPullbackMap|cotangentMap`:
  zero Mathlib hits. The same candidate names, and the final declaration names,
  were searched in upstream WeilConjectures, shared lean/Sheaf and lean_names_upstream.
  Searches for differential and generic-étale words found the consumer
  Curve/FiniteMapAffineLine.lean, not a declaration of this criterion.
- DAG grep for functoriality-differentials and canonical differential-map descriptions
  found algebraic cotangent-complex or unrelated coefficient maps, not this notion.
  `tools/blueprint_refs.py search 'relative differentials'` and
  `search 'canonical map of differentials'` both found zero blueprint nodes.
  The broader `search 'differential'` was also inspected. The ancestor tool gives
  `lem-a1-finite-map-curve`.

No statement correction or STATEMENT-DISPUTED issue remains. The two postponed
statements are the item's criterion and the new node's unique-existence assertion.
Both have full natural-language proof docstrings. The definition selects from unique
existence, which determines the entire morphism, as allowed by the non-hollow rule.

## New nodes

`def-a1-relative-differentials-pullback-map` states and defines the unique canonical
map for composable scheme morphisms h:X→Y and g:Y→S, characterized by
`1 ⊗ da ↦ d(h-sharp a)`. Source: Stacks 01UV, lemma-functoriality-differentials,
specialized to the identity on S. The statement cites exactly the existing relative
sheaf and module-pullback definition nodes. Its source proof constructs the map from
the universal derivation and the inverse-image/tensor adjunctions. This does not
repeat the curve criterion. Its three actual logged searches are recorded verbatim
in mathlib_searches; the blueprint and project searches above found no existing node
or sheaf-level declaration. The module contains the explicit tensor generator, the
matching unique-existence theorem with sorry, and the definition using that theorem.
No data is selected from a mere nonunique existence assertion.

## Second reading by Q26

This is the author's second reading; the dispatcher explicitly prohibits starting
another agent, and the maintainer performs the independent review. I reopened the
node and both module files and checked each of the correspondences above against
0C1C (1) and (4), and the helper against 01UV. The k-linearity condition is present
through Over, and both IsIntegralCurve assumptions are present. The target of dh
was checked carefully: the composite-base differential sheaf is transported using
h.w, so the proposition concerns Ω_{X/k} itself. Nonempty refers to the underlying
open set and Etale is imposed on its inclusion followed by h. The helper's tensor
unit is explicit, which avoids choosing an unnormalized adjunction. Its uniqueness
clause ensures the definition determines the canonical morphism. No hypothesis or
conclusion was changed on this second reading. There is no proof of a theorem in
this stage-2 delivery.

Validation: scompile.py compiled both delivered files separately in dependency order,
with no errors or warnings. The curve module compiled in 43.7 seconds and the map
module in 13.1 seconds in the library-mode checks. No time limit was raised.

The first dry run found only a signature-record formatting mismatch: preflight records
from the keyword `def`, excluding the preceding `noncomputable` modifier. The JSON
record was corrected accordingly; no Lean statement or definition changed.
