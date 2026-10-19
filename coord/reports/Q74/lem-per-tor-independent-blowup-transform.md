## Worker report

The delivery states `AlgebraicGeometry.torIndependent_blowup_transform` in
`Sheaf.AlgebraicGeometry.TorIndependentBlowupTransform`. Its proof is `sorry`.
The module additionally constructs `idealPowerPullbackToStructure` from the published,
section-normalized tensor adjunction, and defines `HasStrictTransformBaseChange` as the
specified compatible scheme isomorphisms. These helpers have real bodies and no postponed
proofs. One new definition module supplies the adapted-coordinate condition described below.
The item's mathematical statement, proof and proof dependencies are unchanged.

The former worker's stale-dispatch objection concerns stage 1: the live item has Q96's
reviewed DAG split but no `lean` or `reviewed_lean` record. This delivery is its stage-2
statement, not another split. I read the live statement and all nine proof steps, the four
original statement dependencies and their recorded declarations, the stage rules, and ILO
X 1.6--1.7 in the local PDF (printed pp. 142--145). The statement retains the reviewed
adapted-coordinate repair; in particular it does not restore the false general-center
normal-crossings claim. There is no further statement correction and no disputed statement.

Hypotheses and conclusions are rendered as follows.

- `X X' : Scheme.{u}`, `[IsNoetherian X]`, `[IsNoetherian X']`, and `g : X' ⟶ X`
  render the morphism between Noetherian schemes, without a field or dimension restriction.
- `I : X.IdealSheafData` represents the actual quasi-coherent center ideal. Its closed
  immersion is `I.subschemeι`. The hypothesis `hI` is an existential codimension function
  `c : I.subscheme → ℕ` with `IsRegularClosedImmersionWithCodimension I.subschemeι c`.
  This existing definition asks for regular affine generators around every source point.
  Existentially quantifying their length function imposes no fixed codimension or local
  constancy hypothesis. It permits zero length and empty sources. The pulled-back ideal
  is `I.comap g`; its closed subscheme is canonically `X' ×_X V`.
- `hTor : PullbackStalkTensor.IsTorIndependent I.subschemeι g` is the published notion
  quantifying over every pair of points with the same image and every positive degree.
  For closed immersions this is equivalent to the node's affine condition
  `Tor_i^A(A',A/J)=0`: localize the affine Tor module at each prime of A' and at its
  image in A/J. If the center fiber is absent, the localized quotient is zero. Conversely,
  vanishing at all these points kills all localizations of the affine Tor module.
  The tensor factors are interchanged by the recorded Tor symmetry; there is no flatness
  assumption on g.
- The first conjunction gives regularity of `(I.comap g).subschemeι`, with an existential
  codimension function, using the same published definition as in the hypothesis.
- `∀ a : ℕ, ∃ e : (tensorPullback g).obj (I ^ a).toModules ≅
  ((I.comap g) ^ a).toModules, ...` gives every ideal-power isomorphism, including a=0.
  The equation `e.hom ≫ ...toModulesι = idealPowerPullbackToStructure g I a` pins it to
  the canonical multiplication map. That map is the adjoint of the actual ideal inclusion
  composed with `unitToPushforwardObjUnit g.toRingCatSheafHom`. The selected adjunction is
  uniquely normalized by sending a section to `1 ⊗ section`, so this does not choose an
  arbitrary isomorphism, change the pullback functor, or replace tensor pullback by ideal
  extension. Since the target ideal inclusion is monic, the equation uniquely specifies
  the factorization. It also forces compatibility of the isomorphisms with multiplication.
- The next existential is an isomorphism from `(I.comap g).blowup` to
  `pullback g I.blowupMap`, commuting with the projection to X'. The second projection
  is the unique universal blowup lift over X, so this is the canonical base-change
  isomorphism. The existing blowup is glued from affine Proj of the Rees algebra.
- The fourth conjunction quantifies over every second closed subscheme W. Its first two
  premises are regularity of W in X and of `I.comap W.subschemeι` in W. Its next two
  premises are Tor independence over X of W and of its intersection with the center.
  The intersection inclusion is explicitly the composite
  `(I.comap W.subschemeι).subschemeι ≫ W.subschemeι`.
  The conclusion gives regularity of the restricted pulled-back center on
  `(W.comap g).subscheme`, followed by `HasStrictTransformBaseChange g I W`.
- In that predicate the old transform is exactly `I.strictTransform W.subschemeι` and
  the new transform is `(I.comap g).strictTransform (W.comap g).subschemeι`, both using
  the existing scheme-theoretic-image construction. The target of eW is
  `X' ×_X W^st`, with the old transform's actual composite structure map to X. The two
  equations fix its projection to X' and its compatibility with the old ambient blowup.
  Thus the isomorphism is an equality of the specified closed subschemes under the
  canonical blowup comparison, including their nonreduced scheme structure.
- The fifth conjunction starts with `IsRegularScheme X → IsRegularScheme X' →` and
  quantifies over a finite component family `W : Fin r → X.IdealSheafData`.
  `∀ j, IsIntegral (W j).subscheme` and `Function.Injective W` express distinct reduced
  irreducible components, as in the node's component notation. Their Cartier sum has
  ideal `∏ j, W j`. Its normal-crossings condition and that of its actual pullback
  are the published `IsNormalCrossingsDivisor`; on these regular schemes the parameter
  presentation gives reducedness. Integral distinct factors of this Cartier product
  are exactly its irreducible components, so this is a component enumeration, not an
  extra irreducibility assumption on the entire divisor.
- `HasAdaptedNormalCrossingsCenter I W` is precisely the additional source coordinate
  condition, with boundary parameters z and independent parameters y. It is imposed
  on the source X only, and does not assume adapted coordinates on X'.
- Every nonempty finite component intersection is represented by `(s.sup W).subscheme`
  (supremum of defining ideals, not product). For each nonempty s the four hypotheses
  impose regularity of this inclusion and its restricted center, and Tor independence
  over X of both. The empty s is excluded exactly as in the node. The ambient center's
  regularity and Tor independence are already the outer hypotheses. The conclusion is
  `HasStrictTransformBaseChange g I (∏ j, W j)`, for the whole scheme-theoretic divisor.
- The last clause explicitly says `I = ⊥ → IsEmpty I.blowup` and quantifies over every
  morphism `j : Z ⟶ X` to assert `IsEmpty (I.strictTransform j)`. Thus the empty center
  sequence means V=X and gives empty blowup and transforms, exactly as stipulated.

Dependency declarations used (their signatures and docstrings were opened):

- `WeilConjectures.Compactification.StrictTransform`:
  `AlgebraicGeometry.strictTransform`, `strictTransformMap`, `strictTransformToSource`,
  and `Scheme.IdealSheafData.strictTransform` (the image of the open complement in the
  actual pullback).
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`, via the
  published regular-immersion definition and the ordinary list ideals in the new module.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`, via the existing stalk
  predicate, derived in the first factor with its actual scalar structures.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, namely
  local Noetherianity and regular stalks.
- `Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension`:
  `AlgebraicGeometry.IsRegularClosedImmersionWithCodimension`.
- `Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison`:
  `AlgebraicGeometry.PullbackStalkTensor.IsTorIndependent`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback` and `tensorPullbackSectionAdjunction`.
- `Sheaf.AlgebraicGeometry.NormalCrossingsDivisor`:
  `Scheme.IdealSheafData.IsNormalCrossingsDivisor`.
- `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters` (maximal-ideal generators of dimension length).
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.IdealSheafData`, `ideal_mul`,
  `ideal_pow`, powers and finite suprema; `Mathlib.AlgebraicGeometry.Properties`:
  `AlgebraicGeometry.IsIntegral`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModules` and
  `toModulesι`, the actual kernel ideal as a module and its inclusion.

The node's proof modules with recorded declarations are imported without `public`.
The two proof nodes with no recorded Lean module are not invented or restated:
`lem-per-noetherian-local-koszul-criterion` and
`lem-weil-pbc-regular-sequence-permutation-noetherian-local`. The homology-long-exact
node also has no recorded Lean module; its planned use is preserved in the proof docstring.
The nine proof steps in the theorem docstring retain the given Koszul, ideal-power,
Proj, Tor-acyclic resolution, strict-transform, chart and product-saturation arguments.

Edge cases checked: degree a=0; zero center ideal (V=X); unit center ideal (V empty);
empty ambient/source schemes; different local codimensions; no boundary components
(r=0 gives unit product and empty boundary); empty component intersections; m=0 or n=0;
empty center tuple m=n=0; and boundary components equal to a blowup pivot (their strict
transforms are empty on that chart). All use the actual ideals and schemes. No regularity,
nonempty center, positive codimension, flatness, field or characteristic hypothesis was
introduced. The component enumeration imposes no connectedness on X or X'.

Searches for an existing statement: msearch LeanFinder query
`Tor independent base change regular immersion blowup strict transform ideal powers`
returned eight results on immersion base change and flat regular sequences, none the
lemma. LeanSearch query `Tor independent base change of blowups of regular immersions
and strict transforms` returned eight results on flat regular elements and generic
base-change properties, none the lemma. Loogle query
`IsRegularImmersion, strictTransform, Tor\x27` reported unknown IsRegularImmersion;
quoted `"IsRegularImmersion"` returned zero hits. Mathlib grep
`torIndependent|TorIndependent|strictTransform|blowupBaseChange` in AlgebraicGeometry
returned zero hits. Project and upstream rg for the same notions found the recorded
stalk Tor-independence interface, strict transforms, the varying-codimension regular
immersion, and only flat/universal blowup inputs, not this theorem. Searching the item
id in upstream WeilConjectures returned no hit. DAG and blueprint searches for regular
closed immersions and adapted coordinates were also made. These searches caused me to
reuse `def-per-regular-closed-immersion-codimension`, rather than delivering a duplicate
regular-immersion definition. The adapted-center searches are recorded in its new node.

Validation: both delivered modules compiled cleanly using scompile.py, with the new
module supplied separately in dependency order. Observed library compile times were
2.3 seconds for AdaptedNormalCrossingsCenter and 2.8 seconds for
TorIndependentBlowupTransform. There are no warnings or unbound implicits. Definitions
contain no sorry; only the item's theorem is postponed. The initial omitted import for
Ideal.ofList and a guessed nonexistent Mathlib import were repaired before these checks.

## New nodes

`def-per-adapted-normal-crossings-center` owns
`Sheaf.AlgebraicGeometry.AdaptedNormalCrossingsCenter` and
`AlgebraicGeometry.HasAdaptedNormalCrossingsCenter`. It records the affine equations
for each component through the point, absence of the other components on that affine,
and I=(z_1,...,z_m,y_1,...,y_n), with the entire list z,y a sublist of a regular parameter
system. An injection labels exactly the components through x. Conditions only on the
closed center avoid excluding unit ideals away from it. Empty tuples are permitted.
Source: ILO X 1.7, printed pp. 144--145. The existing `IsPermissibleCenter` was read but
requires a center contained in the boundary and a nonempty center tuple. It therefore
cannot express the present condition. No other exact DAG, Mathlib or upstream definition
was found by LeanSearch, LeanFinder, Loogle, Mathlib/project grep and blueprint search.
The new definition uses the existing scheme, quasi-coherent ideal and parameter-system
nodes and is a direct statement dependency of the item.

## Second reading by Q74

Author's second pass with the live node and both files open; this is not an independent
review. As the dispatcher brief requires, no other agent was started. The maintainer's
independent review follows delivery.

I checked each clause against the rendering above. The varying-codimension dependency
allows every original regular immersion; the adapted coordinate definition does not
require the center to lie in the boundary; zero and unit ideals are retained; ideal
isomorphisms commute with the actual canonical multiplication map; strict-transform
isomorphisms commute with the ambient comparison; all nonempty component intersections
are present. In this pass I replaced a proposed local fixed-codimension wrapper with
existential use of the already published varying-codimension definition, deleting the
duplicate module. I also checked the new node's complete parameter and component-label
conditions against the source coordinate equations. No mathematical statement change,
weakening, hollow construction or extra proof obligation remains.
