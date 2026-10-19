## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SmoothExceptionalBaseChange.lean` states
`AlgebraicGeometry.Etale.smooth_exceptional_base_change` with `sorry`. It defines four
actual comparison constructions in the same namespace, each belonging to this node:
`smoothExceptionalBaseChangeMap`, `smoothDualizingBaseChangeMap`,
`smoothSquarePullbackIso`, and `smoothDualityTensorBaseChangeIso`.
There is no postponed data or extra theorem. The theorem docstring reproduces all nine
DAG proof steps and their dependency lists. The blueprint source was read at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md`.
No statement correction, new node, or dependency repair is needed.

Hypothesis and clause matching:

- Finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is precisely the coefficient universe used by the recorded ordinary etale
  module-derived categories, for schemes in universe `u`.
- Positive annihilator: `(N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)`.
  The scalar equation is equivalent to `NA = 0` for a unital ring.
- Noetherian schemes: `{X S S' : Scheme.{u}} [IsNoetherian X]
  [IsNoetherian S] [IsNoetherian S']`.
- Invertibility: `hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s)`.
  This is stalkwise invertibility on the base, as in the smooth-tensor dependency;
  it pulls back to X, S', and their fibre product. No new coefficient restriction
  or characteristic hypothesis is imposed.
- Smooth, separated, compactifiable, pure dimension d: `(f : X ⟶ S)
  [IsSeparated f] [HasCompactification f] (d : ℕ)
  [SmoothOfRelativeDimension d f]`. SmoothOfRelativeDimension is the dependency's
  Mathlib predicate, not an additional geometric model.
- Arbitrary change of Noetherian base: `(g : S' ⟶ S)` with no morphism property on g.
- The fibre product, g', and f' are literally `pullback f g`, `pullback.fst f g`,
  and `pullback.snd f g`. Compactifiability of f' is the upstream base-change
  instance. Quasi-compactness needed by the exchange API is inferred from the
  Noetherian source, not an extra assumption on g or a boundedness condition.
- Ordinary unbounded complexes: every K binder has type `DerivedCategoryModule A S`.
  This unfolds to the derived category of `Sheaf S.smallEtaleTopology
  (ModuleCat.{u + 1} A)`; no completed, bounded, or constructible category appears.
- The canonical beta is `smoothExceptionalBaseChangeMap A f g K`. Its body applies
  `rightDerivedUpperShriekAdjunction ... (pullback.snd f g).homEquiv` to the inverse
  of the existing compact-support exchange at f^times K, followed by g^* of the
  existing counit. Invertibility of that exchange is the existing finite-coefficient
  unbounded compact-support base-change theorem. Thus this is exactly the specified
  transpose, with no arbitrary natural transformation parameter.
- First conclusion: `∀ K, IsIso (smoothExceptionalBaseChangeMap A f g K)`.
- The dualizing comparison b is `smoothDualizingBaseChangeMap A f g`: beta at the
  derived coefficient unit, followed by f'^times of `leftDerivedUpperStarUnitIso`.
  Its source is g'^* of `dualizingComplex ... f` and its target is the recorded
  `dualizingComplex ... (pullback.snd f g)`. The second conjunct asserts `IsIso b`.
- Tensor compatibility is the last universally quantified equation. Lean composes
  left to right: `g'^*.map phi_f ≫ beta` is the left side; the right side is
  `smoothDualityTensorBaseChangeIso.hom ≫ (tensor f'^*g^*K).map b ≫ phi_f'`.
  Both occurrences of phi are the dependency's `smoothTensorDualityMap`, with the
  existing projection-formula invertibility theorem passed to its hPF argument.
- The displayed domain identification is `smoothDualityTensorBaseChangeIso`: first
  `leftDerivedUpperStarTensorIso` for g', then tensoring the inverse-image square
  isomorphism `smoothSquarePullbackIso` with the identity of g'^* omega_f.
  The square isomorphism is built from `leftDerivedUpperStarComp` and
  `pullback.condition`. It is not an unspecified chosen isomorphism.
- Inverse image is written with `upperStar.leftDerivedFunctor` to match the existing
  canonical tensor and exchange APIs. `leftDerivedUpperStarIsoMapDerivedCategory`
  identifies this with exact inverse image extended degreewise to complexes, as
  required. The derived tensor is the existing K-flat total tensor `derivedTensor`,
  already recorded for def-kun-derived-tensor. The canonical tensor comparison
  derives the ordinary tensor comparison on complexes, agreeing with the recorded
  ringed-site construction at the constant coefficient ring; no second tensor
  construction or freely chosen monoidal structure is introduced.

Dependency declarations read and reused:

| Dependency | Module and declaration |
| --- | --- |
| thm-asd-smooth-tensor | `Sheaf.AlgebraicGeometry.SmoothTensorDuality`: `AlgebraicGeometry.Etale.smooth_tensor_duality`, `smoothTensorDualityMap` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, `SmoothOfRelativeDimension` |
| def-asd-compactifiable | `Sheaf.AlgebraicGeometry.CompactifiableOverField`, with the existing `WeilConjectures.Compactification.Defs`: `Compactification`, `HasCompactification` |
| def-weil-pbc-derived-categories | `Sheaf.AlgebraicGeometry.DerivedCategories`, `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `DerivedCategoryModule` |
| def-weil-pbc-inverse-image | `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `AlgebraicGeometry.Etale.upperStar` and `upperStarLowerStarAdjunction` |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`, `pullback.snd` |
| def-amb-etale-compact-support | `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `rightDerivedLowerShriekOfCompactification`, specialized by `rightDerivedLowerShriek` to the chosen compactification |
| thm-amb-etale-exceptional-adjoint | `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`: `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`; the associated existing functor and adjunction are `rightDerivedUpperShriek` and `rightDerivedUpperShriekAdjunction` |
| lem-weil-pbc-ringed-topoi-derived-tensor-pullback | `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`: `SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback`, with its K-flat representative characterization; the ordinary constant-coefficient realization is the existing `leftDerivedUpperStarTensorIso` |

The existing `WeilConjectures.SixFunctors.Etale.Derived.Exchange` theorem
`isIso_rightDerivedLowerShriekBaseChangeMap` and the construction
`rightDerivedLowerShriekBaseChangeMap` were read with full signatures and docstrings.
The comparison uses the chosen compactification followed by the canonical
compactification-independence comparison, exactly as the node's proof specifies.
The `UpperStarMonoidal.Comparison` definitions of the tensor and unit isomorphisms
were also read in full, including their representative descriptions.

Every recorded statement dependency module is imported. Proof dependency imports use the
recorded modules except for the K-flat resolution module described below. The proof-only nodes
`lem-amb-proper-coproducts-projection` and `lem-asd-ordinary-finite-p1-adjunction`
have neither a Lean record nor a Mathlib match in the supplied DAG, so there is no
module to import for them yet; neither is needed to type this statement.

Edge cases checked against the signature and definitions: d = 0 is allowed; empty X,
S, or S' is allowed; neither an inhabitedness condition nor a geometric-point choice
occurs. The zero coefficient ring is allowed (including annihilator N = 1). K = 0,
K = the coefficient unit, and unbounded complexes are all included. Identity and
arbitrary nonflat base changes are included without an invertibility assumption on g.
No finite global dimension, valuation-ring condition, orientation, bounded-below
condition, or coefficient-field assumption occurs. Universes follow the existing
module-sheaf encoding and do not identify site object and morphism universes.

Searches actually run:

- msearch leanfinder: `canonical smooth exceptional inverse image base change isomorphism
  and compatibility with tensor duality`. Eight hits concerning Kähler differentials
  and algebra tensor/base change; none states exceptional inverse-image base change.
- msearch loogle: `CategoryTheory.Adjunction, CategoryTheory.IsIso`. Twelve generic
  adjunction/equivalence results; none states this geometric theorem.
- msearch grep: `smooth.*baseChange|baseChange.*[Uu]pperShriek`. Twenty-one hits about
  stability of smoothness and algebra/Kähler base change; none is the statement.
- msearch leansearch: `For a smooth scheme morphism the canonical exceptional inverse
  image base change morphism is an isomorphism compatible with the dualizing tensor map`.
  Service unavailable, Internal Server Error; not treated as evidence of absence.
- rg of the node id and `smoothBaseChange|smooth_base_change` in WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json: only a downstream prose reference in
  SmoothGenericDirectImage, no declaration of this node.
- rg of `UpperShriek.*BaseChange|upperShriek.*baseChange|baseChange.*UpperShriek` in
  WeilConjectures: found `rightDerivedUpperShriekLowerStarBaseChangeMap`, whose full
  signature is the different exchange `Rg'_* f'^! → f^! Rg_*`, not the beta here.
  Its existence therefore does not discharge this node.
- rg of all five proposed declaration names in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no existing declarations with these names.

Validation: the final file compiled cleanly through scompile.py in both sandbox and
library modes (12.0 s and 12.6 s, respectively), with no errors or warnings. The
deliver2.py --no-push result is recorded below.

Proof-import interface fault found and handled: the server compile rejects the published
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` at lines 56 and 58.
The available `CochainComplex.IsKFlat` elaborates at the maximum of the site universes,
while the module attempts an independent coefficient universe; it also fails to
synthesize the module-presheaf tensor localization's IsMonoidal instance. This is the
recorded module of proof-only node `lem-pc-kflat-resolution`, not a statement dependency
or a construction used by this file. Its import is replaced by the smaller existing
upstream `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`. The fully read
`CochainComplex.exists_quasiIso_flat_kFlat` supplies precisely the K-flat flat-term
models needed by Steps 4 and 9 in the existing ordinary module-sheaf coefficient
category. The stronger degreewise-epimorphism clause of the generic resolution node
is not used in this argument. This changes no statement, no coefficient universe,
and no construction: the tensor and inverse-image comparison remain the previously
recorded canonical constructions. No copy of the faulty generic resolution interface
is introduced. Its owner should repair the published independent-universe record;
this delivery reports that library issue rather than modifying a proof-only node
outside its statement-dependency scope.

Final dry run: `deliver2.py NC prop-asd-smooth-base-change --no-push` exited 0 and printed `OK (dry run)`: commit `15e740ba93` compiles and passes preflight except for the independent second reading, which the next worker supplies. Nothing was pushed.

## Second reading by NC

I read the node statement, its blueprint source place (the opening statement and proof of
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md`),
and the complete Lean signature and definitions in
`lean/Sheaf/AlgebraicGeometry/SmoothExceptionalBaseChange.lean`.

The node introduces the following data and hypotheses, in order. (1) A finite commutative
coefficient ring (A), an integer (N\geq1), and (NA=0); these are rendered by
`(A : Type (u + 1)) [CommRing A] [Finite A]`, `(N : ℕ)`, `hN : 0 < N`, and
`hA : (N : A) = 0`. (2) Noetherian schemes (X,S,S'), rendered by the three
`[IsNoetherian ...]` instances. (3) Invertibility of (N) on the base, rendered exactly by
`hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s)`; this is the hypothesis of the
`thm-asd-smooth-tensor` dependency and pulls back canonically along the displayed maps.
(4) A smooth, separated, compactifiable morphism (f:X\to S) of pure relative dimension
`d`, rendered by `(f : X ⟶ S) [IsSeparated f] [HasCompactification f] (d : ℕ)` and
`[SmoothOfRelativeDimension d f]`. (5) An arbitrary base map (g:S'\to S), rendered by
`(g : S' ⟶ S)` with no property on (g).

The node's three conclusion clauses also match. The canonical map
`g'^* f^× K → f'^× g^* K` is the definition
`smoothExceptionalBaseChangeMap A f g K`; its body is the adjunction transpose of the
inverse compact-support exchange followed by the pulled-back counit, so it is canonical.
The first conjunct `∀ K : DerivedCategoryModule A S, IsIso (...)` states its isomorphism for
every ordinary unbounded complex. The coefficient-unit specialization is
`smoothDualizingBaseChangeMap A f g`, whose source and target are respectively the pulled-back
`dualizingComplex ... f` and `dualizingComplex ... (pullback.snd f g)`; the second conjunct
`IsIso (...)` is precisely the asserted (b:g'^*\omega_f\simeq\omega_{f'}). Finally,
the last universal equality is the tensor compatibility: its left side is pullback of the
canonical tensor map followed by beta, and its right side is the canonical pullback tensor
identification `smoothDualityTensorBaseChangeIso.hom`, then tensoring by (b), then the
primed canonical tensor map. Its source and target are the node's displayed identification
of (g'^*(f^*K\otimes^L\omega_f)) with (f'^*g^*K\otimes^Lg'^*\omega_f).
The terms `pullback.fst f g`, `pullback.snd f g`, and `pullback f g` are the recorded fibre
product and projections, not fresh objects. `DerivedCategoryModule`, `upperStar`,
`rightDerivedUpperShriek`, and `derivedTensor` are the declarations of the recorded
dependencies, so no alternate category, inverse image, exceptional functor, or tensor is
introduced.

Edge cases remain covered: (d=0); empty schemes and empty fibres; the zero coefficient ring
(including (N=1) when the annihilator equation forces it); (K=0), the coefficient unit,
and arbitrary unbounded complexes; identity, non-flat, and arbitrary base changes (g). No
inhabitedness, orientation, field, valuation, finite-global-dimension, boundedness, or
constructibility assumption is present. All scheme and coefficient universes are the shared
`u`/`u+1` universes of the dependencies; no independent small universe is introduced.

I repeated the existing-declaration searches with `rg` over `lean/Sheaf`,
`WeilConjectures`, Mathlib, and `dag/lean_names_upstream.json`, and used the recorded
LeanFinder, Loogle, grep, and LeanSearch queries in `searches.jsonl`. The hits are generic
smoothness/Kähler base-change or adjunction declarations; none states this exceptional
inverse-image base-change map or its tensor compatibility. The LeanSearch service was
unavailable, and the Loogle query containing an unknown identifier was treated as unavailable,
not as evidence of absence. The existing `rightDerivedUpperShriekLowerStarBaseChangeMap`
hit has the opposite exchange type and is not this node. Thus the four constructions and the
statement are not duplicate definitions.

No mismatch was found and no source, node, dependency, or Lean statement was changed in this
second reading. The only prior delivery issue was the missing second-reading section itself;
this section supplies it. `scompile.py` compiles the module cleanly with only the expected
`sorry` allowance, and the dry-run delivery is rerun after this report update.
