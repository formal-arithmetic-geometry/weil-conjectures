## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.NonconstantCurveStalkTorsionFree` states
`AlgebraicGeometry.Scheme.Hom.nonconstant_curve_stalk_torsion_free`, with its entire proof
postponed by `sorry`. It introduces no definitions or additional nodes. The node is unchanged
except for its `lean` record. Its five proof steps are reproduced in the theorem docstring.

I read Stacks `curves.tex`, Tag 0CCK, lemma-flat and its proof, and `morphisms.tex`, Tag 0CC1,
lemma-dominant-between-integral, especially clauses (2) and (6). I also read the current
blueprint `sec-deligne-laumon-a1/sk-lem-wft-finite-map/lem-a1-finite-map-curve.md` and its proof,
whose generically etale argument is the ancestor recorded by this node. The extracted node
needs only an integral source and a curve target; no normality or source dimension is used
in the dominance, injectivity, or torsion argument.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`. The schemes are `{X Y : Scheme.{u}}`; the explicit
  universe `u` is arbitrary, and all variables are bound with `autoImplicit false`.
- The target's k-scheme structure is `(sY : Y ⟶ Spec (.of k))` and its curve assumption is
  `[IsIntegralCurve sY]`. This is the dependency's actual class: it extends `IsVariety sY`,
  which includes integrality, separatedness, local finite type and quasi-compactness (finite
  type); its additional field is `topologicalKrullDim Y = 1`. The recorded dimension
  comparison identifies this with the local-ring dimension convention in the node.
- Integrality of the source is `[IsIntegral X]`. There is no k-scheme structure required on
  X and no compatibility requirement on f, because this node asks for a scheme morphism.
- The morphism is `(f : X ⟶ Y)`. The two-point image assumption is exactly
  `(h_nonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂)`: it neither requires injectivity nor finite
  fibres, and allows arbitrary source dimension.
- `genericPoint X` and `genericPoint Y` are Mathlib's canonical generic points. They satisfy
  `IsGenericPoint _ Set.univ` by `genericPoint_spec` and are unique because schemes are T0
  and sober. Choosing them renders the node's eta_X and eta_Y without extra hypotheses.
- `f (genericPoint X) = genericPoint Y` is the generic-point image clause.
- `DenseRange f` says exactly that the image f(X) is dense in Y.
- The quantifier `∀ x : X` renders every source point, and `f x` is the node's y.
  `Y.presheaf.stalk (f x)` and `X.presheaf.stalk x` are its rings A and B.
- The two `IsDomain` conjuncts assert that A and B are integral domains, including their
  nontriviality; these are conclusions, not extra hypotheses.
- `f.stalkMap x` is the canonical induced ring homomorphism A to B and
  `Function.Injective (f.stalkMap x)` is its injectivity.
- The final clause quantifies over every `a : Y.presheaf.stalk (f x)` and
  `b : X.presheaf.stalk x` and asserts
  `a ≠ 0 → (f.stalkMap x) a * b = 0 → b = 0`. This is verbatim the node's explicit
  torsion-free condition for the scalar action a • b = phi(a)b. No arbitrary algebra
  structure or extra module instance is substituted for that action.

Dependency declarations read and used:

- `def-pc-curve`: `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`,
  `AlgebraicGeometry.IsVariety`, `AlgebraicGeometry.IsIntegralCurve`. Public import.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`. Public import; its nonempty and component-domain fields
  also imply the irreducibility used to select generic points.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, `genericPoint`, and
  `genericPoint_spec`. Public import. The same file supplies `IsGenericPoint.eq` for the
  uniqueness part of `lem-sc-scheme-sober`; scheme sobriety and T0 are in Properties.
- `def-weil-pbc-module-stalk`: `WeilConjectures.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj`. Public import of the recorded
  dependency. The ring stalks in this statement are the existing `TopCat.Presheaf.stalk`
  of the structure presheaf, the ring analogue specified in this node, rather than a new
  module-stalk construction; no separate module-sheaf object is needed here.
- `def-weil-locally-ringed-space-morphism`:
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`,
  `AlgebraicGeometry.LocallyRingedSpace.Hom` and its `Hom.stalkMap`. Public import. The
  actual scheme specialization is `AlgebraicGeometry.Scheme.Hom.stalkMap` in
  `Mathlib.AlgebraicGeometry.Scheme`, defined from `f.toLRSHom.stalkMap x`.
- Proof-only `def-pc-dimension` and `lem-pc-scheme-dimension-local-rings`:
  `WeilConjectures.AlgebraicGeometry.Dimension`, `AlgebraicGeometry.Scheme.dim` and
  `AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim`. Non-public import.
- Proof-only `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`. Non-public import.
- Proof-only `lem-sc-integral-scheme-stalks-in-function-field` is a Mathlib leaf, with no
  Lean record required: `Mathlib.AlgebraicGeometry.FunctionField`,
  `AlgebraicGeometry.Scheme.functionField`, `germ_injective_of_isIntegral`,
  `Scheme.germToFunctionField_injective`, `stalkFunctionFieldAlgebra`, and the instances
  `IsFractionRing (X.presheaf.stalk x) X.functionField` and
  `IsDomain (X.presheaf.stalk x)`. I read their signatures and the canonical specialization
  map underlying the algebra. Non-public import.

Edge cases checked mathematically before drafting: the identity of an integral curve gives
identity stalk maps and ordinary domain cancellation. A constant morphism (including any
map from a one-point source) fails the two-point image assumption, so is correctly excluded.
The empty source is excluded by integrality and the empty target by the curve assumption.
A local spectrum `Spec O_{Y,y} → Y` at a closed curve point has generic and closed images,
so is included; its stalk maps are localizations and injective. A source of dimension larger
than one, such as a product mapping to a curve factor, is allowed. Frobenius in positive
characteristic is included: no separability hypothesis is present. Singular and nonnormal
integral curve targets are allowed: this result only claims torsion-freeness, not flatness.
At the generic point the target stalk is a field, consistent with the cancellation clause.
The clause excludes a = 0, for which its conclusion would fail for b = 1.

Searches for an existing complete statement (actual responses in `searches.jsonl`):

- LeanFinder, query "A nonconstant morphism from an integral scheme to an integral curve
  sends generic point to generic point, has dense image, and has injective stalk ring maps
  making stalks torsion free": eight hits, including `genericPoint_eq_of_isOpenImmersion`
  (extra open-immersion hypothesis), `IsDominant` (only the notion), and germ injectivity
  for one integral scheme. None states this result.
- Loogle, `AlgebraicGeometry.IsDominant, Function.Injective`: only
  `isDominant_of_of_appTop_injective`, which instead assumes injectivity on global sections,
  an affine target, and compact source. I read its signature and docstring.
- Mathlib grep via msearch, `stalkMap.*injective|injective.*stalkMap|nonconstant|IsTorsionFree`
  in AlgebraicGeometry: nine hits. I read `IsAffineOpen.stalkMap_injective` and
  `stalkMap_injective_of_isAffine`, which need a zero-kernel hypothesis, and
  `stalkMap_injective_of_isOpenMap_of_injective`, which needs open and injective underlying
  maps and injectivity on global sections. None deduces these clauses from two image points.
- LeanSearch, query "A nonconstant morphism to an integral curve is dominant with injective
  maps on local rings and torsion free stalk modules": eight hits, including
  `Module.isTorsionFree_iff_algebraMap_injective`. That is an algebraic component only;
  it does not establish dominance or stalk-map injectivity.
- Direct rg searches of `lean/WeilConjectures` and `lean/Sheaf` for nonconstant, curve and
  torsion/stalk terms, and an item-id search in `lean/WeilConjectures`, found no exact
  statement. The existing `NonconstantNormalCurveMapFlat` has curve and base-compatibility
  assumptions on the source and normality on the target, and concludes flatness. Existing
  dense-etale stalk injectivity requires a locally Noetherian target and a dense etale
  locus. Neither is this node. The proposed full declaration name was also searched in
  Mathlib, both project roots, and `dag/lean_names_upstream.json`, with no collision.

No statement correction, disputed assertion, missing notion, or unusable dependency was found.

Validation: the module is checked with the prescribed server-only `scompile.py`; the dry run
and final delivery use `deliver2.py`. No local/global Lean build or direct repository mutation
is used. The maintainer supplies the independent second reading under the dispatcher's current
worker-delivery protocol; this report does not claim an independent review by its author.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
