## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantNormalProjectiveModel` states
`AlgebraicGeometry.equivariant_normal_projective_model`, with one sorry proof.
It introduces no definitions and leaves the node unchanged except for `lean`.
All variables and universes are explicit (`set_option autoImplicit false`).

Hypotheses, in the order of the node:

- A field k: `(k : Type u) [Field k]`.
- X and T are schemes: `(X T : Scheme.{u})`.
- X is integral: `[IsIntegral X]`. Normality is
  `hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)`; integral schemes
  have domain local rings, so this is exactly integrally closed domain local rings.
- X is proper and finite type over k: `f : X ⟶ Spec (.of k)` and `[IsProper f]`.
  Mathlib properness includes locally finite type, and universally closed implies
  quasi-compact, so this includes both parts of finite type, with no omitted hypothesis.
- T is integral and finite type: `[IsIntegral T]`, `g : T ⟶ Spec (.of k)`,
  `[LocallyOfFiniteType g] [QuasiCompact g]`.
- T is projective over k in the finite-projective-space sense: `[IsHProjective g]`.
- A finite group, without faithfulness: `(H : Type v) [Group H] [Finite H]`.
- Actions on k, X, T: `rho : H →* (k ≃+* k)`, `aX : H →* Aut X`,
  `aT : H →* Aut T`. A homomorphism into automorphisms includes the group laws.
- Semilinearity: `haX` and `haT`. The left action on the spectrum of k is
  `Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)`. The inverse is necessary
  because Spec is contravariant; it agrees with the landed semilinear Chow module.
- The equivariant k-morphism p: `p : T ⟶ X`, `hp : p ≫ f = g`, and `hequiv`.
- The specified induced function-field isomorphism: `e : X.functionField ≃+*
  T.functionField` and `he`, which says that its Spec map commutes with the
  canonical generic-point morphisms and p. These canonical morphisms are the
  spectra of the generic stalks, so the equation identifies e with the actual
  pullback of rational functions; it is not an arbitrary abstract field isomorphism.
- The specified dense open and its isomorphism: `U : X.Opens`,
  `hU : Dense (U : Set X)`, `hpU : IsIso (p ∣_ U)`.
- The normalization n:N→T is the canonical `T.fromNormalization` with
  `N = T.normalization`. These are exactly the dependency's construction in k(T),
  not an existentially chosen model or an extra hypothesis about its finiteness.
  N's k-structure is the composite `T.fromNormalization ≫ g`.

Conclusions, clause by clause:

- n finite and surjective: `IsFinite T.fromNormalization` and
  `Surjective T.fromNormalization`.
- n birational: the dense-open witness V with `IsIso (T.fromNormalization ∣_ V)`,
  together with the induced field isomorphism eN below. This matches the node's
  explicit meaning of birational, not merely dominance.
- N normal and integral: the explicit `IsIntegral T.normalization` conjunct and
  integrally closed stalks at every point of N. The canonical normalization already
  has an integral instance, allowing its function field to be used in the signature;
  the explicit conjunct still records this requested conclusion.
- N finite type over k: `LocallyOfFiniteType (T.fromNormalization ≫ g)` and
  `QuasiCompact (T.fromNormalization ≫ g)`.
- N projective over k: `IsHProjective (T.fromNormalization ≫ g)`.
- Unique semilinear lift: the witness `aN : H →* Aut T.normalization`, its scalar
  compatibility and n-equivariance, and the explicit equality `aN' = aN` for every
  other action satisfying those same two conditions. There is no faithfulness
  assumption and no demand for an equivariant projective embedding.
- pn equivariant: the final equation in the aN witness, using the original aX.
- pn proper, surjective, H-projective: the three conjuncts on
  `T.fromNormalization ≫ p`.
- The specified field identification: `eN : T.functionField ≃+*
  T.normalization.functionField` and its generic-point equation identify eN as n's
  actual pullback. The next equation uses exactly `e.trans eN` for pn's pullback,
  so the prescribed e is retained in the conclusion.
- pn is an isomorphism over the original U: `IsIso ((T.fromNormalization ≫ p) ∣_ U)`.
- If X is geometrically integral, T and N are: the final implication
  `GeometricallyIntegral f → GeometricallyIntegral g ∧
  GeometricallyIntegral (T.fromNormalization ≫ g)`.

Dependency declarations used (their source signatures and docstrings were read):

- `Field`, Mathlib.Algebra.Field.Defs (`def-weil-field`).
- `AlgebraicGeometry.IsIntegral`, Mathlib.AlgebraicGeometry.Properties
  (`def-pc-integral-scheme`).
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  and `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
  (`def-weil-finite-type-morphism`).
- `AlgebraicGeometry.IsProper`, Mathlib.AlgebraicGeometry.Morphisms.Proper
  (`def-weil-proper-morphism`).
- `AlgebraicGeometry.IsHProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective (`def-kun-projective`).
  Its finite coordinate type gives exactly an embedding in some finite-dimensional
  projective space; this is independent of the letter H for the acting group.
- `AlgebraicGeometry.Scheme.functionField`, Mathlib.AlgebraicGeometry.FunctionField,
  as explicitly required for the arbitrary integral-scheme clause of
  `def-sc-function-field`. The dependency's recorded module
  WeilConjectures.AlgebraicGeometry.FunctionField is imported publicly; its product
  definition for reducible curves is not the notion needed here.
- `AlgebraicGeometry.Scheme.fromSpecFunctionField`,
  WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField, the canonical generic-stalk map.
- `AlgebraicGeometry.Scheme.normalization` and `.fromNormalization`,
  WeilConjectures.Mathlib.AlgebraicGeometry.Normalization (`def-sc-normalization`).
- `AlgebraicGeometry.IsFinite`, Mathlib.AlgebraicGeometry.Morphisms.Finite
  (`def-weil-finite-integral-morphism`).
- `AlgebraicGeometry.Surjective`, Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
  (`def-weil-surjective-morphism`).
- `AlgebraicGeometry.IsOpenImmersion`, Mathlib.AlgebraicGeometry.OpenImmersion
  (`def-weil-open-immersion`): U is represented by the canonical open subscheme and
  morphism restriction, which use this existing open-immersion notion.
- `AlgebraicGeometry.GeometricallyIntegral`, Mathlib.AlgebraicGeometry.Geometrically.Integral
  (`def-pc-geometrically-irreducible`).

Already stated proof dependencies are imported: normalization existence and normal-locus
restriction in the upstream Normalization module; `finite_over_projective_affineLocally`
in Sheaf.AlgebraicGeometry.FiniteOverProjective; `hProjective_properness` in
Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper;
`geometricallyIrreducible_affineLocal` in
Sheaf.AlgebraicGeometry.GeometricIrreducibilityAffineLocal; the function-field fraction-ring
lemma in Mathlib.AlgebraicGeometry.FunctionField; and
`geometrically_integral_of_fractionRing_equiv` in
WeilConjectures.AlgebraicGeometry.FieldFractionRingGeometricIntegrality.
The two proof-only nodes `lem-sfb-finite-normalization-model-functoriality` and
`lem-sfb-finite-constant-projective-graph` have no recorded Lean declaration at inspection;
no import can be added for them yet. Neither is needed to elaborate this statement.
The declaration docstring contains all seven natural-language proof steps and their inputs.

Sources checked locally: varieties.tex lemma-normalization-locally-algebraic (Tag 0BXR),
morphisms.tex lemma-normalization-localization, lemma-normal-normalization, and
lemma-projective-over-quasi-projective-is-H-projective. Also read the current blueprint's
sk-thm-sf-ctf-stability-direct-images.proof.md, part (3), which locates this auxiliary
alteration input. No statement correction or missing notion was found.

Edge cases checked: a trivial finite group and nonfaithful actions are allowed; the group
universe v is independent of the scheme universe u. No invariant-open hypothesis is imposed.
U may be any dense open, including the whole scheme; in an integral nonempty X it cannot
be empty. Empty X or T are excluded exactly by the original integrality assumptions.
Zero-dimensional integral schemes and arbitrary characteristic are allowed. There is no
smoothness, perfection, separability, or geometric-integrality assumption; the latter is
only the premise of the final conditional conclusion. Normality of T is not assumed.
All scheme and function-field constructions use universe u, with no restriction on dimension.

Searches (2026-10-24):

- msearch.py leanfinder: "Normalization of an integral projective variety lifts a semilinear
  finite group action and is projective birational over a normal target". Eight results,
  including Scheme.Hom.normalizationDesc, toNormalization and constituent instances;
  none states the equivariant projective model lemma.
- msearch.py loogle: `"AlgebraicGeometry", "normalization"`. Twelve results, all constituent
  relative-normalization constructions and instances; no full statement match.
- msearch.py leansearch: "The normalization of a projective integral scheme is projective
  and carries a unique lift of any group action". Eight results, including
  Scheme.Hom.normalization.hom_ext and normalizationDesc; no full statement match.
- msearch.py grep: `(normalization|normaliz).*([Ee]quivariant|[Pp]rojective)|
  ([Ee]quivariant|[Pp]rojective).*normalization`, AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for semilinear action constructions found
  the landed SemilinearEquivariantChowModification and NormalAlterationConstantRegularization
  modules. Their actual action encodings and source docstrings were read and reused.
  Neither states this lemma. The exact node id has no hit in lean/WeilConjectures.
- rg for `equivariant_normal_projective_model` across lean/Sheaf, lean/WeilConjectures
  and dag/lean_names_upstream.json: no existing declaration.
- Source search for fromSpecFunctionField found the canonical upstream definition;
  it is used directly. No new canonical map or duplicate function-field definition is needed.

Validation: scompile.py compiled both sandbox and library module successfully (1.7/1.8 seconds)
with no errors or warnings. After the final explicit dependency-import additions,
deliver2.py --no-push compiled both forms again and passed maintainer preflight: OK.

## Second reading by Q80

The dispatcher forbids starting other agents; this is a separate rereading by the same worker,
not a claim of independent review. With the node and final signature open, checked each
hypothesis and conclusion against the mapping above. In particular, verified that Spec's
contravariance requires rho(h inverse), that both the input and output field isomorphisms
are constrained by the actual canonical generic-point maps, that the output composite uses
e.trans eN rather than an unrelated isomorphism, and that the unique lift compares with all
semilinear equivariant actions. Verified that the dense-open conclusion uses the given U,
not merely a smaller open, and that the geometric-integrality conclusion is an implication.
No extra hypothesis or missing clause was found. No new or dependency module is delivered.
The only final adjustment was making the existing morphism-property dependency imports
explicit; no mathematical statement changed. The maintainer supplies the independent review.
