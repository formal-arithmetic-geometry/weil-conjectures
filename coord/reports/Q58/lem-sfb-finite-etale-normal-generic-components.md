## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents` states
`AlgebraicGeometry.exists_finite_etale_normal_generic_components`, with its sole proof
`sorry`. It introduces no new definition, helper theorem, or dependency module. The node
is unchanged outside `lean`. Its Q48 stage-1 split was already reviewed and is preserved:
that split does not provide a Lean statement and does not prevent this stage-2 delivery.

Source read: `literature/stacks-project/pione.tex`, Tag 0BQL,
`lemma-finite-etale-covering-normal-unramified`, statement and both proof paragraphs;
`literature/stacks-project/morphisms.tex`, Tag 02GL,
`lemma-etale-over-field`, both parts and proof. The former explicitly gives finitely many
disjoint normal integral components; the latter identifies generic fibres as spectra of
finite separable extensions. The complete eight-step DAG proof is carried into the theorem
docstring, including the affine integral-closure identification and localization gluing.

Hypothesis and conclusion correspondence:

- `X Y : Scheme.{u}` and `p : Y ⟶ X` are the specified schemes and cover, in an arbitrary
  explicit universe. `[IsIntegral X]` supplies nonemptiness and integral domains on
  nonempty opens. Its standard stalk instances supply that every local ring is a domain.
- `[IsLocallyNoetherian X] [CompactSpace X]` render exactly the node's definition of
  Noetherian: locally Noetherian and quasi-compact. No finite-type-over-a-field assumption
  is added.
- `hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)` renders the remaining normality
  condition. Together with integrality these are exactly integrally closed local domains.
- `[IsFinite p] [Etale p]` render the two hypotheses on the cover.
- The finite indexing set is `Fin n`, for existential `n : ℕ`. Every finite set admits
  such an enumeration, so this introduces no size or nonemptiness restriction.
- `U : Fin n → Y.Opens` gives the actual component open subschemes `(U i).toScheme`,
  with their canonical inclusions `(U i).ι`. `∀ i, IsClosed (U i : Set Y)` makes these
  inclusions clopen. Pairwise `Disjoint` and `(⨆ i, U i) = ⊤` give precisely the disjoint
  union decomposition of Y, as subschemes with the restricted structure sheaves.
- The existential class family `hI : ∀ i, IsIntegral (U i).toScheme` supplies integrality
  and nonemptiness of every component. Its stalks are domains. The component clause
  `∀ y, IsIntegrallyClosed (...)` supplies their normality. The family is used as local
  instance data throughout the signature; it is not an extra hypothesis on the input.
- `IsFinite ((U i).ι ≫ p)`, `Etale ((U i).ι ≫ p)`, and
  `Surjective ((U i).ι ≫ p)` state all three properties of every component structure map.
- `F` is the existing `X.functionField`, and `F_i` is literally
  `(U i).toScheme.functionField`, rather than an unrelated chosen field. Existential
  `A : ∀ i, Algebra X.functionField (U i).toScheme.functionField` supplies the extension
  structure. The second projection identity of the generic-fibre isomorphism specifies
  its map to Spec F, while the first specifies its map to Y. Composing these identities
  with the pullback relation gives the canonical generic-point square over X. Thus A
  describes the maps induced by p, rather than arbitrary unrelated field extensions.
- `FiniteDimensional X.functionField (U i).toScheme.functionField` and
  `Algebra.IsSeparable X.functionField (U i).toScheme.functionField` state that every
  extension F_i/F is finite and separable, including over imperfect fields.
- `∃! e : (U i).toScheme ≅ X.normalizationIn (U i).toScheme.functionField` gives the
  canonical normalization identification. Its first equality makes it an X-isomorphism;
  its second equality says the generic map is the specified `toNormalization` map from
  Spec F_i, hence fixes that field. Uniqueness is with these compatibilities, not
  uniqueness of abstract isomorphisms, which could have Galois automorphisms.
  Finiteness and étaleness of the normalization structure map follow by transporting
  the stated properties of the component map along this X-isomorphism.
- The final existential isomorphism has source `∐ i, Spec (U i).toScheme.functionField`
  and target `pullback p X.fromSpecFunctionField`. This is exactly the displayed generic
  fibre decomposition, with the harmless inverse orientation. For each summand, its
  composite with the first projection is the component's generic-point map into Y;
  its composite with the second is Spec of the specified `algebraMap F F_i`.
- This actual coproduct decomposition into spectra of fields also expresses the
  concluding field-factor assertion. Primitive nonzero idempotents of its generic
  algebra are indexed by the summands, each attached to its particular component.
  Isomorphic field factors remain distinct summands; the statement does not identify
  factors merely by abstract field isomorphism class. Each component's normalization
  is already identified, with its finite étale map as above.
- `(n = 0 ↔ IsEmpty Y)` explicitly records the empty-cover convention. For n=0 both the
  component family and the generic coproduct are empty. There is no `Nonempty Y` binder.

Dependency declarations read and reused:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `IsIntegral`,
  including its `nonempty` and `component_integral` fields and the derived domain and
  irreducibility instances.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`,
  `Scheme.functionFieldOfComponents`, with its docstring directing integral schemes to
  Mathlib's `Scheme.functionField`. This integral-scheme clause is the one needed here.
  The module is publicly imported; Mathlib's generic stalk and field instances are used.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `IsFinite`, the affine-local finite-module definition.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Etale`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-fin-normalization-extension`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `Scheme.normalizationIn`
  and `Scheme.fromNormalizationIn`. Read the full field-extension section: these use
  `Scheme.fromSpecOfAlgebraFunctionField` and relative normalization of that map.
  The generic compatibility uses its actual `Scheme.Hom.toNormalization`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` and `algebraMap`.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable` (which already includes algebraicity in the field case).
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `pullback.fst`, and `pullback.snd`, with the existing scheme pullbacks.

The declared proof dependencies are imported privately, using their recorded modules or
Mathlib matches: `EtaleNormalComponents`, `EtaleFibreDiscreteSeparablePoints`,
`NormalSectionsFiniteProduct`, and the Mathlib modules for finite type/Noetherian schemes,
closed immersions, finite morphisms and composition, étale composition, properness,
quasi-finite morphisms, universally open morphisms, affine pullbacks, extensive categories,
and finite algebras being integral. The normalization and function-field proof dependencies
are also supplied by the public statement imports. No dependency needs a replacement.

Edge cases checked before writing: empty Y (n=0); the identity cover (one component,
F_i=F and the normal X equals its normalization); two copies of X (two distinct indices
with isomorphic fields); X=Spec F (the finite étale product-of-fields case); and imperfect
F (separability is required of the extensions, not perfection of F). X itself cannot be
empty because the node assumes integral. No characteristic, connected-cover, or
surjectivity assumption is added to p. The chosen finite indexing enumeration excludes
no finite indexing set or scheme universe. No statement dispute or correction is needed.

Actual searches:

- `msearch.py`, leanfinder: "A finite etale cover of a normal integral Noetherian scheme
  decomposes into normal integral components with finite separable function fields and
  equals their normalization". Eight hits, all generic relative-normalization APIs:
  `Scheme.Hom.normalizationOpenCover`, `toNormalization`, `instIsIntegralNormalization`,
  `instIsIntegralHomNormalizationDesc`, `instIsIntegralHomFromNormalization`,
  `normalization`, `instIsIsoToNormalizationOfIsIntegralHom`, and `normalizationDesc`.
  None states the component and generic-field theorem.
- `msearch.py`, loogle: `"normalizationIn", "Etale"`: zero hits.
- `msearch.py`, grep: `normalization.*[Ee]tale|[Ee]tale.*normalization|[Ee]tale.*[Nn]ormal`,
  subdirectory `Mathlib/AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the exact node id found only the
  proof-docstring reference in `Curve/TameRadicalNormalization.lean`, not a declaration.
- `rg` in those two source roots for `normalizationIn.*Etale|Etale.*normalizationIn|
  finite_etale_normal_generic|[Ee]tale.*normal.*components` found normal-component tools
  and their users, including `EtaleNormalComponents`, `NoetherianComponents`, and
  `NormalizationExtendsCover`, but no exact declaration. The existing normal-component
  result supplies the partition only; normalization-extending-cover results impose
  additional field-base hypotheses. The generic-component-splitting module was also
  read and concerns finite-type families after shrinking/base extension, not this theorem.

Validation: `scompile.py Q58 lem-sfb-finite-etale-normal-generic-components` compiled the
complete signature against the live server library cleanly in module mode, including the
existential component-integrality and algebra class families and all normalization and
coproduct terms. The final packet is checked again by the prescribed delivery dry run.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
