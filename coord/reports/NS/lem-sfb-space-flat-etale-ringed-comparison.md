## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFlatEtaleRingedComparison` states
`AlgebraicGeometry.AlgebraicSpace.mapIsFlat_iff_isFlatEtaleRingedMap`, with one
`sorry` and no definitions or proofs. The natural-language node, its proof,
and proof dependencies are unchanged. The two already-landed definition nodes
`def-sfb-space-morphism-properties` and `def-sfb-flat-etale-ringed-map` are added
to `stmt_deps` so that the statement uses their existing predicates.

Source read: `literature/stacks-project/spaces-morphisms.tex`, Tag 073C,
`lemma-flat-morphism-sites`, including its complete proof. It identifies geometric
flatness with flatness of O_X over f_small-inverse O_Y, via conservative geometric
stalks and Tag 04NG. Also read the source's `definition-P` and the compatible-chart
criterion preceding it, the recorded dependency declarations and their docstrings,
and the existing definitions of both predicates used in this statement.

Hypothesis and clause correspondence:

- “Let S be a scheme”: `{S : Scheme.{u}}`, with explicit `universe u` and
  `set_option autoImplicit false`.
- “Z,W algebraic spaces over S”: `{X Y : AlgebraicSpace S}`. This is the
  existing full subcategory of fppf sheaves with representable diagonal and an
  étale surjective scheme atlas, not a chosen presentation or a scheme restriction.
- “Any S-morphism h”: `(f : X ⟶ Y)`, with no flatness, representability, separation,
  Noetherian, finite-presentation, surjectivity or finiteness assumption added.
- “Flat on étale scheme charts”: `MapIsFlat f`. Unfolding the existing predicates
  gives `∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
  (b : yoneda.obj V ⟶ Y.obj.obj) (h : U ⟶ V), IsEtale a → IsEtale b →
  a ≫ f.hom.hom = yoneda.map h ≫ b → Flat h.left`.
  This is the same universal chart test as the node. Given an étale chart
  V → Y and an étale chart T → X ×_Y V, composition gives a compatible étale
  chart T → X and the scheme map T → V. Conversely, a compatible pair U → X,
  V → Y gives U → X ×_Y V, which is étale: both U and X ×_Y V are étale
  over X, and morphisms between étale X-spaces are étale. Thus every chart
  in either test occurs in the other. Neither test requires charts to be surjective.
- “Its canonical morphism of ringed small étale topoi, with h-sharp”: the existing
  `IsFlatEtaleRingedMap f` uses `enlargedDirectImage f RingCat` and the actual
  chart-normalized `enlargedStructuralMap f`. Its inverse image is specified by
  an adjunction to that direct image; its inverse-image structural map is the
  adjoint mate of exactly that structural map. These are the canonical ringed
  morphism of `lem-trf-space-enlarged-etale-ringed-site-model`. Restriction to
  scheme charts is its equivalence with the small étale ringed topos. The module
  imports the dependency's current recorded `SpaceCotangentRingMap` module as
  well, retaining its newer commutative-ring interface without redefining anything.
- “O_Z regarded by h-sharp as an h-inverse O_W-module is flat”:
  `IsFlatEtaleRingedMap f` requires the scalar-extension functor `E` along that
  specific ring map to be exact. The adjunction `E ⊣ restrictScalars α` fixes E
  up to unique adjunction-compatible isomorphism. This is O_X tensor over
  f-inverse O_Y. Exactness is equivalent to flatness of O_X as an f-inverse O_Y
  module: restriction of scalars is exact and conservative, and its composite
  with E is the tensor endofunctor in `def-pc-flat-sheaf-modules`. Consequently
  this predicate is precisely the existing definition of ringed flatness; the
  existential left adjoints do not allow an arbitrary structural map or functor.
  No replacement flatness definition is introduced.
- “If and only if”: the conclusion is `MapIsFlat f ↔ IsFlatEtaleRingedMap f`,
  containing both implications. The four-step proof docstring retains the
  canonical scalar-action identification, conservative-point criterion, atlas
  argument and converse for arbitrary, possibly nonsurjective charts.

Dependency declarations used/read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsEtale`, `EtaleSite`, `etaleTopology`, `structureSheaf`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`
  and `MapIsFlat`, owned by the added `def-sfb-space-morphism-properties`.
- `Sheaf.AlgebraicGeometry.FlatEtaleRingedMap`: `IsFlatEtaleRingedMap`, owned
  by the added `def-sfb-flat-etale-ringed-map`. Read its full definition.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `cotangentRingInverse`,
  `cotangentRingMap`, and the chart normalization determining their structural
  map. This is the current recorded module of the ringed-site dependency. The
  theorem uses its already available equivalent enlarged-site flatness predicate.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite` and
  `CategoryTheory.exactFunctor`. `FlatEtaleRingedMap` uses the latter exactness
  predicate for scalar extension; no specialization to constant ring sheaves.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and
  `Flat.iff_flat_stalkMap`, the scheme test inside `MapIsFlat`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, the scalar-action stalk test
  in the future proof.
- Proof import `Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative`:
  `geometricStalk_mono_epi_iso_iff`, `geometricStalk_inverseImage`, and
  `geometricStalk_structureMap`, with their operation and germ compatibility.
- Proof import `Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness`:
  `geometricStalk_flat_iff` and `flatAt_iff_chart_stalk`, especially the latter's
  quantification over every compatible chart and point over a point class.
- Proof import `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`.
- Proof import `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `CategoryTheory.stack_chartwise_smooth_etale_calculus` and composition calculus.
- `def-weil-size-convention` is metatheoretic, with no module to import. The
  existing predicates keep the original coefficient/module universe `u` and
  use canonical equivalences of site models, without a universe equality added
  as a hypothesis. `lem-sfb-ringed-site-conservative-flatness` currently has
  no recorded Lean declaration, so there is no module to import for this proof
  dependency. It is not needed to type this statement. Its role is retained in
  the unchanged proof and the theorem docstring; no downstream prerequisite is
  used to define one of the statement's objects.

Edge cases checked semantically against the definitions: empty source, empty
scheme charts, nonsurjective charts, the zero structure ring on an empty chart,
identity maps, and arbitrary base schemes and characteristics. The left predicate
uses all charts rather than one fixed atlas. Identity scalar extension is exact;
on empty sites module categories are trivial. The zero-ring case does not need a
nontriviality assumption. There is no degree, index set, or characteristic binder
to restrict. No statement fault or STATEMENT-DISPUTED concern was found.

Searches actually run (the msearch log is in this item's sandbox):

- `msearch.py leanfinder`: “A morphism of algebraic spaces is flat on etale scheme
  charts if and only if its structure sheaf is flat over the inverse image
  structure sheaf”. Eight hits, all scheme flatness declarations, including
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`; none states this space comparison.
- `msearch.py leansearch`: “A morphism of algebraic spaces is flat if and only
  if the associated morphism of ringed small etale topoi is flat”. Eight hits,
  including `AlgebraicGeometry.Flat`, `flat_iff`, `Flat.iff_flat_stalkMap` and
  `Flat.of_stalkMap`; none compares algebraic-space geometric and ringed flatness.
- `msearch.py loogle`: `"Flat", "Etale"`. Twelve hits, including scheme/ring
  étale-flat implications and descent statements; no ringed-to-space comparison.
- `msearch.py grep`: `flat.*ringed|ringed.*flat|AlgebraicSpace`. Zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for flat/ringed and `MapIsFlat`,
  and the exact node id: found the two existing definitions reused here, scheme
  and ringed-space results, and `HypercoverAugmentationFaceProperty` referencing
  this pending result only in its proof docstring. No existing theorem states it.
- `grep -rn` of the exact node id in `lean/WeilConjectures`: zero matches.
- `rg` of the proposed theorem name and exact item id in
  `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`: no
  declaration-name collision and no existing statement match.

Validation: initial `scompile.py` compiled the sandbox and named library module
successfully (3.4 s and 3.1 s), with no errors or non-sorry warnings. Delivery dry
run and final delivery are run after this report is written. No additional node,
dependency module, or natural-language statement correction is necessary.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
