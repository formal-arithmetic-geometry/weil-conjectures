## Worker report

The module `Sheaf.AlgebraicGeometry.MonoschemeToricRealization` defines the fine
monoschemes, their actual toric realization, monomial ideals, canonical component
torus actions, saturated monoscheme blowups, and finite normalized scheme towers
of ILO, Exposé VIII. The primary declaration is
`AlgebraicGeometry.Monoscheme.Fine`; the Lean record lists every helper declaration.
No natural-language statement was changed. The saved packet was first tested with
`deliver2.py --no-push` and passed as dry-run commit `7134c45658`; its mechanical
success did not resolve the two independent-review findings on returned head
`084029194154`. This repair addresses both explicitly. Current main has the five
original statement dependencies and no Lean record for this item; comparison
confirms that only `lean` and `stmt_deps` change. The new dependency is the existing
normalized-blowup construction, recorded by `def-trf-normalized-blowup`; the
calculus theorem is no longer a statement dependency.

Clause-by-clause reading (names below are in `AlgebraicGeometry.Monoscheme`):

* The sheaf of commutative monoids is `Fine.space : SheafedSpace CommMonCat`.
  `affine P` uses the unsharpened `FineFan.spectrumSheaf P`, with the dependency's
  monoid-prime spectrum and actual local-fraction sheaf. `Chart` specifies a fine
  coordinate monoid and an isomorphism from the restriction to an open onto this
  affine model. `Fine.finiteCover` gives a finite family of these charts covering
  every point; it therefore includes the local-model condition and the finite-cover
  restriction in the node. No sharpness or saturation is assumed.
* `Hom.map` retains the continuous map and natural maps on sections of the
  sheafed spaces. `Hom.isLocal` is the dependency's `FineFan.IsLocalMorphism`:
  every induced map on actual monoid stalks is local, i.e. detects units.
* `Fine.IsTorsionFree` says that every positive natural power equal to 1 in
  every stalk's canonical group completion has base equal to 1. This is the
  additive condition ng=0 implies g=0. `Fine.IsSmooth` requires the finite
  products `Multiplicative (Fin r → ℕ) × Multiplicative (Fin t → ℤ)` at each
  stalk. `Hom.IsSmooth` requires an isomorphism from the original stalk times
  these two factors and the equation identifying the original stalk map with
  the first-factor inclusion. The natural-number and integer function types
  encode exactly the finite additive direct sums in the source.
* `sharpening` uses `FineFan.sharpSheaf`, the sheafification of the sectionwise
  quotient by units. `Fine.toFan` equips that exact space and sheaf with the
  dependency's fine-fan structure, using the named `sharpening_properties`
  proof obligation. No fan notion is copied.
* A field is bound explicitly by `(k : Type u) [Field k]`. `monoidAlgebra` uses
  Mathlib's `MonoidAlgebra k P`, the finite formal sums with basis multiplication
  induced by monoid multiplication. Monoids in Lean are written multiplicatively,
  including those used by the dependency; this is the additive notation of the
  node with 0 written 1. Its map is exactly `MonoidAlgebra.mapDomainRingHom`.
  `AffineOpens M` consists of the actual opens with an unsharpened fine affine
  model. `affineSections` restricts the given sheaf to them. `realizationDiagram`
  applies the monoid-algebra functor and contravariant `Scheme.Spec`.
  `realization k M` is Mathlib's actual colimit gluing of this specified diagram,
  not an arbitrary supplied scheme. `realizationι` are its chart embeddings;
  `baseCocone` and `realizationToBase` give its canonical structure over k.
  The named open-immersion and locally-directed obligations justify that these
  are precisely localizations and open gluing. Sections on an affine spectrum
  recover its coordinate monoid, so this gives the stated Spec k[P] charts
  independently of a selected atlas or selected coordinate isomorphisms.
* `IdealFamily`, `idealStalk`, and `IsIdealSheaf` spell out subsheaves of ideals
  on the unsharpened space: absorption, restriction, and local membership.
  `IsNonemptyCoherentIdeal` is local finite nonempty generation on germs.
  These use the dependency's actual stalk and germ constructions. The dependency's
  ideal-family types take a sharp fan, so their unsharpened variants are stated
  here on `Fine`, with the same recursive definitions, rather than assuming a
  sharpening identifies the ideals of the two different sheaves.
  `chartRingIdeal` takes the ideal span of exactly the monomials with exponents
  in `I U`, and transfers it through `Scheme.ΓSpecIso` to the affine chart's
  global sections. `ringIdeal` glues these by taking the infimum of their
  ideal-sheaf pushforwards. The pushforward is right adjoint to ideal pullback,
  so this is precisely the largest quasi-coherent ideal whose restrictions have
  the indicated memberships. For coherent monoid ideals their localization
  compatibility identifies the restriction with each chart's monomial ideal.
* `ToricComponent M` is now indexed by the original arbitrary `M : Fine`, with
  `component : ConnectedComponents M.space`, and torsion-freeness tested on
  exactly its points. It supplies neither a separate connected monoscheme nor
  a chosen generic point. `ComponentAffineOpens C` consists of affine opens of
  M whose points map to C's actual component class. ILO 3.1.10(ii) gives the
  unique generic point, fixed by `existsUnique_componentGenericPoint`.
  `ToricComponent.lattice` is the group completion of that ambient generic stalk.
* `realizationι_open` exposes that the actual realization chart maps are open
  immersions. `componentOpen k C` is the supremum of their open images for
  `ComponentAffineOpens C`. `componentRealization` is its actual open subscheme
  of `realization k M`, and `componentι` is its canonical inclusion.
  `componentChart` factors each ambient chart embedding through that inclusion
  by Mathlib's open-immersion universal property. `componentToBase` is the
  inclusion followed by M's structure map. Thus the torus acts on the specified
  open subscheme of k[M], with no unrelated realization or supplied map.
* `torus k C` is Spec k[L]. `degree` uses the actual ambient germ map on each
  component chart; `coaction` sends e^p to e^degree(p) tensor e^p. The generic
  stalk is a group and canonically identifies these degrees with the source's
  L. `chartProductMap` uses the canonical component chart embeddings and the
  prescribed k-structures. `IsCanonicalTorusAction` fixes every product-chart
  restriction to the Spec map of that exact coaction. `torusAction` uses the
  uniquely characterized morphism from `existsUnique_torusAction`.
* `IsComponentTorusEquivariant k C J` takes an ideal J of the ambient k[M],
  and compares its comaps along `torusAction k C ≫ componentι k C` and
  `pullback.snd ... ≫ componentι k C`. This is exactly restricting J to the
  component and comparing action/projection pullbacks. `IsTorusEquivariant k M J`
  quantifies over every torsion-free connected component of M. For torsion-free
  M these are all its components. No connectedness hypothesis on M is imposed.
* `AffineOpen`, `affineSection`, `affineGerm`, and `IsAffineMap` give the
  unsharpened chart maps, fixed on prime inverse images and canonical germs.
  `BlowupPatch` uses the dependency's exact `FineFan.saturatedChart`,
  `FineFan.chartInclusion`, and `FineFan.overlapElement`. Its chart models are
  our unsharpened `affine`, not sharp fans. Its generators are a finite nonempty
  generating set of the given ideal, and `GeneratedOnChart` specifies ideal
  generation on actual stalks. Its cover, over-base equation, and overlap
  equation specify gluing along D(b/a) inside the same original completion.
  The canonical map condition fixes the transitions on localized numerators.
  `IsSaturatedBlowup` requires these patches around every base point and
  nonempty coherence of the center, exactly as in the cited fan definition.
* `Tower` retains levels, arrows, centers, their order, and the saturated-blowup
  property of each step. `pullbackAlong` and `pullbackIdeal` generate pulled
  ideals on germs. `PullbackTower` requires these exact recursive pulled centers
  and commuting level maps. `Contraction` retains the order by a monotone
  surjection on levels, gives the level isomorphisms, identifies retained maps
  and centers, and collapses exactly whole-ideal isomorphisms.
* `IsNormalizedBlowup` requires a coherent ring ideal (finite generation on all
  affine opens) and an isomorphism over the original scheme to
  `J.normalizedBlowup`, using `J.normalizedBlowupMap`. These existing definitions
  are the ordinary `J.blowup`, constructed by the upstream blowup gluing from
  its affine chart fractions, followed by its componentwise function-field
  normalization. No arbitrary map is substituted for the canonical blowup map.
  `NormalizedTower.reduced` includes the reducedness restriction at every level;
  no normality or regularity of the input is added. Its ordered `center` data
  is retained even when a morphism is an isomorphism.
* `NormalizedPullback` uses the actual ideal-sheaf `comap` recursively and
  commuting level maps, with smooth maps as in the node. Each step in both
  towers is already the indicated normalized blowup.
  `NormalizedContraction.deleted` requires BOTH the unit ideal and an isomorphism;
  its retained-map and retained-center equations transport all undeleted data in
  order. In particular a nontrivial normalization with unit center is retained.
  `NormalizedTower.IsDesingularization` is precisely `IsRegularScheme` of the
  final level, using the recorded dependency including local Noetherianity.

Dependency declarations used:

* `Sheaf.AlgebraicGeometry.FineFanBlowup`: `AlgebraicGeometry.FineFan.IsFine`,
  `MonoidPrime`, `spectrumSheaf`, `sharpSheaf`, `stalk`, `germ`, `stalkMap`,
  `IsLocalMorphism`, `numerator`, `Fan`, `Chart`, `saturatedChart`,
  `chartInclusion`, and `overlapElement`. The full recorded source was read.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`;
  `Scheme.Spec` is the functor used in the realization diagram.
* `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization` and `Scheme.fromNormalization`, read with their
  integral-scheme binders and docstrings. These are used through
  `Sheaf.AlgebraicGeometry.ReducedNormalization`, which normalizes each actual
  reduced integral component and takes its disjoint union, including the empty case.
* `Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus`:
  `Scheme.IdealSheafData.normalizedBlowup` and `normalizedBlowupMap`, both
  read in full. Their definitions have no finite-type-over-Q restriction;
  that restriction belongs only to the calculus theorem, which is not assumed here.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  used on the scheme level maps without a substitute smoothness predicate.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  exactly local Noetherianity and the published stalkwise regularity predicate.

The definitions' named proof obligations all belong to this node's sharpening,
localization/gluing, or canonical-action clauses, and are listed in its Lean
record: `sharpening_properties`, `realizationDiagram_open`,
`realizationDiagram_locallyDirected`, `realizationι_over`, and
`existsUnique_torusAction`, together with the new component helpers
`realizationι_open`, `existsUnique_componentGenericPoint`,
`ToricComponent.generic`, `componentChart_range`, and `componentChart_over`.
Each is a named theorem with its entire proof `sorry`
and a source and complete natural-language proof in its docstring. No mathematical
theorem was proved. Functor-law, section-map, and pullback-lift witnesses only supply
the structural equations of the definitions. No definition contains `sorry` data.

Edge cases checked against the formulas: the empty monoscheme has a zero-chart
cover and its realization is the empty colimit (the empty scheme); all stalk and
ideal-cover conditions on it are vacuous. Toric components themselves are nonempty,
as a component with a generic point must be. Disconnected monoschemes remain
allowed and the torus acts on each nonempty component separately. The zero monoid,
rank-zero free factors, and length-zero towers all occur. Torsion is allowed for
fine monoschemes and their realizations, but not for the component torus designation;
in particular P=Z/2 gives μ₂ rather than being asserted to be a split torus.
Nonsaturated monoids are allowed. The unit-center cusp example
Spec Q[t] → Spec Q[t²,t³] fails the `IsIso` clause and cannot be contracted.
All universes and variables are bound explicitly; `autoImplicit` is false.

Searches for reuse:

* `msearch.py leanfinder`, query “Fine monoschemes unsharpened monoid spectra
  toric realization monoid algebra normalized blowup towers”: eight hits on
  normalization diagrams, relative normalization, Proj, and affine spaces;
  none defines monoschemes or their realization.
* `msearch.py loogle`, query “MonoidAlgebra, Scheme.GlueData, normalization”:
  no hits (the service did not recognize the abbreviated Scheme.GlueData name).
* `msearch.py grep`, query “Monoscheme|MonoidalSpace|toricRealization|normalizedBlowup”:
  no Mathlib hits. Direct Mathlib reads found and reused its monoid algebras,
  spectrum functor, locally directed open gluing, tensor-product spectrum
  comparison, and ideal-sheaf pullback/pushforward constructions.
* `rg` of the same notions in the upstream WeilConjectures tree and side
  `lean/Sheaf` tree found no monoscheme or toric-realization declarations.
  It did find the side normalized-blowup definitions, which were read and reused.
  Searching the item id upstream and in `dag/lean_names_upstream.json` found no
  recorded upstream implementation.

The full ILO source PDF was read via text extraction, including VIII 3.1.3--3.1.15,
3.2.1--3.2.4, 3.2.14--3.2.18, and 2.2.1--2.2.8. There is no
STATEMENT-DISPUTED flag and no statement correction. A module-system wrapper
cannot import the recorded legacy `FineFanBlowup` file; this new file therefore
uses legacy `import` syntax too, preserving the dependency as published.

## Repair of returned delivery

R1 (H2): removed the theorem `lem-trf-normalized-blowup-calculus` from the
saved packet's added dependencies. Added `def-trf-normalized-blowup` as an
`existing: true` definition node, citing `def-nagata-global-blowup` and
`def-weil-pbc-reduced-normalization`. It records exactly the two published
plain definitions in `Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus`.
There is no new Lean copy and no appeal to the calculus theorem.

R2 (H3): replaced the standalone connected `ToricComponent` with
`ToricComponent M` over an arbitrary fine monoscheme and its actual connected
component Z. Defined the component's open subscheme in k[M], canonical chart
maps, its torus and coactions, and componentwise equivariance for ambient ideals.
The use in `lem-trf-toric-monoid-comparison` (i) is now directly expressible
as `IsTorusEquivariant k M J`. The component actions required by
`lem-trf-toric-normalized-desingularization` are the canonical `torusAction`s on
these open subschemes, with `componentι` for restriction of centers; the tower
extension remains the downstream theorem's conclusion. The component tori and
coactions in `lem-trf-toric-realization-finite-type` are now indexed by actual
components of M. No citer or natural-language statement has been edited.

Additional edge cases: M may be disconnected and have torsion only on some
components. Only torsion-free components get a split torus; if M is wholly
torsion-free, every Z has the component datum, constructed by
`{ component := Z, torsionFree := fun x _ ↦ hM x }`. An empty M has no
component classes, so componentwise equivariance is vacuous and no generic
point is chosen from an empty type. A component chart is a nonempty affine
monoid spectrum, which has its empty prime as generic point; components form
open unions of such charts, so the generic-point characterization is not
vacuous. A rank-zero component has the trivial torus. Multiple components may
have distinct lattices and ranks; no global common lattice is assumed.

## New nodes

`def-trf-normalized-blowup` records the existing construction
`AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup` and its canonical
`normalizedBlowupMap` in `Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus`.
It is built from the ordinary global blowup and componentwise reduced
normalization, with exactly these two definition-node dependencies. ILO VIII
2.2.1 and 2.2.3 give the source construction on reduced noetherian schemes;
the published definitions implement the same formula more generally.
LeanSearch and LeanFinder returned relative-normalization declarations,
Mathlib grep returned no normalized-blowup definition, upstream grep no hits,
and side-library grep found exactly these two definitions. DAG definition-node
search found no separate normalized-blowup node, and `blueprint_refs.py search
'normalized blowup'` returned zero matches. The exact search outputs are stored
in its `mathlib_searches`. This new node reuses published definitions as
`existing: true` and therefore adds no module. Its empty-scheme behavior follows
the empty blowup gluing and empty component coproduct.

## Validation

The repaired module compiled cleanly through `scompile.py` both as a sandbox
module (5.5 s) and at its actual library module name (5.7 s). A scratch consumer
checks that arbitrary torsion-free M and every Z give a component, that its action
has a canonical map into ambient k[M], and that both ambient and per-component
ideal equivariance use ideals of that same k[M]. This scratch file is not delivered.
No theorem was proved: the component helpers are source-documented named proof
obligations, each included in `lean.declarations` with proof `sorry`.

The consumer compiled cleanly in 2.6 s. Delivery dry run passed server preflight
and per-file compilation: `OK (dry run): commit 79b1cc146b passes the preflight
and compiles; nothing pushed`. The staged set was exactly the item module, the
item node, the new existing-definition node, and this report.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
