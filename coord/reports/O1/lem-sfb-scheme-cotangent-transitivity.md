## Worker report

Item: `lem-sfb-scheme-cotangent-transitivity`.
Module: `Sheaf.AlgebraicGeometry.SchemeCotangentTransitivity`.
Main declaration:
`AlgebraicGeometry.CotangentPresentation.exists_schemeCotangentTransitivity`.

This is a statement-only delivery: one theorem with `sorry`, real construction helpers,
and a Prop structure collecting its clauses. No statement correction, new node, or
replacement dependency module is needed. The resolved stage-1 repair note was read;
the accepted four-step split and every non-Lean field of that split are retained.
Only `lean` and the permitted addition of already landed statement dependencies change.

The intrinsic construction dependency deliberately returns a section-normalized `System`
together with affine and lci comparison data. This theorem returns that same existential
package, with its existing `Properties`, extended by the transitivity properties. It does
not assume a new arbitrary cotangent object or a functoriality map. `sourceArrow` is exactly
`derivedChange` of the source square; `relativeArrow` is the base-change chain map for the
identity source, composed with the inverse of the section-normalized identity pullback.
All helper definitions construct maps from published maps, isomorphisms, and counits.
No object or arrow is selected using a mere existence theorem.

Clause-by-clause reading:

- Arbitrary morphisms of schemes: every field quantifies over `X Y Z : Scheme.{u}` and
  `a : X ⟶ Y`, `b : Y ⟶ Z`. The theorem constructs a family for all such morphisms at once.
  There are no geometric hypotheses on them. The ring and sheaf derived-category instance
  families only supply the localizations required by the recorded intrinsic presentation.
  Their universes are explicit: rings use `u+1` for derived Hom, scheme sheaves use `w`.
- The intrinsic complexes without an lci hypothesis: `cotangent (D.model a)`,
  `cotangent (D.model b)`, and `cotangent (D.model (a ≫ b))` are literally the dependency's
  standard-resolution sheaf complexes localized by `DerivedCategory.Q`. `D`, `F`, `E`,
  and `Properties D F κ E` retain the dependency's normalization, rather than a second
  construction of cotangent complexes. `C : Coherence` and `κ : Naive.Comparison C` are
  its existing representation data, with existence already recorded by their nodes.
- The derived category is the recorded `schemeDerivedCategory.{u,w} X`, built from
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)` and its existing abelian structure.
- The triangle: `TransitivityProperties.distinguished` says
  `Triangle.mk (sourceArrow D a b) (relativeArrow D a b) (δ a b) ∈ distTriang ...`.
  The objects of those arrows are precisely `La*L(Y/Z)`, `L(X/Z)`, `L(X/Y)`, and the
  shift of the first by `(1 : ℤ)`. Both non-boundary arrows are constructed before the
  theorem. The family of connecting boundaries is in the conclusion.
- Derived pullback uses `AlgebraicGeometry.derivedPullback`, computed by the retained
  `recordedDerivedPullbackCounit` on flat K-flat representatives. Ordinary pullback in
  every helper is `Scheme.Modules.tensorPullback`, never `Scheme.Modules.pullback`.
- Canonical source arrow: `sourceArrow` calls `D.square b (a ≫ b) a (𝟙 Z)` followed
  by `derivedChange D`. `SystemLaws.change_formula` from the returned `Properties`
  fixes the chain map on every standard differential generator, in every degree.
- Open restriction: `source_restriction` and `relative_restriction` state the two
  squares under arbitrary diagrams of open immersions `x`, `y`, `z`. `sourceRestriction`
  uses the recorded composition comparisons and the specified cotangent restriction
  arrow. `boundary_restriction` states the third shifted square for the same family
  `δ`, so restriction includes the connecting map. The existential shift structures
  are constrained by `shift_compatibility`: `NatTrans.CommShift` for the retained
  tensor-pullback counit fixes their canonical derived normalization.
- Source composition: `composition` uses `recordedDerivedPullbackComposition c a`. Its
  inverse identifies `L(c ≫ a)*` with `Lc* La*`. `Category.assoc` supplies only the
  necessary equality transport of the target composite. The resulting equation is
  exactly `u_(ac),b = u_c,(ba) ∘ Lc*(u_a,b)` in mathematical composition order.
- Identity source: `identity` compares `sourceArrow D (𝟙 X) b` with `sourceIdentity`,
  after the literal `id_comp` equality transport. `sourceIdentity` is the retained
  derived counit followed by the normalized tensor identity unitor on the standard
  complex. `identity_isIso` makes explicit that this is an identification; under it,
  the source arrow is the identity.
- Augmentations: `D.augmentation` is the dependency's already normalized chain map
  to the degree-zero complex of its existing `relativeDifferentials`. `augmentation`
  asserts `IsIso (augmentationH0 D b)` for every scheme arrow `b`; hence it includes
  both `b` and `a ≫ b`. `augmentationH0` is H0 of that augmentation followed by the
  standard single-complex H0 isomorphism, not an unspecified identification.
- Augmentation commutes with source functoriality: `augmentation_square` is the
  derived commuting square using `pullbackSingleComparison` (the retained derived
  counit) and the recorded `relativeDifferentialsPullbackMap`, put in degree zero.
- Flatness is assumed only for the final H0 identification and formula, as `Flat a`.
  `flat_identification` makes `pullbackAugmentationH0` an isomorphism to
  `(tensorPullback a).obj b.relativeDifferentials`; `flat_H0` asserts the required
  equality of H0(u) with the canonical differential map under these two induced
  identifications. There is no assumption of flatness elsewhere.
- The local formula is `differential_formula`: for every open `V`, scalar
  `r : Γ(X,a ⁻¹ᵁ V)` and `s : Γ(Y,V)`, the differential map sends `r • (1 ⊗ ds)`
  to `r • d(a.app V s)`. `relativeDifferentialsPullbackGenerator` is the published
  actual inverse-image/tensor/sheafification section. Thus it is literally the
  pure-tensor formula, not an abstract isomorphism of modules.
- No separatedness, finite type, Noetherianity, smoothness, or étaleness binder occurs.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.LciCotangentPresentation`: `CotangentPresentation.System`,
  `System.model`, `System.square`, `System.change`, `System.augmentation`, `cotangent`,
  `derivedChange`, `identityComplex`, `pullbackComplex`, `Properties`, and
  `exists_lciCotangentPresentation`. The signatures, defining terms, and source
  docstrings were read, including the section-generator normalizations.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionId`, publicly imported
  `Scheme.Modules.tensorPullback` and its explicit tensor-sheaf construction.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `linearMapEquivDerivation`. The existing scheme sheaf and derivation are
  `Scheme.Hom.relativeDifferentials` and `relativeDifferentialsDerivation` from
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`, already used by the
  intrinsic presentation. No second sheaf of differentials is defined.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` and `Flat.iff_flat_stalkMap`.
- Added existing node `def-a1-relative-differentials-pullback-map`, module
  `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `relativeDifferentialsPullbackMap`, `relativeDifferentialsPullbackGenerator`.
  The universal property, full signature, and actual generator definition were read.
- Added existing node `def-pc-derived-pullback`, module
  `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback` and
  `derivedPullback_spec` (the flat-resolution computation).
- Added existing node `lem-pc-recorded-pullback-composition`, module
  `WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition`:
  `recordedDerivedPullbackCounit`, `recordedDerivedPullbackComposition`. The original
  universal counit, actual composition lift, and its tensor associator were read.
- Mathlib helpers: `DerivedCategory.homologyFunctorFactors`,
  `HomologicalComplex.homologyFunctorSingleIso`, `singleMapHomologicalComplex`,
  `NatIso.mapHomologicalComplex`, and `Pretriangulated.Triangle.mk`.

All available proof-dependency modules are imported privately. The two currently
unstated proof nodes, `lem-sfb-injective-sheaf-cotangent-sequence-roof` and
`lem-sfb-standard-sheaf-cotangent-augmentation`, have no module to import; their
proof contributions remain in the main theorem's four-step natural-language proof.
They are proof prerequisites, not missing notions in this statement.

Sources read locally: `literature/stacks-project/cotangent.tex`, the full ringed-space
triangle and its proof (08T4), H0 identification (08UV), and scheme definition (08T2).
The node's four accepted proof steps are reproduced in the theorem docstring, including
the injective graph, localization at `(0,1)`, strict standard maps, K-flat pullback,
composition formula and flatness only for the H0 identification.

Edge cases checked mathematically before writing: identity `a` (zero relative complex,
identity first arrow under the tensor unitor), identity `b` (zero first cotangent
complex and canonical relative identity), composition with identity `c`, empty schemes
and empty opens (zero module sheaves, all restriction equations meaningful), nonflat
`a` (triangle and augmentation square still present; no unjustified H0 pullback
identification), singular/nilpotent and positive-characteristic schemes, nonaffine
and nonseparated schemes. There are no finite-variable, finite-chart, rank, or lci
assumptions. The maps are actual module/sheaf morphisms, so the scalar formula covers
all coefficients, including zero, and does not depend on a chosen affine presentation.

Searches (all through the prescribed wrapper or read-only source searches):

- LeanFinder: "Cotangent complexes of schemes form a canonical transitivity distinguished
  triangle compatible with pullback composition and augmentations". Eight hits on
  naive algebra cotangent modules, H1 and Jacobi–Zariski maps; no scheme theorem.
- Loogle: `cotangent, triangle`. No hits; diagnostic unknown identifier `cotangent`.
- LeanSearch: "Canonical distinguished triangle for cotangent complexes of morphisms
  of schemes". Eight hits on generic distinguished triangles and triangles of short
  exact sequences; no intrinsic scheme cotangent statement.
- msearch grep: `cotangent.*[Tt]ransitiv|[Tt]ransitiv.*[Cc]otangent`, subdirectory
  `AlgebraicGeometry`. Zero hits in Mathlib.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` with that pattern and the item id:
  the ring-only `CotangentTransitivityTriangle`, proof references, and the intrinsic
  lci dependency; no scheme transitivity declaration. The ring-only theorem was
  opened and is about `CommRingCat` cotangent complexes, not this node.
- Requested `grep -rn` of the item id in `lean/WeilConjectures`: zero hits.
- `rg` of `dag/lean_names_upstream.json` and upstream Lean for the new theorem name:
  no declaration clash. Existing differential-map and recorded composition nodes
  were found and reused, with their ids added to statement dependencies.

No STATEMENT-DISPUTED issue or source correction was found.

## Second reading by O1

This is a separate self-audit pass; no second agent was started, as the dispatch brief
explicitly prohibits that. The maintainer's independent review remains to be done.
I reopened the node and final module and matched each clause above. In particular,
I checked the direction of the recorded composition comparison (inverse in the source
composition law), the associativity transport, and the normalization of both maps in
the triangle. A first draft had only the first two restriction squares; I added
`boundary_restriction` and the counit-normalized shift data so that the connecting
arrow is also covered. I checked that both H0 identifications are induced by the
actual augmentations and that the flat identification is asserted to be invertible,
rather than assuming an unspecified isomorphism. The local formula uses the existing
pure tensor generator, and the theorem returns a normalized intrinsic system instead
of assuming the conclusion as input. No clause of the node is removed or corrected.
