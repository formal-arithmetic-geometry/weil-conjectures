## Worker report

The item is stated by `AlgebraicGeometry.Scheme.Modules.flatBaseChangeMap_sections` in
`Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections`. It includes the resolution construction,
independence of every resolution and augmented lift, and the formula on every section class.
No statement correction was needed. There are two theorem proofs left as `sorry`: the main
statement and the inverse-image equality supporting the open-choice definition; the dependency
module also states its higher-direct-image theorem with `sorry`. All definition data are explicit.

Hypotheses and constructions, clause by clause:

- Schemes and morphisms: `{X S S' : Scheme.{uBC}}`, `(f : X ⟶ S)`, `(g : S' ⟶ S)`.
  The fibre product is Mathlib's chosen `Limits.pullback g f`, with `f' = pullback.fst g f`
  and `g' = pullback.snd g f`. Its square identity is `pullback.condition`.
- Both flatness assumptions are present: `[Flat g]` and `[Flat (pullback.snd g f)]`.
  The latter is also derivable by base change; retaining it renders the literal node.
- The module is `(F : X.Modules)` and `F'` is exactly
  `(tensorPullback (pullback.snd g f)).obj F`, using the dependency's tensor pullback.
- Nonnegative degree is `(p : ℕ)`. Resolutions are arbitrary `InjectiveResolution F` and
  `InjectiveResolution F'`. Their `ℕ` complexes encode zero negative terms, and their
  augmentations are `I.ι` and `J.ι`.
- The arbitrary lift `t` has type `I.cocomplex ⟶ (pushforward g').mapHomologicalComplex … J`.
  The displayed equation `I.ι.f 0 ≫ t.f 0 = unit.app F ≫ (pushforward g').map (J.ι.f 0)`
  is precisely `ta = g'_*(b) η_F`; equality in degree zero suffices since both augmentations
  have only that potentially nonzero component.
- `flatBaseChangePushforwardSquare` uses the standard `pushforwardComp`, `pushforwardCongr`
  of the projection identity, and inverse `pushforwardComp`. These are sectionwise identities,
  with the necessary equality transport between the two inverse-image opens.
  `flatBaseChangeResolutionQ` is `f_*t` followed by this comparison, hence the stated `q`.
- `flatBaseChangeResolutionC` is the inverse Hom equivalence of the canonical adjunction
  lifted to complexes. It is exactly the termwise adjoint `c`.
- `flatBaseChangeResolutionBeta` is the image of `c` under the homology functor. The explicit
  adjacent arrows are `I.isoRightDerivedObj`, exact pullback's `ShortComplex.mapHomologyIso`
  inverse, and `J.isoRightDerivedObj` inverse. Its type is exactly
  `g^* R^p f_*F ⟶ R^p f'_*F'`.
- The existential `beta` is equal to `flatBaseChangeResolutionBeta` for EVERY `I,J,t`
  satisfying the augmentation equation. Thus equality of the maps after canonical resolution
  comparison is explicit, including changes of resolutions and of lifts. Its adjoint is the
  actual expression `(Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv … beta`.
- Every open `V : S.Opens` is included. The new open-choice structure sets `U=f⁻¹V` and
  `W=g'⁻¹U`, with restricted morphism `g'.resLE U W le_rfl`. Its `psi` is the restricted
  adjunction unit, pinned by `unit_square`, rather than an arbitrary h-map. The square is also
  the canonical identification of `h^*(F|U)` with `F'|W`: the adjoint of `psi` is its
  tensor/inverse-image restriction comparison. Both resolutions are identified with the
  restrictions of `I,J` by augmentation-preserving isomorphisms, and their section-complex
  isomorphisms are pinned componentwise to `restrictAppIso`.
- The theorem asserts these auxiliary choices EXIST for every `I,J,V`; they are not extra
  geometric hypotheses, and the formula then holds for every such choice.
- The actual cohomology pullback on the right is the dependency's
  `moduleCohomologyFMap (g'.resLE U W le_rfl) D.psi p`, the h-map of the restricted unit.
  Cohomology of the open is written literally as `RingedSpace.moduleCohomology U.toScheme …`
  of `F|U`, with the additive forgetful functor. This is the node's `H^p(U,F)`.
- `D.sourceClass` and `D.targetClass` use `resolutionSectionClass`, the specified evaluation
  and resolution comparisons, the canonical `sectionCohomologyTheta`, and the inverse
  `isoRightDerivedObj`. They render the canonical `[xi]` and the canonical image of the
  pullback class, with no arbitrary cohomology isomorphisms. The equality of `W` with
  `f'⁻¹(g⁻¹V)` is transported by `flatBaseChangeOpenEquality` and `eqToIso`.
- The final equality is exactly `betaFlat_V([xi]) = [h^*xi]` for every `xi`.
  Since theta is the specified sheafification-universal map and `betaFlat` is a sheaf
  morphism, this also says it is induced by the stated presheaf maps, including their
  compatibility with restriction.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.condition`, with scheme pullback existence from
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`.
  The canonical unit is from `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`,
  `Scheme.Modules.exists_tensorPullbackAdjunction`, as required by the current convention.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`,
  `cocomplex`, `ι`; its full signature and the injectivity/quasi-isomorphism fields were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`: `moduleCohomologyFMap` and its resolution
  construction; its full module was read. The section formula uses this exact map.
- `Sheaf.AlgebraicGeometry.FlatModulePullbackExact`:
  `flat_module_pullback_exact_pushforward_injective`. The finite-limit/finite-colimit
  instances are its two exactness projections; additivity follows from finite products.
- The higher-direct-image dependency needs the accompanying dependency module below.
  It gives `sectionCohomologyPresheaf`, `sectionCohomologyComparison`,
  `sectionCohomologyTheta`, `higherDirectImageSections`, `directImageSectionClass`.
- Existing standard comparison tools include `InjectiveResolution.isoRightDerivedObj`,
  `ShortComplex.mapHomologyIso`, `Scheme.Modules.pushforwardComp`, `pushforwardCongr`,
  `restrictFunctor`, `restrictAdjunction`, and `restrictAppIso`.
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` supplies the existing
  `Adjunction.mapHomologicalComplex`; this is not redefined.
- Recorded cohomology is `RingedSpace.moduleCohomology` from
  `Sheaf.Topology.RingedSpaceModuleCohomology`. The dependency's canonical open-cohomology
  comparison uses `RingedSpace.openModuleCohomology` and `openModuleSections` from
  `Sheaf.Topology.OpenModuleCohomology`.

Sources read: the local literature tree has only citation/list files, so the text of Stacks
[02N7](https://stacks.math.columbia.edu/tag/02N7),
[01E4](https://stacks.math.columbia.edu/tag/01E4), and
[01FB](https://stacks.math.columbia.edu/tag/01FB) was read online. The source's square can be
any commutative square; the item's fibre-product square is retained exactly. Its derived
construction specializes to a module in degree zero and then to degree-p homology.

Edge cases checked before writing: `p=0` gives the adjoint of the ordinary sectionwise
pullback map; zero modules give zero classes and maps; `V=∅` gives zero section complexes
and the empty restricted schemes; `V=⊤` gives the global-cohomology formula. Empty source,
base, or fibre product is permitted by the scheme binders. No nonempty, proper, separated,
Noetherian, affine, quasi-coherent, or characteristic assumption is added. One scheme
universe is used throughout, with no quantification over tests in a smaller universe.
The choices are universally quantified and asserted nonempty, so no vacuous choice
hypothesis is used. Their resolution and section maps are pinned, preventing arbitrary
transport from weakening the formula.

Searches for the item (performed through the launcher search helper):

- LeanFinder, `flat base change map on higher direct image sections equals pullback on
  module cohomology`: eight results concern Mathlib module pullback, free sheaf pullback,
  and composition/adjunction; none states the O-module higher-direct-image section formula.
- Loogle, `Functor.mapHomology, InjectiveResolution.isoRightDerivedObj`: no hits; the first
  identifier is unknown. The actual homology and resolution comparisons were then read
  directly in Mathlib's source.
- Grep, `baseChange|higherDirectImage`, Mathlib/AlgebraicGeometry: 25 hits concern stability
  under base change, elliptic curves, gluing, and related scheme constructions, no match.
- `rg` of base-change and higher-direct-image names over `WeilConjectures` and `lean/Sheaf`
  found etale derived maps and the unbounded `schemeDerivedBaseChangeMap`, which has different
  categories and does not state this resolution/sections theorem. Searching the item's exact
  blueprint id in `WeilConjectures` found nothing. `dag/lean_names_upstream.json` and both
  source trees contain none of the introduced declaration names.
- The separate new-node searches are recorded below and verbatim in its `mathlib_searches`.

Compilation: all three modules were compiled together in dependency order by `scompile.py`
under the default limit. The final clean compile took 21.3 seconds and had no warnings.
A large single record initially exhausted elaboration heartbeats; factoring its source and
 target resolution identifications into `RestrictedResolutionSections` fixed the definition
without increasing any resource limit. No proof was attempted.

## New nodes

`def-weil-pbc-flat-base-change-open-choices`, module
`Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`, defines the restricted-unit h-map and
pinned restricted-resolution/section comparisons used to state the formula. The general
cohomology map, restriction, and resolution notions already exist and are reused. What was
missing was the canonical bridge from cohomology on the open subschemes to section classes
in the two higher direct images. The bundle states all its compatibility equations;
`resolutionSectionClass` is composed entirely from the standard comparisons and theta.
`flatBaseChangeOpenEquality` is the named theorem needed for its open transport, with
`sorry` and its elementary proof in the docstring. Sources are Tags 01FB, 01E4 and 01E1.

LeanSearch query `restricted injective resolution section complexes cohomology map flat
base change` returned Internal Server Error (recorded unavailable). LeanFinder query
`injective resolution restriction to open subscheme comparison section complex canonical
cohomology maps` returned eight hits, including resolution morphism identities, sheaf global
restriction, and scheme restriction formulas, but no such bundle. The exact results are
listed in the new node. Launcher grep `RestrictedResolutionSections|FlatBaseChangeOpenChoices|
sectionCohomologyTheta` in Mathlib/CategoryTheory returned zero hits. Direct `rg` over Mathlib,
`WeilConjectures`, `lean/Sheaf`, and upstream names returned no introduced names. Blueprint
search `restricted resolution` returned zero nodes. DAG search for restriction/resolution
found existing ingredients, especially module-open-restriction-injectives and
module-cohomology-fmap, rather than this pinned bridge. The new node cites those notions
through its statement dependencies and is cited by the item; no private copy is used.

## Dependency modules

`lem-weil-pbc-higher-direct-image-presheaf` has an unusable old record:
`AlgebraicGeometry.higherDirectImagePresheaf` merely quantified an unspecified presheaf,
unconnected to open cohomology, and an unspecified map to the derived object. Its clause
saying that a map from its sheafification exists to each sheaf is not the universal property
and is vacuous for module sheaves because the zero map exists. It does not specify the
canonical theta needed here. The dependency node's statement itself is correct and unchanged.

The replacement module `Sheaf.AlgebraicGeometry.HigherDirectImageSections` gives the actual
presheaf `H^p(forget(f_*I))`; its evaluation is section-complex homology. The explicit
`directImageSectionClass` identifies this with `RingedSpace.openModuleCohomology` on `f⁻¹V`
using the chosen resolution and exact evaluation. Its presheaf restrictions are the actual
section-complex restrictions, hence the recorded cohomology restrictions. The canonical
sheafification comparison is inverse exact-sheafification/homology comparison followed by
homology of the counit on the complex. `sectionCohomologyTheta` is its sheafification adjoint,
so it is precisely the cocycle-to-sheaf map. `higherDirectImageSections` states that comparison
is invertible, the actual unique factorization property of theta, that theta's induced map
on each module stalk is invertible, and degree-zero pushforward. The standard
`I.isoRightDerivedObj (pushforward f) p` identifies its cohomology sheaf with the recorded
higher direct image. The existing module cohomology definitions and the existing module
stalk functor are reused. Only the dependency's `lean` field is changed, with a note explaining
these defects; its statement, dependencies, and other records are unchanged.

## Second reading by R1

I read the item node, its statement dependencies and their recorded declarations, the three
source places (Stacks Tags 02N7, 01E4 and 01FB), and all three delivery modules. The
hypothesis/conclusion matching is as follows.

- The Lean binders `{X S S' : Scheme.{uBC}}`, `f : X ⟶ S`, and `g : S' ⟶ S` render the
  two scheme morphisms. `pullback g f`, `pullback.fst g f`, and `pullback.snd g f` render
  `X'`, `f'`, and `g'` with the stated fibre-product square.
- `[Flat g]` and `[Flat (pullback.snd g f)]` render the two flatness assumptions. No
  Noetherian, separated, proper, affine, quasi-coherent, characteristic, or finiteness
  hypothesis is added.
- `(F : X.Modules)` and
  `(tensorPullback (pullback.snd g f)).obj F` render `F` and `F' = g'^*F`, using the
  dependency declaration `Scheme.Modules.tensorPullback`.
- `(p : ℕ)` renders `p ≥ 0`; `InjectiveResolution F` and the corresponding resolution
  of `F'` render the nonnegative resolutions (their `ComplexShape.up ℕ` complexes have
  no negative terms), with augmentations `I.ι` and `J.ι`.
- `t : I.cocomplex ⟶ (pushforward g').mapHomologicalComplex ... J.cocomplex` and the
  displayed degree-zero equation render the augmented chain lift
  `ta = g'_*(b)η_F`. The theorem quantifies this equation before asserting equality with
  the single existential `beta`, so independence of every resolution and lift is present.
- `flatBaseChangePushforwardSquare`, `flatBaseChangeResolutionQ`, and
  `flatBaseChangeResolutionC` render respectively the sectionwise equality
  `f_*g'_* = g_*f'_*`, the pushed-down lift `q`, and its termwise adjoint `c`.
- `flatBaseChangeResolutionBeta` renders `H^p(c)` with the exact pullback homology
  comparison and the canonical resolution comparisons, and has exactly the node's source
  and target derived objects. The first conjunct states it equals `beta` for every valid
  `I,J,t`.
- `Nonempty (FlatBaseChangeOpenChoices f g F I J V)` renders existence of the required
  restricted open choices for every `V : S.Opens`; it is not an extra geometric hypothesis.
  The structure pins `U = f⁻¹V`, `W = g'⁻¹U`, the restricted unit map `psi`, the unit
  square, augmentation-preserving resolution comparisons, and the componentwise section
  identifications. `flatBaseChangeOpenEquality` transports `W` to `f'⁻¹(g⁻¹V)`.
- `sourceClass` and `targetClass` use the canonical resolution/homology comparisons and
  `sectionCohomologyTheta`, so they render the node's canonical section classes rather
  than arbitrary identifications. The final conjunct quantifies every `xi` and states
  that the adjoint of `beta` sends the source class to the class obtained by
  `moduleCohomologyFMap` for the restricted `g'` map, exactly the displayed formula.

The source reading confirms that Tag 02N7 constructs the map by lifting the adjunction unit,
pushing along `f`, and taking the `g^* ⊣ g_*` adjoint; Tag 01E4 identifies higher direct
images with the open-cohomology presheaf and its sheafification; Tag 01FB specifies the
resolution-based cohomology arrow. The Lean construction follows these steps. No mismatch
with the node was found, so no statement correction or citer update was needed.

Edge cases checked: `p = 0` uses the same degree-zero derived comparison; zero modules and
zero section classes are admitted; `V = ⊥` gives empty inverse-image opens and the same
quantified formula; `V = ⊤` gives the global-section case; empty schemes and empty fibre
products are allowed by the scheme binders. The single universe `uBC` is shared by all
schemes, modules and open sections, so no test universe is inadvertently excluded.

Searches were repeated with launcher LeanFinder/Loogle queries for flat base change maps,
resolution section complexes, and higher-direct-image sections; with `rg` over Mathlib,
`WeilConjectures`, and the repository's `lean/Sheaf`; and with the upstream-name index.
Only generic pullback, adjunction, and derived-functor declarations were found. No existing
declaration states this item or either delivery-specific notion. The old recorded declaration
for `lem-weil-pbc-higher-direct-image-presheaf` was unusable because it did not identify the
open-cohomology presheaf or its canonical theta; its dependency module was therefore replaced
with `HigherDirectImageSections`, with the required explanatory `lean.note`. The missing
restricted-choice bridge was added as the new definition node
`def-weil-pbc-flat-base-change-open-choices`; its fields and named open equality match the
node's definition statement. All three delivery modules compile together with
`scompile.py` under the default limit and produce no warnings.
