## Worker report

Stage 2 statement of `lem-pur-principal-torsor-yoneda-sign`, in
`Sheaf.AlgebraicGeometry.PrincipalTorsorYonedaSign`.
The only postponed proof is `AlgebraicGeometry.Etale.principal_torsor_yoneda_sign`.
Its proof is `sorry`. All six helper declarations have actual data or fully written
propositions. The helpers organize this node's own localization, comparisons and clauses;
they introduce no independent mathematical notion or extra axiom.

The node is already stage-1 reviewed PASS. This delivery changes only its `lean` field;
it does not re-split it, correct its statement, or change its proof or dependencies.
No statement dispute or source correction was needed.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Scheme T and closed immersion i:Z -> T | All clauses quantify `T Z : Scheme.{u}`, `i : Z ⟶ T`, `[IsClosedImmersion i]`. |
| Complementary open j:W -> T | `W : T.Opens` with `h : Set.range i.base = (Set.range W.ι.base)ᶜ`; the open immersion is `W.ι`. Every open immersion is isomorphic to this open-subscheme presentation; no quasi-compactness, nonemptiness or finite-type assumption is imposed. |
| The constant integral localization sequence | `principalTorsorLocalization i W h` is a definition with explicit short-complex type, using the published `openClosedShortComplex` evaluated on Mathlib's constant sheaf at `AddCommGrpCat.of (ULift.{u+1} ℤ)`. Its first and last terms are `j_! j^* Z_T` and `i_* i^* Z_T`. The canonical constant inverse-image isomorphisms identify these with exactly `j_! Z_W` and `i_* Z_Z`. Both arrows are the existing adjunction counit and unit. |
| Abelian etale sheaf G | `G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}`. |
| G-torsor P | `P : CategoryTheory.Sheaf.Torsor G`, the recorded general-abelian-sheaf version of `def-sc-gm-torsor`. |
| Global frame e and prescribed section s | In `Formula`, `e` is evaluated at `Scheme.Etale.mk (𝟙 T)`, and `s` at `Scheme.Etale.mk W.ι`. |
| s = g + e restricted to W | Binder `g : G.obj.obj (op (Scheme.Etale.mk W.ι))` and equation `_hs` using `P.vadd` and the terminal restriction of `e`. |
| Specified extension beta(P,s) | `E`, `a`, `b`, `hab` and `hE : (ShortComplex.mk a b hab).ShortExact` are any representative of that extension. `F` is a natural transformation from `P.sheaf.obj` to the underlying presheaf of `E`; `_hF` is equivariance, `_hbF` puts its image over supported one, and `_hFs` says `F(s)=0`. These are exactly the characterization in `relative_extension_existsUnique`. With the global frame, equivariance and short exactness identify its image with the whole fibre. The Ext class is `hE.extClass`. No absolute-H1-only condition is used. |
| Pushout along the map adjoint to 1 -> -g | `C.openSection` is the natural additive Hom-to-section equivalence. `Normalized` requires naturality in every coefficient sheaf and that the canonical inclusion maps to constant one. This specifies the standard extension-by-zero adjunction: any natural automorphism fixing the inclusion is identity because that inclusion is monic. The pushout map is `(C.openSection ... G).symm (-g)`. `Formula` asserts `hE.extClass = hL.extClass.comp (Ext.mk₀ ...) (add_zero 1)`, the usual covariant Ext image, i.e. the pushout extension class, and includes `hL` short exactness. |
| Every coefficient short exact sequence 0 -> H -> K -> G -> 0 | `H K`, `aK`, `bK`, `habK`, and `hK` in the second clause of `Formula`, universally quantified. |
| Extension class k and Yoneda splice k[1] after beta | `hK.extClass` and `hE.extClass.comp hK.extClass (rfl : 1+1=2)`. This is Mathlib's covariant coefficient composition, not a contravariant Ext boundary. |
| Ordinary coefficient connecting map delta_W | `I J L` and `α β` range over all compatible degreewise split injective-resolution models of the coefficient sequence. `_hα`, `_hβ` are augmentation compatibility, `_hsplit` records the splitting. Such models exist for every coefficient short exact sequence by the imported horseshoe theorem; these are computational models, not extra hypotheses on the sequence. `hOpen.δ 0 1 rfl x` is the ordinary section connecting class, where `x` is any degree-zero homology representative of `g`, specified by `TorsorSectionRepresents`. |
| Supported-Hom identification z -> (z p,0) | `C.relative` is an additive equivalence from the actual supported-source Ext group to the existing `relativeCohomology`. For every resolution, every positive degree, and every cocycle `z`, `Normalized` fixes its value on `I.extMk z ... hz` by `TorsorSignedRepresents ... (z(p(1))) 0`. Every Ext class has such a representative, so this fixes the comparison completely. The comparison maps are supplied existentially together with this normalization, not assumed as arbitrary maps. |
| Derived kernel-of-restriction support cohomology | `C.support T : RelativeCone.System ...` is the published normalized kernel-to-cone realization, including `kernel_components`, `κ_components`, the quasi-isomorphism, and right-derived computation normalization. The explicit `C.toSupport T W H I 2` is precisely the normalized `.e 2` map and has target `((Sheaf.supportedSectionsFunctor ... restrictionArrow).rightDerived 2).obj H`. This is exactly the right derived kernel of restriction, with the original sheaf H, not a renamed cone group. Its normalization precludes an arbitrary sign or comparison. |
| Splice equals minus partial delta_W(g) | The final displayed equality in `Formula` applies the normalized `C.toSupport ... 2` to `C.relative ... (hE.extClass.comp hK.extClass ...)`; its right side is minus `C.toSupport ... 2` applied to `torsorLocalizationBoundary ... 1 (hOpen.δ 0 1 rfl x)`. Both sides therefore lie in derived kernel-of-restriction cohomology. |
| D(a,b)=(da,res(a)-db), partial[b]=(0,-b) | The existing `TorsorSignedRepresents`, `torsorSignedA/B`, and `torsorLocalizationBoundary` are used without redefinition. The second coordinate is minus Mathlib's ordinary cone coordinate, exactly as specified in their docstrings. |
| Naturality in coefficient short exact sequences | `Natural`'s first clause states compatibility of the supported-Hom comparison with every coefficient morphism and every augmentation-compatible resolution lift, including identity coefficients and arbitrary comparison lifts. The ordinary connecting arrows are the actual `ShortExact.δ`; their sequence-morphism naturality is `HomologicalComplex.HomologySequence.δ_naturality`. The localization boundary is the existing cone arrow, natural in those same lifts. Thus the formula is preserved under morphisms of coefficient short exact sequences. |
| Naturality in etale restriction of the pair | The second clause of `Natural` universally quantifies an etale `v : T' ⟶ T`, a cartesian closed-support square `IsPullback w i' i v`, the inverse-image open, arbitrary resolutions and direct-image resolution lifts. It uses the existing `globalResolutionSectionTransfer` and `relativeTransfer`. For any source/target supported cocycles satisfying the defining restriction equation on `z p(1)`, it asserts equality of the target Ext realization and the relative transfer of the source realization. Because the comparison is determined on cocycles, this is the representative formulation of the full restriction square, not a selection of one lift. The canonical kernel-to-cone system carries its own normalization, coefficient and object-square naturality. |
| G_m means inverse unit | This is a notation translation, not an added hypothesis or a new assertion: the recorded `Scheme.gmSheaf` is an abelian sheaf written additively, and its negation is multiplicative inversion. Thus the actual formula uses `-g`, i.e. `g⁻¹`. |

### Dependencies read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to the small
  etale site and `AddCommGrpCat.{u+1}` as its node prescribes.
- `WeilConjectures.CategoryTheory.Sites.Torsor`: `CategoryTheory.Sheaf.Torsor`, including
  its full action, naturality, simply-transitive and local-nonempty fields.
- `Sheaf.CategoryTheory.Sites.RelativeTorsorExtension`:
  `CategoryTheory.Sheaf.Torsor.relative_extension_existsUnique`. Its full extension
  characterization is used in `Formula`; its proof is the uniqueness step of this node.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the abelian-sheaf derived-category
  encoding described in `def-weil-pbc-derived-categories`; ordinary abelian sheaves here
  use `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1})`.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`: `CategoryTheory.Abelian.Ext`,
  `Ext.comp`, `Ext.mk₀`. `Ext.ExtClass`: `ShortComplex.ShortExact.extClass`.
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `Etale.closedSupportHom`, read with its
  full ordinary-linear-RHom signature and docstring. The normalized abelian integral
  specialization needed here is specified directly on Ext cocycles, without a second
  definition of RHom or an assumed unnormalized isomorphism.
- `Sheaf.AlgebraicGeometry.RelativeEtaleCohomology`: `relativeSections`,
  `relativeSectionComplex`, `relativeCohomology`; their actual cone and shift are retained.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`: `supportedEtaleSections` is the
  module-coefficient kernel functor of the dependency. For the node's abelian sheaves,
  the existing `Sheaf.supportedSectionsFunctor` used by `RelativeCone.System` is its
  coefficient-general kernel construction; it derives the kernel, not the restriction
  cone by definition. No new support functor is introduced.
- Proof interfaces: `openClosedShortComplex`, `shortExact_openClosedShortComplex`,
  `openImmersionLowerShriekUpperStarAdjunction`, `pushout_short_exact_sequence`,
  `InjectiveResolution.extMk`, `extAddEquivCohomologyClass`,
  `InjectiveResolution.exists_horseshoe_resolutions`,
  `InjectiveResolution.extMk_resolution_connecting_eq_triangle`,
  `HomologicalComplex.HomologySequence.δ_naturality`,
  `RelativeCone.System/Realization`, `torsorLocalizationBoundary`,
  `TorsorSignedRepresents`, `TorsorSectionRepresents`, `torsorOpenShortComplex`,
  `relativeSectionMap`, `relativeTransfer`, and `globalResolutionSectionTransfer`.
  Their recorded modules are imported; proof-only dependencies use plain imports.

### Sources and edge cases

Read local Stacks `sites-cohomology.tex`, `lemma-torsors-h1` (03AJ), and
`derived.tex`, `lemma-yoneda-extension` (06XU), and the current blueprint
`main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md`.
The inverse-unit pushout and sign are the already-reviewed refinement recorded in this
node, not a new correction of the parent unit. The proof docstring carries all seven
DAG steps, including the homotopy `-h` and differential of `(0,-r)`.

- W empty: open source and g vanish; the framed extension splits and both sides are zero.
- W=T: the supported source is zero; all supported Ext and cohomology groups vanish.
- Empty ambient scheme: section groups are zero; no Nonempty premise is introduced.
- G or H zero: the formulas specialize to zero maps and remain meaningful.
- g extending globally: the pushout map extends across Z_T, so its relative extension
  class and the localization of its coefficient boundary vanish.
- Arbitrary characteristic, nonreduced closed immersion, and non-quasi-compact open:
  no smoothness, reducedness, invertibility, characteristic or quasi-compactness binder occurs.
- Site objects have universe u+1, morphisms universe u, coefficients universe u+1;
  every universe and binder is explicit (`autoImplicit false`). Positive degrees q+1
  include the required Ext degrees one and two. The resolution comparison clauses
  include identity coefficients, identical resolutions, and arbitrary resolution lifts.

### Searches for an existing declaration

All searches used the prescribed read-only roots and `msearch.py` group/item wrapper.

- LeanFinder: `A framed abelian etale torsor relative extension is a pushout along minus
  the section and its Yoneda splice is minus the localization connecting class`.
  Result: eight hits, led by `GrothendieckTopology.MayerVietorisSquare.isPushoutAddCommGrpFreeSheaf`;
  none states the framed relative extension or the supported coefficient-Yoneda sign.
- Loogle: `CategoryTheory.Abelian.Ext.comp, CategoryTheory.ShortComplex.ShortExact.extClass`.
  Result: twelve hits including `ShortExact.extClass_naturality`, covariant Ext exactness,
  `Ext.δ_apply` and the derived-triangle boundary formulas. These are constituent tools,
  not the node's statement.
- Mathlib grep: `torsor.*yoneda|principal.*torsor|relative.*pushout`.
  Result: two irrelevant simplicial-set relative-cell-complex hits, no match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` with the item id,
  `principal.*torsor|torsor.*yoneda`: only unrelated log-ideal charts, divisor realization
  proof text, and affine torsor filenames. No declaration of this node.
- Additional focused source searches located the actual open-closed sequence, the
  torsor-extension specification, the signed cone, integral constants, and support
  functors. Existing integral constants are used through Mathlib's literal constant
  sheaf expression, and existing one-sections through `torsorExtensionOne`.

### Validation

Every compile uses `scompile.py` against the live published library. The first compile
had no errors and only an unused computational-model binder warning; that binder was
renamed `_hsplit`. A subsequent version compiled without warnings, and the first
dry run passed preflight. After making the cartesian closed-support square explicit
in etale naturality, compilation hit the fixed 60-second limit. The localization
helper was therefore changed from a reducible abbreviation to an ordinary definition
with explicit short-complex return type, retaining exactly the same data. This avoids
repeated eager unfolding during elaboration. The kernel-to-cone map is also
named `PrincipalTorsorComparisons.toSupport` with explicit source and target, so its
large type is checked once before applying it twice in the splice formula. The limit is unchanged. Final compile
and delivery checks are performed by the prescribed wrappers. The final module passed
the server confirmation without errors or warnings in 56.7 seconds, at the unchanged
60-second limit. All diagnostic profiler options were removed before this check.

## Second reading by N5

I re-read the complete node against the module: the extension is specified by the full
relative F(s)=0 condition; the pushout uses -g; the splice is the covariant coefficient
product; the target is the normalized derived kernel, and both naturality clauses are
present. This was a self-check, not an independent second-agent review. The dispatcher's
brief forbids starting other agents and assigns the independent delivery review to the
maintainer. No independent review is claimed here.
