## Worker report

The delivery states `lem-weil-pbc-localization-inverse-image-coherence` in
`Sheaf.CategoryTheory.LocalizationInverseImageCoherence`. Its clauses are the declarations
listed in `lean.declarations`, rather than an unspecified isomorphism witness. Every theorem
has proof `sorry`; definitions contain actual data. There is no statement correction and
no disputed assertion.

Hypotheses and objects:

- The two sites are `C`, `D`, `J`, `K`, with independent object and morphism universes.
  `EssentiallySmall.{u}` and the existing sheafification/underlying-sheaf instances express
  smallness relative to the coefficient universe; they do not identify the site universes.
  In particular, objects in `Type (t+1)` and morphisms in `Type t` are allowed. The common
  coefficient universe can be any sufficiently large universe, as for the existing module
  and algebraic inverse-image interfaces. None of these instances is an extra geometric
  property such as flatness, enough points, continuity of a site functor, or subcanonicity.
- The geometric morphism is the actual adjunction `L ⊣ V` with
  `[PreservesFiniteLimits L]`. It is not restricted to one induced by a functor of sites.
- `R` is the source commutative ring sheaf. `S` and
  `a : SheafOfModules.AlgebraicInverseImage L R S` present `R' = f⁻¹R` and its module
  inverse image. This is the existing dependency definition: its ring and module graph
  equations specify all operations and its natural underlying-sheaf identification
  specifies maps. An arbitrary additive functor is not substituted for inverse image.
  The module publicly imports the dependency's recorded `AlgebraicInverseImageOfUniverses`
  module, which retains this common-coefficient-universe presentation. Its node is added
  to `stmt_deps`, as permitted for already landed definition nodes by brief-stage2 §5.
- `t`, `s` are actual global compatible sections. `IsInverseImageSection a t s` says
  precisely `s = f⁻¹t`: it tests every arrow from every sheaf which is constantly `t`
  sectionwise and requires its transported arrow to be constantly `s`. Testing the
  terminal sheaf recovers transport of the global section; testing arbitrary sheaves
  makes it applicable to local/generalized representatives. This is a presentation of
  the section named in the node, not an additional scalar hypothesis.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Actual sheafified localization ring | `ringedLocalizationRingOfUniverses R t` and `ringedLocalizationRingUnitOfUniverses R t`, in the dependency module. |
| Actual tensor module localization | `scalarLocalization R t` is `SheafOfModules.siteSheafTensorRight (A := R) (ringedSectionLocalizationOfUniverses R t)`. Thus its object is the existing sheaf tensor `M ⊗ R[1/t]`, the canonical symmetric form of the displayed `R[1/t] ⊗ M`. No independent localization model is invented. |
| Module localization unit | `existsUnique_scalarLocalizationUnit` specifies every section as `m ⊗ 1`, using the actual localization unit and the actual tensor sheafification pure-tensor map. `scalarLocalizationUnit` takes this uniquely specified map. The existence theorem determines the data uniquely, so this is not a hollow choice from mere existence. |
| Canonical module comparison and naturality | `existsUnique_localizationInverseImage` gives a natural isomorphism `scalarLocalization R t ⋙ a.modules ≅ a.modules ⋙ scalarLocalization S s`. Its equation is equality of natural transformations preserving the specified units. |
| Canonical ring comparison and its unit | `existsUnique_localizationInverseImageRing` takes any algebraic presentation `b` of `f⁻¹(R[1/t])` with coefficient ring `A`, and produces the unique ring-sheaf isomorphism `α : A ≅ S[1/s]` whose underlying map commutes with `L` of the actual ring localization unit. `b.ringUnderlying` makes the domain exactly inverse image, including transported ring operations. This does not replace it by an arbitrary ring. |
| Linearity over the identified localized ring | `localization_restrictScalars_fullyFaithful` says every map between localized module sheaves which is linear over the original ring has a unique localized-linear lift with the same actual map. Thus the displayed comparison in original-module categories recovers, uniquely, the comparison in localized-module categories with their canonical scalar actions. |
| Local fraction formula | `localizationInverseImage_fraction` quantifies over every test sheaf `T`, numerator arrow `m`, fraction arrow `q`, and `n : ℕ`. Its hypothesis is `tⁿ q = η(m)`; its conclusion is `sⁿ β(f⁻¹q) = η(f⁻¹m)`. In a localized module multiplication by `sⁿ` is invertible, so this specifies exactly the representative `(f⁻¹m)/sⁿ`, including `n=0`. It makes no sectionwise description of the geometric inverse image. For rings, the ring isomorphism and its ring-unit equation likewise force the fraction formula by multiplicativity and inversion. |
| Both functors exact | `localization_inverseImage_exact` concludes additivity, finite-limit preservation and finite-colimit preservation for `a.modules`, the source scalar-localization functor, and the target scalar-localization functor. Exactness is a conclusion, not a supplied hypothesis. |
| Composition, with canonical identifications | `localizationInverseImage_comp` uses a third site and two geometric adjunctions. It allows a composite algebraic presentation `c` and its inverse-image composition iso `κ`. Its displayed equation is `δ ≫ (κ ▷ localization) = (localization ◁ κ) ≫ (β ▷ b.modules) ≫ (a.modules ◁ γ)`. The normalization of all three comparisons is explicit. The equation is valid for any natural presentation iso `κ`, hence for the canonical one. |
| Identity, including an arbitrary identified lift | `localizationInverseImage_id` allows any algebraic identity inverse-image presentation `a` with its natural identification `κ` with the identity module functor. The equation identifies `β` with the identity, with `κ` inserted on both sides. The identity is not assumed to be strict. |
| Specified coefficient identification | `localizationInverseImage_coefficient` binds the specified ring-sheaf iso `e : S ≅ A`. The identity-geometric presentation `b` is required to have exactly `(sheafCompose K (forget CommRingCat)).mapIso e` as its ring identification. Its section-transport conditions require the section of `A` to be `e(s)`. The displayed square compares the direct identified presentation with the original one followed by this reinterpretation. It is an equality of natural transformations. |
| Ordinary unbounded derived comparison | `localizationComparisonDerived` descends the same module natural iso using `Functor.mapDerivedCategoryNatIso`, between the canonical `mapDerivedCategoryCompIso` identifications. It uses `DerivedCategory` and termwise exact functors on all cochain complexes indexed by `ℤ`; there is no boundedness, injective resolution or completeness hypothesis. The exactness instances it accepts are precisely the conclusions supplied above when instantiated to inverse image and localization. |
| Derived units | `localizationUnitDerived` is the localization lift of the actual termwise unit chain map, with the canonical derived identity iso. `localizationComparisonDerived_unit` states its unit equation. |
| Derived composition and identity | `localizationComparisonDerived_comp` and `_id` state equalities of natural transformations, with the explicit canonical derived composition and identity comparisons. Apply them to the module equations above after transporting along `κ` using `Functor.mapDerivedCategoryNatIso`. The coefficient square is the same composition assertion with the exact identity-topos coefficient reinterpretation as second functor. |

Dependency declarations used: `CategoryTheory.Precoverage.IsSiteForCoverings` and the existing
`Sheaf` definitions through `Sheaf.CategoryTheory.SiteCoveringAxioms`;
`CategoryTheory.ringedSiteModules` through `Sheaf.CategoryTheory.RingedSiteModules`;
the localization dependency described below; `SheafOfModules.siteSheafTensorRight` and
`siteSheafTensorTmul` through the recorded `SiteTensorFunctoriality` module;
`DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q` and the exact-functor API from
Mathlib; and `SheafOfModules.AlgebraicInverseImage` through the recorded
`AlgebraicInverseImageOfUniverses` module. The already stated proof dependencies are
imported without `public`, including geometric module transport, the lifted ring-object
adjunction, exact module sheafification, module colimits/forgetful, tensor-sheafification,
ordinary module localization/exactness, and exact-functor derived identification.

Edge cases checked mathematically before writing: the zero ring and nilpotent `t` localize
to the zero ring and zero modules; the unique comparison and all unit equations remain
valid. For `t=1` the normalization gives the identity. The zero module and zero complex
are included. For the empty site there are no sectionwise constraints beyond the unique
sheaves, so the constructions still apply. Exponent `n=0` is explicitly allowed. Arbitrary
unbounded complexes, arbitrary identity inverse-image presentations, arbitrary coefficient
ring identifications, and sites with different object/morphism universes are retained.
The fraction condition uses arbitrary generalized elements and does not assume enough
points or that inverse image is sectionwise restriction.

Searches made:

- `msearch.py`, LeanFinder, query “Inverse image of sheaves of modules commutes coherently
  with localization at a global section”: free-module and site-pullback comparisons
  (`SheafOfModules.ιFree_mapFree_inv`, `pullback_map_ιFree_comp_pullbackObjFreeIso_hom_assoc`)
  and module unit/sheafification maps; no statement with these localization coherence clauses.
- `msearch.py`, Loogle, query `SheafOfModules, localization`: zero hits, unknown lower-case
  identifier `localization`. Repeated with the valid quoted query `"Sheaf", "localization"`: 12 hits,
  including sheafification as categorical localization, structure-sheaf stalk/basic-open
  localization and `TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf`; none is the
  arbitrary-geometric inverse-image scalar-localization comparison with its coherence.
- `msearch.py`, Mathlib grep, query
  `localiz.*(inverseImage|pullback)|(inverseImage|pullback).*localiz`, under
  `Algebra/Category/ModuleCat`: the categorical localization of module sheafification only.
- `rg` across Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf`, with inverse-image,
  localization, geometric-morphism and proposed-name patterns; upstream grep for the exact
  item id returned no declaration. The source DAG name index was also searched.
  Side `ScalarLocalizationDerivedHom` supplies exactness for a specialized scalar-extension
  presentation, not this arbitrary-geometric inverse-image coherence theorem.
  `RingedLocalizationRHomCalculus.localizationModules` is a specialized transparent alias;
  this delivery uses a distinct transparent alias of the dependency's actual category
  so that no full declaration name collides. Neither alias constructs a category.
- The source places were opened locally: `sites-modules.tex` at
  `lemma-tensor-product-pullback` (03EL) and `lemma-adjointness-tensor-restrict` (03CZ).
  The unique-fraction extension, exactness and normalization are the extracted argument
  recorded in the node, not attributed to a verbatim theorem in Stacks.

## Dependency modules

`def-weil-pbc-ringed-section-localization`: the recorded
`Sheaf.CategoryTheory.RingedSectionLocalizationRing` requires `C : Type u` and
`[SmallCategory C]`, with coefficients also in `u`. Its module and ring constructions
cannot be applied to the original small-site statement while keeping independently
sized site objects and morphisms. Under §1(B),
`Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses` retains the old public import
and supplies the identical construction with independent site universes and the existing
sheafification instances in the chosen coefficient universe. It constructs
`Localization.Away` sectionwise with the actual localization-lift restrictions; module
and commutative-ring sheafifications, their actual units, the normalized comparison of
their underlying modules, and restriction of a local section to the slice are all given.
It imposes no equality of universes and chooses no arbitrary ring or scalar map. Only
this dependency node's `lean` record changes. No new DAG node is needed.


## Repair

The returned delivery identified `CategoryTheory.ringedSliceSection_naturalOfUniverses` as a duplicate of the existing `CategoryTheory.ringedSliceSection_natural` in `Sheaf.CategoryTheory.RingedSectionLocalization`. I removed the duplicate theorem declaration. `ringedSliceSectionOfUniverses` now uses the existing theorem directly and is explicitly specialized to its `SmallCategory` universe convention; the independent-universe localization and ring constructions remain unchanged. The dependency node's `lean.declarations` list and note were updated accordingly.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
