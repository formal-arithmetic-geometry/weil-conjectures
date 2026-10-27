## Worker report

The module `Sheaf.CategoryTheory.CechInjectiveImageAugmentation` states
`CategoryTheory.CechInjectiveImage.cech_injective_image_augmentation`, with its proof
`sorry`. Its conclusion `ExactAugmentation f D V I` is a fully written proposition
containing all the node's assertions. Every helper is a real composite of existing
Mathlib/project constructions; no construction uses `sorry` or an existence-only choice.
The one postponed theorem has the node's complete seven-step proof in its docstring.
The natural-language statement, proof and proof dependencies are unchanged.

The item's statement dependencies gain the already landed definition node
`def-sfb-coherent-cech-image-model`. Its module was read in full: `D.imageIso`, `D.adj`,
`D.restriction`, `D.unit` and `D.augmentation_naturality` fix actual localization direct
images and all their maps, rather than arbitrary additive endofunctors. This is a choice
of presentation of the specified canonical construction, not an extra mathematical
restriction on the cover, the topos or the injective complex. The recorded construction
`D.bicomplex` puts Čech degree first and resolution degree second; `D.IsAugmentation`
fixes every component of the total augmentation to the localization unit.

Hypotheses and objects, clause by clause:

- Small presented sites and fixed coefficient universes: explicitly bound `C X : Type u`,
  `[SmallCategory C]`, `[SmallCategory X]`, topologies `J K`, rings, set sheaves and module
  values in universe `u`. The category of module sheaves has objects in `Type (u + 1)`.
  This is the fixed larger bound of the node; no essential-smallness or representability
  restriction is added. The derived localization has the independently explicit universe
  `w`, through `[HasDerivedCategory.{w} (ringedSiteModules.{u} S)]`. All sequence and finite
  diagonal index categories are small. `set_option autoImplicit false` is active.
- Ring sheaves: `R : Sheaf J RingCat.{u}`, `S : Sheaf K RingCat.{u}`, with `_commR` and
  `_commS` giving sectionwise commutativity. This uses the recorded ringed morphism API
  without constructing a duplicate commutative-ring or module category.
- Ringed-topos morphism: `f : RingedToposMorphism R S`, including its set adjunction,
  left exact inverse image, induced module direct image and underlying-sheaf comparison.
  Cartesian coefficients are `[IsIso f.ringMap]`. Exact module inverse image is
  `fInverse`, its `Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits` instances,
  and `_fAdj : fInverse ⊣ f.modules`. The adjoint is unique up to its canonical isomorphism.
- Arbitrary topos cover: `V : Sheaf J (Type u)` and `[Epi (terminal.from V)]`.
  `sheafCoverNerve V` is the actual Čech nerve of that map. Its `n`-th object is `V_n`;
  no original-site fibre products or representability hypotheses appear.
- Nonnegative injective complex: `I : CochainComplex (ringedSiteModules.{u} R) ℕ` and
  `_injective : ∀ q, Injective (I.X q)`. There is no augmentation from another module,
  no resolution hypothesis and no acyclicity hypothesis on `I` itself.
- Ordinary unbounded derived category: Mathlib's `DerivedCategory`, `DerivedCategory.Q`
  and `HomologicalComplex.extendMap ... ComplexShape.embeddingUpNat`. Extension by zero
  permits the nonnegative complex and total to be localized in the ordinary integer-indexed
  derived category; this does not replace it by a bounded or connective derived category.

Conclusions, clause by clause, are the fields of `ExactAugmentation`:

- `injective_slice`: for every target site object `W` and every `q`, the actual module
  restriction `elementModulePullback R (testObject f W)` of `I.X q` is injective.
  `testObject f W` is literally `f.inverse.obj ((presheafToSheaf K (Type u)).obj
  (yoneda.obj W))`, the specified `A = f⁻¹(h_W#)`.
- `sections_identification`: the equivalences are isomorphisms of cosimplicial abelian
  groups `row f D V W (I.X q) ≅ sliceRow V (testObject f W) (I.X q)`. Thus they preserve
  addition and commute with all faces (and also the degeneracies). `row` evaluates the
  actual composite `f_* j_n* j_n^*`; `sliceRow` is the group of sections of `I.X q` over
  `A × V_n`, canonically the sections of `I.X q|_A` over `V_A^{×_A(n+1)}` by the recorded
  slice/relocalization equivalence. No different family of cover objects is substituted.
- The first equation in `sections_identification` fixes each component on every free
  abelian generator. Its right side `localizedTranspose` first applies sheafification
  and Yoneda to a section at `W`, then `f.adj`, then the free-module sheafification
  adjunction, then `D.adj V_n` after `D.imageIso V_n`, and finally evaluates the map on
  `generator R A U a` at the element-site object `(U,v)`. Here `(a,v)` are the projections
  of the generalized element of `A × V_n`. These generators determine the map uniquely;
  the isomorphism is not an arbitrary nonempty comparison or arbitrary selected map.
- The second equation gives compatibility with every `I.d q r`, using postcomposition
  `sectionsMap`. The third evaluates the augmentation on each free abelian generator
  as `transpose ... x` restricted by `prod.fst`. It is precisely restriction from `A`
  to `A × V_0`, and therefore is the unit augmentation in the statement.
- `sectionwise_exact`: `Function.Injective (augment ...)` states exactness at the first
  nonzero term. `Function.Exact (augment ...) ((rowComplex ...).d 0 1)` states exactly
  the degree-zero kernel/image equality. For every `n`, `IsZero (...homology (n+1))`
  states positive Čech cohomology vanishing. `rowComplex` is the actual alternating
  coface complex of `row`; no signed differential is changed.
- `sheaf_rows`: an augmentation from `single₀ (f_* I^q)` to the actual module-sheaf Čech
  row has degree-zero component exactly `f.modules.map (D.augmentation ...).app (I.X q)`
  and is a quasi-isomorphism. Since its source is concentrated at zero, this is precisely
  exactness of the augmented row, including the left endpoint, as module sheaves.
- `total_augmentation`: there exists a chain map `b` with `D.IsAugmentation ... b`,
  `QuasiIso b`, and `IsIso (DerivedCategory.Q.map (extendMap b ...))`. The component
  predicate specifies *every* component as the localization unit into the `(0,q)`
  summand, so this existence assertion introduces no arbitrary map. The total is the
  already recorded finite-diagonal total, with differential `d_Cech + (-1)^n d_I`.
- `transpose_sign`: Mathlib's actual chain isomorphism `totalFlipIso` (in its inverse
  direction) sends each `(n,q)` inclusion to `(-1 : ℤ)^(n*q)` times the `(q,n)` inclusion.
  Thus both signed conventions and the precise sign are part of the result.
- `transpose_augmentation`: its restriction to each `(0,q)` inclusion is the `(q,0)`
  inclusion with coefficient one. This records the specified identity normalization
  on augmentation summands, rather than only an abstract isomorphism of totals.

The representation of sections by Hom from free abelian presheaves is the existing
`def-sc-presheaf-cech-complex` convention: the free-abelian adjunction identifies these
Hom groups with maps from the underlying sheaf object. The helper `freeModule` is a
transparent composite of `PresheafOfModules.free` and the recorded module sheafification;
it is used only to spell out the normalization by the module adjunction. It is not a
second module category, localization, Čech nerve or total-complex definition.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings` and its
  retained Mathlib `GrothendieckTopology`/`Sheaf` presentation of the site component.
  The size-convention node is metatheoretic, with no declaration to import.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation for Mathlib `SheafOfModules`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  especially `inverse`, `adj`, `modules`, `underlying` and the induced-action specification.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`/`overMap` for the recorded site-object localization.
  For the arbitrary sheaf localizations needed here the node also records
  `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`:
  `CategoryTheory.RingedSheafSliceAdjunctionData`, `ringed_sheaf_slice_adjunction`;
  `elementRing`, `elementModulePullback`, `elementObj` are its re-exported constructions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and inversion of quasi-isomorphisms.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`: recorded filtrations and total
  convention; the actual first-quadrant total/flip API comes from
  `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` and
  `Mathlib.Algebra.Homology.TotalComplexSymmetry` (`totalFlipIso`).
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.Injective`. The recorded `InjectiveResolution` signature was also read;
  it is deliberately not required of this arbitrary nonnegative injective complex.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; `Mathlib.CategoryTheory.Yoneda`: `yonedaEquiv`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationHomEquiv`,
  `sheafificationAdjunction`, and its finite-limit-preservation instance. These supply
  the two recorded module-sheafification dependencies, including their exactness.
- `WeilConjectures.CategoryTheory.InjectiveModulePresheaf`:
  `injective_module_sheaf_injective_presheaf`.
- `WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic`:
  `injective_presheaf_module_nerve_acyclic`, and
  `WeilConjectures.CategoryTheory.Sites.PresheafCechComplex`: `presheafCechComplex`.
- `Mathlib.CategoryTheory.Sites.LocallySurjective`:
  `Sheaf.isLocallySurjective_iff_epi`; `Mathlib.CategoryTheory.Sites.RegularEpi`
  and `Mathlib.CategoryTheory.Limits.Shapes.KernelPair`: `IsKernelPair.toCoequalizer'`.
- `WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation`:
  `HomologicalComplex₂.quasiIso_of_column_augmentation`.
- `Sheaf.CategoryTheory.CoherentCechImageModel`: the additional landed dependency
  listed above, especially `sheafCoverNerve`, `cochains`, `bicomplex`, `IsAugmentation`.

Edge cases checked before writing:

- `V = 1`: the full alternating Čech row is retained (not silently replaced by a
  normalized complex); its augmentation and transpose normalization remain correct.
- Initial `A`, or zero module/zero complex: the Hom section groups are zero and all
  exactness and quasi-isomorphism assertions have their usual zero-object meanings.
- The zero coefficient ring and the degenerate topos are admitted. An empty covering
  object is admitted when its terminal map is epi; there is no `Nonempty V` assumption.
- `q = 0` and total degree zero: the single-object row condition includes the missing
  incoming differential; the total component is the unit into `(0,0)` with sign one.
- Positive cohomology is quantified as every `n+1`, not just degrees above one.
- Arbitrary sheaf `A` and `V_n`: only sheaf products and the element site are used,
  never products or representing objects in the original site.
- `I` need not resolve a module and may have arbitrary nonzero homology in higher
  resolution degrees. The claim is the augmentation quasi-isomorphism, not vanishing
  of the total complex.
- Every total diagonal has `n+1` possible summands, so no infinite product or unbounded
  diagonal was introduced. At `n=0` the transposition multiplier is one for all `q`.

Searches for an existing statement/construction:

- `msearch.py`, leansearch, query "An epimorphic sheaf cover has exact augmented Cech
  rows for injective module sheaves; the localization-unit augmentation to the direct-image
  first-quadrant total is a quasi-isomorphism": eight hits, including local-surjectivity/epi
  equivalence, generating sections, module presentations and injective-resolution extension;
  no match for this exact-row and normalized total-augmentation statement.
- `msearch.py`, leanfinder, query "Exact augmented Cech rows for injective module sheaves
  over arbitrary epimorphic topos covers and direct image total quasi-isomorphism":
  eight hits, primarily Mayer--Vietoris short complexes and the K-injective criterion;
  none state the arbitrary-sheaf-slice exact rows, specified total unit and transpose signs.
- `msearch.py`, loogle, query
  `CategoryTheory.RingedToposMorphism, HomologicalComplex₂.flip, SheafOfModules`:
  zero hits, unknown identifier `CategoryTheory.RingedToposMorphism` in Mathlib's index.
- `msearch.py`, grep, query `cech|Cech|augmentation` in `CategoryTheory/Sites`:
  five hits in Mathlib's representable-cover Čech functor; not the required general statement.
- `rg` in both project source roots for the item id: no existing declaration.
  Concept searches `cech.*[Ii]njective|[Cc]ech.*[Aa]ugment|cechInjective|CechInjective`
  and `RingedToposMorphism|elementModulePullback|elementRing` found the recorded coherent
  model and derived descent consumer, as well as representable-cover injective statements.
  Read `CoherentCechImageModel`, `DerivedCechImageTotalization`,
  `CechLocalizationUnitTotalization`, `InjectiveCechTotalSections`,
  `InjectiveCechAugmentationQuasiIso` and `PresheafCechComplex` to distinguish them.
  The derived descent theorem assumes an injective resolution and concludes a different
  derived comparison; it is a downstream consumer of this row-exactness input.
  The representable-cover statements require fibre products in the original site and
  injective abelian sheaves, so neither is a match for this module-sheaf statement.
- `rg` for the new declaration names in both source roots found no name in the new
  `CategoryTheory.CechInjectiveImage` namespace. Existing general-purpose free abelian,
  free module, Yoneda, sheafification, total and transpose constructions are reused.

Source verification: read the full statement and proof of
`sites-cohomology.tex:lemma-injective-module-trivial-cech` (03FC) and
`homology.tex:lemma-double-complex-gives-resolution` (0133), including its second-variable
variant, together with the node's reviewed seven-step extension to arbitrary slices.
No statement fault or `STATEMENT-DISPUTED` issue was found; no correction, new node or
dependency-interface repair is needed.

Validation: `scompile.py Q07 lem-sfb-cech-injective-image-augmentation` compiled the
sandbox and its library module cleanly (25.3 s and 20.6 s); the initial elaboration issue
in the Yoneda transpose was repaired by explicitly specifying its underlying target sheaf.
The delivery dry run passed the server preflight and recompiled the module without warnings.
A final dry run after completing this report is required before pushing.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
