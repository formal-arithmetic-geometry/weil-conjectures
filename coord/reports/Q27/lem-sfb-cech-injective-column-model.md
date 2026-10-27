## Worker report

The module `Sheaf.CategoryTheory.CechInjectiveColumnModel` states
`CategoryTheory.cech_injective_column_model`, with its whole proof postponed by `sorry`.
It also defines `CategoryTheory.cechColumnRestrictComplex`: the existing canonical
`elementModulePullback` applied termwise to integer-indexed complexes. Its data is the
Mathlib `mapHomologicalComplex` construction, not a choice of a complex or a map. The
adjunction `D.adj A` supplies preservation of coproducts; the existing biproduct lemmas
supply additivity and hence preservation of zero. These are instance terms in the body
of this definition, not extra hypotheses, local commands or postponed proofs.

The node's statement, dependencies and proof are unchanged. The previous worker's stale
stage-1 assignment diagnosis does not prevent stage 2: the current node is split and
reviewed PASS for Q36, with no Lean record. There was no saved Lean module in this sandbox.

Hypotheses, in the order of the natural-language statement:

- Topoi presented by small sites in a fixed common larger coefficient universe are
  `{C X : Type u}`, `[SmallCategory C]`, `[SmallCategory X]`, `J` and `L`.
  Their topoi are `Sheaf J (Type u)` and `Sheaf L (Type u)`. This is exactly the common
  universe convention already fixed by the element-site definition. The independent
  localization hom-universes are `wX`, `wY` and `wSlice`; none are equated. The instance
  family for all sheaf element sites supplies the specified ordinary derived categories,
  rather than a bounded or different derived category.
- The ring sheaves are `R : Sheaf J RingCat.{u}` and `S : Sheaf L RingCat.{u}`.
  `_hR` and `_hS` assert commutativity for every pair of sections at every site object.
  Thus these binders have precisely the commutative ring objects of the statement,
  retaining the recorded RingCat-based module interfaces.
- The ringed geometric morphism is `f : RingedToposMorphism R S`. This includes the
  geometric inverse/direct image adjunction and the induced module direct image.
  `[IsIso f.ringMap]` is the Cartesian coefficient identification. `fInverse`, its
  additive and finite-limit/finite-colimit-preservation instances, and `_adj` supply
  the exact module inverse image. The adjunction determines it up to the canonical
  adjunction-compatible isomorphism; it is not an unconstrained extra functor.
- The cover is `V : Sheaf J (Type u)` with `[Epi (terminal.from V)]`.
  `sheafCoverNerve V` is the actual Cech nerve of that arrow; its object at `op n` is
  the sheaf power with `n.len + 1` factors. In particular no representability,
  subterminality, finite covering family or nonempty section set is assumed.
- `M : ringedSiteModules.{u} R` is an arbitrary module sheaf. Indices are the small
  categories `SimplexCategory`, `ℕ` and `ℤ`, so every diagram used here is small.

Conclusions, clause by clause:

- The initial `Nonempty (InjectiveResolution M)` is the existence of an ordinary
  nonnegative resolution, with actual augmentation `I.ι`. The recorded structure has
  injective terms and a quasi-isomorphism from `(CochainComplex.single₀ _).obj M`.
  Its extension by `ComplexShape.embeddingUpNat` is zero in every negative degree.
- `Nonempty (CoherentCechImageModel R)` asserts existence of the canonical simultaneous
  localization model. Its restrictions are already fixed by counit transposition,
  its augmentations by the identity transposes, and its identity/composition laws by
  the actual functor `D.image`; this is not existence of an unspecified diagram.
- The subsequent `∀ (I : InjectiveResolution M) (D : CoherentCechImageModel R)` retains
  the statement's EVERY-resolution and EVERY-canonical-model clauses. The first
  conjunct is `CochainComplex.IsKInjective` of the integer extension of I. For every
  simplex n, the next conjunction asserts K-injectivity of its canonical restriction
  and `QuasiIso` of the restriction of `extendMap I.ι`. No preservation of
  K-injectivity by an arbitrary inverse image is assumed.
- `B` is an actual `CosimplicialObject (CochainComplex ... ℕ)`. `σ n` identifies its
  column with `(D.bicomplex f.modules V I.cocomplex).X n.len`. That recorded definition
  has terms `f.modules.obj ((D.image.obj (op V_n)).obj (I.cocomplex.X q))`.
  The equation quantified over EVERY `θ : n ⟶ m` and EVERY q identifies its maps,
  through σ, with `f.modules.map ((D.image.map (nerve.map θ.op).op).app (I.X q))`.
  Hence it includes actual cofaces and codegeneracies and their strict identities.
  Each σ is a chain isomorphism, so its vertical differential is the original mapped
  resolution differential. Naturality gives commuting differentials; the alternating
  coface differential and its square-zero identity are the recorded `D.bicomplex`.
- The isomorphisms `κ n` identify the extended B columns with the complex obtained by
  applying `D.push V_n ⋙ f.modules` to the canonical restriction of I. The component
  equation for κ, using the existing `extendXIso` transports, identifies it with
  `f.modules.map ((D.imageIso V_n).hom.app (I.X q))` after σ. Thus the entries really
  are `(f v_n)_* v_n^* I^q`, represented by the actual composite direct image, and
  κ is not an arbitrary object isomorphism.
- `α` is a natural transformation from the constant complex f_*I to B. Its degree-q
  component, transported by σ, is `f.modules.map ((D.augmentation V_n).app (I.X q))`.
  `α.app (SimplexCategory.mk 0) ≫ σ_0.hom = a` gives the specified chain map a_V.
  `a ≫ (D.bicomplex ...).d 0 1 = 0` is the first-Cech-differential assertion.
- `b` is a chain map into the recorded first-quadrant total. Its equation
  `b.f q = a.f q ≫ ...ιTotal ... 0 q q (zero_add q)` is exactly the prescribed
  inclusion of the localization unit in the (0,q) summand. The total uses finite
  natural-number diagonals, with horizontal sign +1 and vertical sign `(-1)^n`.
  Extending b and its source by zero gives the stated unbounded chain augmentation.
- `RF`, `η`, `RFslice n`, and `ηslice n` are supplied as conclusions, together with
  their `Functor.IsRightDerivedFunctor` properties for the respective actual functors
  followed by Q. This uses the existing universal-property definition of total right
  derivation. No existence of such functors or invertibility of units is assumed.
  It is equivalent to the recorded homotopy-category universal pair: the additive
  prolongations preserve homotopy and Q factors through the homotopy quotient.
- `c` is the isomorphism `Q(f_*I) ≅ RF(Q(M[0]))`, including the canonical interchange
  between applying f_* and extension by zero. The equation `c.hom ≫ RF.map (Q.map a)`
  equals that interchange followed by `η.app I` fixes it to the resolution comparison.
  Because Q(a) is invertible, the equation says precisely unit followed by the inverse
  derived resolution map, in the orientation required by the node.
- `hT n` fixes each object of the derived cosimplicial diagram T to
  `RFslice n (Q(v_n^* M[0]))`. The natural isomorphism `e : B ⋙ extend ⋙ Q ≅ T`
  supplies the column comparisons coherently for ALL simplicial operators. Its
  normalization equation after `eqToHom (hT n)` and the derived image of `v_n^*a`
  equals `Q(κ_n)` followed by the actual unit at `v_n^*I`. Again Q(v_n^*a) is
  invertible, so this is exactly the specified canonical comparison, not arbitrary
  isomorphisms of derived objects or only per-degree cohomology isomorphisms.
- `β` is a natural augmentation of T from the constant RF(M[0]) diagram. Its equation
  is `c.inv ≫ Q(extendMap (α.app n)) ≫ e_n.hom`. Hence the augmentation and EVERY
  restriction are transported from this one strict resolution diagram. Naturality
  of e and β encodes all derived simplicial and augmentation identities. The
  otherwise arbitrary choice of a universal pair is determined up to its unique
  unit-preserving isomorphism; the displayed equations preserve that normalization.

Dependencies read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: site convention; this theorem uses
  the associated Grothendieck-topology presentation, as the node permits.
- `def-weil-size-convention`: metatheoretic convention, rendered by the explicit
  common site/coefficient bound u and independent derived-category universes.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the Mathlib `SheafOfModules` category and its abelian structure.
- `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`:
  geometric morphism, structural ring map, and induced additive module direct image.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `over`, `overMap`, `overFunctorMap`: the object-slice
  convention of `def-pur-localized-ringed-site`. For the nonrepresentable sheaves V_n,
  the actual specialization is the additional recorded element-site dependency;
  no object of C representing V_n is assumed.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`: ordinary unbounded localization.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`, `HomologicalComplex₂`,
  `.total`, `.ιTotal`: bicomplexes and finite-diagonal totals, used through the
  recorded `CoherentCechImageModel.bicomplex` interface. The total sign definitions
  were checked in Mathlib `ComplexShapeSigns`: ε₁=1 and ε₂(n,q)=(-1)^n.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`, `Injective` and
  `InjectiveResolution`: actual resolutions, not arbitrary quasi-isomorphic complexes.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
  `CochainComplex.IsKInjective`: null-homotopy of every map from every acyclic complex;
  the definition node's exact `mathlib_match` is used despite its absent lean record.
- `Sheaf.CategoryTheory.RingedSheafSliceConstruction`, `elementProjection`,
  `elementTopology`, `elementRing`, `elementModulePullback`, `elementMap`,
  `elementModulePullbackOver`: the canonical concrete sheaf-slice restrictions.
- `Sheaf.CategoryTheory.CoherentCechImageModel`, `sheafCoverNerve`,
  `CoherentCechImageModel`, `.bicomplex`, `.push`, `.imageIso`, `.augmentation`:
  the actual simultaneous restriction model and its adjunction normalization.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  its recorded universal-pair definition, unit and unique normalization are used
  through the existing `Functor.IsRightDerivedFunctor` universal-property interface
  (`Mathlib.CategoryTheory.Functor.Derived.RightDerived`). Both are total right derived
  functors; no monomorphic-resolution requirement is introduced.

The module also imports every stated proof dependency: the recorded generalized
`SheafOfModules.isGrothendieckAbelianOfUniverses`, Mathlib's Grothendieck-enough-injectives
and ordinary injective-resolution construction, the recorded slice adjunction and
continuous-cocontinuous theorem, the upstream adjoint-preserves-injectives lemma,
Mathlib's bounded-below injective K-injectivity theorem, the recorded Grothendieck
K-injective-resolution instance, and `exists_rightDerived_of_enough_isKInjective`
(the last via the public recorded right-derived module). The theorem docstring gives
all nine proof steps and their DAG dependencies. It does not import the downstream
`DerivedCechImageTotalization` or `CechLocalizationUnitTotalization` modules.

Edge cases checked before writing:

- M=0 and zero coefficient ring: InjectiveResolution and all zero complexes are valid;
  no nontriviality or nonzero-section assumption is present.
- V terminal (identity cover): the actual nerve and all its degeneracies remain in the
  statement; it does not replace the nerve by a normalized complex.
- A sheaf V with no global section, and non-subterminal sheaves: all localizations use
  the element sites. The model supplies right adjoints, not an incorrect product/sum
  identification or an adjunction in the opposite direction.
- Degree q=0: the total inclusion is (0,0), with vertical sign +1, and the first Cech
  differential annihilates the chain augmentation. Negative degrees are zero by the
  actual embedding extension, rather than omitted from the derived category.
- Arbitrarily large finite simplicial degrees: all n are quantified and both faces
  and degeneracies are included. Only finite diagonals are summed; there are no
  infinite direct-sum/product totalizations.
- Empty topos: Epi of the terminal arrow retains its ordinary categorical meaning;
  there is no added global nonemptiness hypothesis.

Searches for existing declarations:

1. `msearch.py ... leanfinder "A single injective resolution gives coherent Cech columns
   computing derived direct images on ringed topoi"`: 8 hits, all concerning local
   injectivity of morphisms of module presheaves and sheafification. No matching column
   model theorem.
2. `msearch.py ... loogle "CategoryTheory.InjectiveResolution, CochainComplex.IsKInjective"`:
   one hit, `CategoryTheory.InjectiveResolution.instIsKInjectiveCochainComplex`
   in `Mathlib.CategoryTheory.Abelian.Injective.Ext`. It covers only K-injectivity of
   an ordinary injective resolution, not localization, columns, augmentation or units.
3. `msearch.py ... grep "CoherentCechImageModel|cech.*injective|injective.*cech"
   CategoryTheory`: 0 Mathlib hits.
4. `msearch.py ... leansearch "injective resolution restricted to a sheaf slice computes
   the total derived direct image"`: 8 hits, on `injectiveResolutions`, ordinary
   cohomology comparison/naturality and maps of resolutions. No matching sheaf-valued
   augmented cosimplicial theorem.
5. `rg -n 'lem-sfb-cech-injective-column-model' lean/WeilConjectures lean/Sheaf`:
   no existing attachment. `rg` for `CoherentCechImageModel|cech_injective_column|
   cechInjectiveColumn` found the recorded definition and two downstream totalization
   modules. Their full relevant declarations were read. The downstream descent
   theorem handles an additional exact functor H and proves an isomorphism of totals;
   its column theorem asserts invertibility of a unit. Neither gives all clauses here:
   ordinary resolution/model existence, restriction of the resolution map, the actual
   full cosimplicial diagram with degeneracies, both comparison normalizations, and
   their coherent derived augmentation. Those downstream modules are not used as
   prerequisites for this item. The existing canonical element-site and bicomplex
   constructions are reused rather than redefined.

Validation: server `scompile.py` compiles this module independently both as its sandbox
probe and at its delivered module name (23.2 s and 20.5 s). No errors or disallowed
warnings. The first compile exposed missing public imports for K-injectivity and the
right-derived universal property; the imports were repaired and the final compile passed.
There is no statement correction, disputed statement, new node or dependency-node repair.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
