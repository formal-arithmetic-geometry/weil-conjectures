## Worker report

The module `Sheaf.Paper.BoundedFlatReplacement` states
`AlgebraicGeometry.Scheme.exists_functorial_bounded_flat_replacement` and its explicit
integer-coefficient specialization
`AlgebraicGeometry.Scheme.exists_bounded_flat_replacement_zmod`. Both proofs are `sorry`.
There are no new definitions, new DAG nodes, dependency repairs, or statement changes.
The node copy differs from the base only in `lean`.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- An arbitrary scheme T is `(T : Scheme.{u})`. No field, characteristic, nonemptiness,
  finiteness, Noetherian, properness, or invertibility hypothesis is imposed.
- An arbitrary commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`, the
  established coefficient universe for the small etale site of a `Scheme.{u}`.
  `T.Etale` has object universe u+1 and morphism universe u; they are not identified.
- The ring sheaf Λ_T is `(constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
  (CommRingCat.of Λ)`. `constantSheaf` is sheafification of the constant presheaf.
  `sheafCompose ... (forget₂ CommRingCat RingCat)` forgets commutativity to give the
  ring-sheaf argument of `SheafOfModules.{u + 1}`. Thus these are modules over the
  actual constant ring sheaf, rather than modules over a varying unrelated ring.
- Cochain complexes are `CochainComplex ... ℤ`. Its morphisms are the chain maps
  of `def-weil-abstract-derived-category`, and `QuasiIso` asserts isomorphisms on
  cohomology in every integer degree.
- The supplied integer upper bound is `(N : ℤ)`. Inputs form the existing Mathlib
  `ObjectProperty.FullSubcategory (fun K : CochainComplex ... ℤ ↦ K.IsStrictlyLE N)`.
  By `CochainComplex.isStrictlyLE_iff`, this condition is precisely
  `∀ i : ℤ, N < i → IsZero (K.X i)`, so it concerns terms, not just cohomology.
  The full subcategory includes every chain map between these complexes.
- The construction is the existential functor `Φ` from that full subcategory to
  cochain complexes over the same constant ring sheaf. A theorem asserts its
  existence; no arbitrary choice is used to create a hollow definition.
- The replacement has the same bound by `(Φ.obj F).IsStrictlyLE N` for every input F.
- Every replacement term is flat by `∀ i : ℤ, SheafOfModules.IsFlatOnSite ...
  ((Φ.obj F).X i)`, using exactly the recorded flatness declaration of
  `def-pc-flat-sheaf-modules`: the sheafified tensor functor is exact.
- The augmentation is the natural transformation `ε : Φ ⟶ ObjectProperty.ι _`.
  Its component is an actual chain map to the input complex. `QuasiIso (ε.app F)`
  gives the quasi-isomorphism and `∀ i : ℤ, Epi ((ε.app F).f i)` gives termwise
  surjectivity in the sheaf category (local surjectivity). No sectionwise
  surjectivity of an arbitrary sheaf epimorphism is imposed.
- Functoriality includes identity and composition, through the `Functor` fields
  of Φ. For any map f between two inputs, `ε.naturality f` states
  `Φ.map f ≫ ε.app G = ε.app F ≫ f.hom`. This is exactly compatibility with both
  quasi-isomorphisms; no additivity of Φ is required.
- The last clause is the second theorem, quantified over `(n : ℤ)`. The ring is
  `ULift.{u + 1} (ZMod n.natAbs)`, canonically the ring Z/(n), since (n)=(|n|).
  `ULift` changes only size. Given any complex F and any bound N with
  `[F.IsStrictlyLE N]`, the conclusion supplies P, `P.IsStrictlyLE N`, flatness
  in every degree, and a quasi-isomorphism `q : P ⟶ F`. This explicitly retains
  the full range of integer coefficients and the bound from the main theorem.

Dependency declarations and sources read:

- `def-weil-pbc-etale-sheaves`: recorded module
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, read using `scompile.py --source`
  because it is absent in the older source checkout. Its record supplies the
  `SheafOfModules` encoding over the constant ring sheaf. The full source and its
  docstrings were read; its unrelated locally constant/set-sheaf predicates are
  not copied or imposed. Mathlib's `SheafOfModules`, `Hom`, `Category` and
  `toSheaf` in `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean` and the abelian
  instance in `.../Sheaf/Abelian.lean` were read.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  `QuasiIso` in `Mathlib.Algebra.Homology.QuasiIso`. The declaration signatures
  and documentation were read. Only complexes and quasi-isomorphisms are needed
  here; no unnecessary derived-category choice is a hypothesis.
- `def-pc-flat-sheaf-modules`: `SheafOfModules.IsFlatOnSite` in
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, read locally and confirmed
  using `scompile.py --source`. Its full signature permits independent site,
  coefficient and module universes. Its definition is exactness of the canonical
  sheafified sectionwise tensor functor `siteSheafTensorRight`.
- Mathlib's `ObjectProperty.FullSubcategory`, its `Category`, and `ObjectProperty.ι`
  were read in `CategoryTheory/ObjectProperty/FullSubcategory.lean`. They provide
  the input category and forgetful functor, without a private replacement notion.
- `CochainComplex.IsStrictlyLE`, `isZero_of_isStrictlyLE` and
  `isStrictlyLE_iff` were read in `Algebra/Homology/Embedding/CochainComplex.lean`.
- The modules of recorded proof dependencies are imported, including the free
  module, flat tensor, exact sheafification, functor-category evaluation, homology
  comparison, and module-sheafification-flatness interfaces. The size-convention
  node is metatheoretic and has no module. Both docstrings give the node's proof
  route; the main theorem carries all seven steps, including the repaired cycle
  pullback and the sheafified scalar action.

Sources and edge cases:

The full DAG node, including all seven proof steps and the imported-blueprint
counterexample, and the stored unit record `sk-prop-sf-kunneth-ordinary` were read.
The local literature files are absent in this machine's read-only mirror. The
primary Stacks pages [05T7](https://stacks.math.columbia.edu/tag/05T7), part (1), and
[03ER](https://stacks.math.columbia.edu/tag/03ER), part (3), were opened and checked.
The former uses cycles in its descending pullback and asserts the same upper
bound, a termwise surjection, and a quasi-isomorphism. The node makes its free-cover
construction functorial, as explained explicitly in step 7. A fetch of the pinned
blueprint markdown from raw GitHub failed with a cache miss; the source statement
and proof are available in full in the supplied DAG record, and no correction is
needed. In particular the previously recorded source error is a proof error only;
this delivery does not change the node's statement.

Checked zero complexes, the empty scheme, arbitrary negative and zero N, terms
above N, and degree N itself. Flatness of zero objects permits zero terms. At the
upper boundary the next cycle term is zero and the free cover starts in degree N;
there is no lower bound requirement. Checked n=0 (ZMod 0 is Z), n=1 and n=-1
(the zero ring), and negative n generally (the same principal ideal as |n|).
There is no `NeZero n`, `n > 0`, or coefficient invertibility restriction.

Searches actually run for an existing declaration:

- `msearch.py ... leanfinder "Every bounded above complex of sheaves of modules
  admits a functorial termwise epimorphic quasi-isomorphism from flat sheaves with
  the same upper bound"`: eight hits, principally `CochainComplex.cm5b`,
  `degreewiseEpiWithInjectiveKernel`, and derived-category bounded-representative
  lemmas. None states the bounded-above flat functor with natural augmentation.
- `msearch.py ... loogle '"flat", "resolution"'`: zero hits.
- `msearch.py ... grep 'bounded.*flat|flat.*bounded|FunctorialFlat'
  Algebra/Homology`: zero hits.
- `msearch.py ... leansearch "functorial bounded above flat replacement of
  complexes of sheaves of modules"`: service unavailable, Internal Server Error;
  this is recorded as unavailable, not as no match.
- `rg` of upstream `WeilConjectures/` for flat resolutions and bounded flat models
  found `CochainComplex.exists_quasiIso_flat_of_isStrictlyLE` in
  `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`. Its complete
  signature and proof were read: it asserts an individual bounded flat model,
  not a functor with a termwise epic natural augmentation, and uses
  `ObjectProperty.flat` rather than the recorded ring-sheaf interface.
- `rg` of project `lean/Sheaf` and the DAG located the related generic
  `CochainComplex.exists_functorial_boundedAbove_flat_replacement` in
  `Sheaf.Algebra.Homology.BoundedFlatReplacement`. Its current full server source
  was read with `scompile.py --source`: its signature requires site objects and
  morphisms both in universe u and modules in u, and uses `IsFlat`. Thus it does
  not specialize directly to `T.Etale` with object/morphism universes u+1/u or
  supply the recorded independent-universe `IsFlatOnSite` interface. No new
  definition of either flatness or boundedness was introduced here.
- Search by the exact node id in upstream `WeilConjectures/` returned no hit.
  Searches of Mathlib, upstream, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the two proposed declaration names returned
  no existing declarations. Matches for the filename `BoundedFlatReplacement`
  refer to the different generic module discussed above; this delivery is in
  `Sheaf.Paper.BoundedFlatReplacement`.

Validation: the delivered file was compiled with `scompile.py Q17
lem-kun-bounded-flat-replacement`. The first attempt exposed a missing import of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`, needed to synthesize cohomology
for complexes of ring-sheaf modules. After adding that public import, the file
compiled cleanly (8.3 seconds for the library module; no warnings or errors).
The required delivery dry run follows this report; the second reading is reserved
for the independently started second reader.

## Second reading by Q17

I read the node `lem-kun-bounded-flat-replacement`, its source place (Stacks
Project Tag 05T7(1), with the flat-module convention of Tag 03ER(3)), the three
statement dependencies, and the complete module
`Sheaf/Paper/BoundedFlatReplacement.lean` independently.

The node's objects and hypotheses match the Lean as follows. The scheme `T` is
`T : Scheme.{u}`. The arbitrary coefficient ring is
`Λ : Type (u + 1)` with `[CommRing Λ]`; no field, characteristic, finiteness,
Noetherian, properness, nonemptiness, or invertibility assumption is present.
The coefficient sheaf is the constant sheaf
`(constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)`,
viewed as a ring sheaf through `sheafCompose` and `forget₂`; the site object and
morphism universes are retained. Complexes are
`CochainComplex (SheafOfModules ...) ℤ`, and the morphism property is Mathlib's
`QuasiIso`. For a fixed integer `N`, the input category is the full subcategory
whose objects satisfy `K.IsStrictlyLE N`; by
`CochainComplex.isStrictlyLE_iff`, this is exactly
`∀ i, N < i → IsZero (K.X i)`. Thus the full subcategory carries precisely the
node's bounded-above hypothesis and includes all maps between such complexes.
The existential `Φ` is a functor from that full subcategory, and `ε : Φ ⟶
ObjectProperty.ι _` is the augmentation. For every input `F`, the conjunction
`(Φ.obj F).IsStrictlyLE N`, the degreewise
`SheafOfModules.IsFlatOnSite` clauses, `QuasiIso (ε.app F)`, and
`∀ i, Epi ((ε.app F).f i)` render respectively the same bound, flat terms,
quasi-isomorphism, and termwise epimorphism in the node. Naturality of `ε`
expresses the required compatibility for every map in the full subcategory;
no additivity of `Φ` is assumed.

The final clause is rendered by
`exists_bounded_flat_replacement_zmod`: `n : ℤ`, an arbitrary bound `N`, and a
complex `F` over the constant sheaf of
`ULift.{u + 1} (ZMod n.natAbs)` with `[F.IsStrictlyLE N]` yield `P`, `q : P ⟶ F`,
`P.IsStrictlyLE N`, flatness in every degree, and `QuasiIso q`. The `ULift` is a
size placement only; `n.natAbs` gives the same principal quotient for positive,
zero, and negative integers. The node's final assertion asks only for a flat
quasi-isomorphic replacement, so it does not require the main theorem's
termwise-epimorphism clause in this specialization.

Edge cases checked: the zero complex and zero sheaf terms satisfy the bound and
flatness; the empty scheme is allowed by the unrestricted `Scheme` binder;
`N = 0` and negative `N` retain the strict upper-bound meaning; degree `N` is
allowed and only degrees strictly above it vanish; `n = 0` gives `ZMod 0 ≃ ℤ`,
`n = 1` gives the zero ring, and negative `n` uses the same quotient as its
absolute value. No universe equality beyond the recorded small-etale size
convention is imposed.

Searches were rechecked by exact declaration names and concepts with `rg` in
Mathlib, `WeilConjectures`, and `lean/Sheaf`, and with the recorded
LeanFinder/Loogle/LeanSearch searches. The only related declaration is the
generic `CochainComplex.exists_functorial_boundedAbove_flat_replacement` in
`Sheaf.Algebra.Homology.BoundedFlatReplacement`; it uses the generic `IsFlat`
interface and equal site/module universes, so it does not state this etale
specialization with `IsFlatOnSite` and the independent coefficient universe.
The upstream `CochainComplex.exists_quasiIso_flat_of_isStrictlyLE` is an
individual replacement and has no functorial augmentation. No exact declaration
of either theorem exists in Mathlib, upstream, or this project.

No mismatch was found, so no Lean or node repair was made. The module compiled
cleanly with `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q17
lem-kun-bounded-flat-replacement lean/Sheaf/Paper/BoundedFlatReplacement.lean`.
