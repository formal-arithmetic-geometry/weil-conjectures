## Worker report

The module `Sheaf.Algebra.Homology.SourceHyperExtModuleTarget` states
`DerivedCategory.exists_source_hyperExt_module_target`, with proof `sorry`.
Its only helper, `DerivedCategory.sourceHyperExtAbutment`, is an abbreviation
for the actual module obtained by evaluating the recorded derived cohomology
of the recorded derived internal Hom. It has real data and introduces no
replacement for either construction. The item node changes only in `lean`.
There are no new nodes or dependency modules and no statement correction.

Source read: `literature/stacks-project/injectives.tex`,
`remark-spectral-sequences-ext-variant` (Tag 0G20), including the displayed
renumbering to Ext^i(H^{-j}(M),K), and the preceding
`remark-ext-from-filtered-complex` (Tag 0G1Z). The former's bounded-above
source and bounded-below target specialize to the present K and N[0]. The
node's explicit Hom-double-complex proof is carried into the theorem's
docstring, including the signs, endpoint calculation and degree translation.

Hypotheses and clauses:

| Node text | Lean rendering |
| --- | --- |
| A is an arbitrary commutative ring | `(A : Type u) [CommRing A]` |
| K is in the ordinary derived category D(A) | `K : DerivedCategory (RingSiteModules A)`; this is the existing one-object identity-covering presentation of ordinary A-modules, not a category of modules on a scheme |
| N is an A-module | `N : RingSiteModules A`, in the same presentation; `N.val.obj (op ⟨PUnit.unit⟩)` is its ordinary underlying A-module |
| Integer upper bound u | `(b : ℤ)`; b is the node's u, renamed to distinguish it from the universe |
| H^a(K)=0 for every a>u | `hK : ∀ a : ℤ, b < a → IsZero ((homologyFunctor (RingSiteModules A) a).obj K)` |
| N[0] | `(singleFunctor (RingSiteModules A) 0).obj N` in the abutment abbreviation |
| Derived internal Hom on the one-object site | `derivedInternalHomOfUniverses.{u, u, u, w} ⊥ (CochainComplex.onePointRingSheaf A)` evaluated on `(op K, N[0])` |
| Abutment H^t RHom_A(K,N[0]) | `sourceHyperExtAbutment A K N t`, evaluating `homologyFunctor` of this actual derived Hom at the unique object and bundling it in `ModuleCat A` |
| An A-linear spectral sequence | `E : E₂CohomologicalSpectralSequence (ModuleCat.{u} A)`; every differential is an actual A-linear morphism |
| E2^{i,j}=Ext_A^i(H^{-j}(K),N) for i>=0 | First conjunct: for `(i : ℕ) (j : ℤ)`, an isomorphism in `ModuleCat A` to `ModuleCat.of A (Abelian.Ext (ModuleCat.of A H^{-j}(K)(*)) (ModuleCat.of A N(*)) i)`; all nonnegative integer i occur by the Nat cast |
| Ext is in the abelian category of A-modules | `Abelian.Ext` is taken in `ModuleCat.{u} A`, using the existing `ModuleCat.HasExt` instance and the scalar action from `DerivedCategory.Ext.Linear` |
| E2=0 for i<0; every page zero outside i>=0,j>=-u | Second conjunct: for all `s`, `hs : 2 ≤ s`, `i j : ℤ`, `i < 0 ∨ j < -b → IsZero ((E.page s hs).X (i,j))` |
| Differential bidegree (s,1-s) | The definition of `E₂CohomologicalSpectralSequence` is `SpectralSequence` with `ComplexShape.up' (s,1-s)` |
| Next page is kernel(outgoing)/image(incoming) | The `SpectralSequence.iso` field gives `(E.page s).homology (i,j) ≅ (E.page (s+1)).X (i,j)`; in `ModuleCat A` homology is exactly this kernel/image quotient |
| Every fixed bidegree eventually stabilizes to E-infinity | `EInf : ℤ → ℤ → ModuleCat A` and third conjunct: for each i,j, some `r ≥ 2` and isomorphisms `e` from every page s>=r to `EInf i j` |
| Stabilization is through the sequence's maps | The third conjunct's equation compares `iCycles ≫ e_s.hom` with `homologyπ ≫ (E.iso s (s+1) ...).hom ≫ e_{s+1}.hom`. Thus these are compatible stable-page identifications, rather than unrelated isomorphisms |
| Finite exhaustive separated A-submodule filtration for every t | `F : ∀ t : ℤ, DecreasingFiltration (sourceHyperExtAbutment A K N t)` with `(F t).IsFinite ∧ (F t).IsExhaustive ∧ (F t).IsSeparated`. Subobjects in `ModuleCat A` are A-submodules |
| Successive quotients E-infinity^{t-j,j}, -u<=j<=t | Fourth conjunct: `(F t).F 0 = ⊤`, `(F t).F (t+b+1) = ⊥`, and for each `-b ≤ j ≤ t`, `Nonempty ((F t).gr (t-j) ≅ EInf (t-j) j)`. The indices i=t-j run through 0,...,t+b, exactly the nontrivial filtration steps |
| Empty interval gives zero abutment | Last conjunct: `∀ t : ℤ, t < -b → IsZero (sourceHyperExtAbutment A K N t)` |
| No Noetherian or finite-generation conditions | There are no such binders, predicates or instances |

The module/ordinary-module presentation is faithful without adding a
hypothesis: the underlying site is `Discrete PUnit`, its topology is bottom,
and every module sheaf is just its value at the unique object with the
identity restriction. Conversely any A-module defines the constant module
presheaf, which is a sheaf for bottom topology. The unique-object restriction
is the identity by functoriality. These inverse presentations preserve
linear maps, kernels, images and cokernels. Thus the K and N binders cover
ordinary modules and their entire derived category. In particular, the
statement does not replace ordinary Ext by a sheaf Ext object: it uses
Mathlib's ordinary `Abelian.Ext` in `ModuleCat A` itself.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.singleFunctor`, in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` (also reexported by the
  public cohomology import). The `w` parameter only chooses morphism sizes.
- `def-weil-derived-category-cohomology-functor`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`, in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `def-pur-derived-internal-hom`:
  `CategoryTheory.derivedInternalHomOfUniverses` from exactly its recorded
  module `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `def-sp-spectral-sequence`: `CategoryTheory.SpectralSequence`,
  `CohomologicalSpectralSequence`, `E₂CohomologicalSpectralSequence` and
  its `page`/`iso` fields, in `Mathlib.Algebra.Homology.SpectralSequence.Basic`.
- `def-pc-ext`: `CategoryTheory.Abelian.Ext`, from
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`; its `Module A`
  structure is from `Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear`,
  both publicly imported by `Mathlib.Algebra.Category.ModuleCat.Ext.Basic`.
- `def-sp-filtration`: upstream `CategoryTheory.DecreasingFiltration` and
  `DecreasingFiltration.gr`, in
  `WeilConjectures.CategoryTheory.Abelian.Filtration`, reexported by
  `WeilConjectures.CategoryTheory.CanonicalFiltration`; the latter exposes
  `IsExhaustive` and `IsSeparated`, and reexports `IsFinite` from
  `WeilConjectures.CategoryTheory.Filtration`.
- Existing presentation helpers: `CategoryTheory.RingSiteModules` in
  `Sheaf.Algebra.Homology.RingHomExtensionDefs` and
  `CochainComplex.onePointRingSheaf` in `Sheaf.Algebra.Homology.KFlatTensorQuasiIso`,
  publicly available through that import. These helpers are reused, not copied.

The non-public proof imports cover every recorded proof dependency:
`DerivedCategory.TStructure.t` and `isLE_iff` (standard t-structure);
`CategoryTheory.InjectiveResolution` (injective resolution);
`ModuleCat.enoughInjectives` (arbitrary ring modules);
`CochainComplex.isKInjective_of_injective` (bounded below injectives);
`CategoryTheory.homComplex` in its current upstream module;
`HomologicalComplex₂.firstFiltration` in `Sheaf.CategoryTheory.DoubleComplexTotal`;
`HomologicalComplex₂.exists_spectralSequence` in the current upstream
`WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex`; and
`CategoryTheory.InjectiveResolution.extEquivCohomologyClass` in
`Mathlib.CategoryTheory.Abelian.Injective.Ext` for the Ext identification.
The double-complex theorem's older `lean.module` records its former location
`WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`; the current source
of that file explicitly points to `ExactCouple.DoubleComplex`, and its
`lean_audit.slopmaster2.decls` also records the latter. The actual declaration,
signature and docstring were read there. No duplicate theorem was introduced.

Edge cases checked mathematically before and against the signature:

- K=0, N=0, or the zero ring: every displayed term can be zero; no nonzero
  module or nontrivial ring is assumed.
- K=M[-a] with a<=b: only j=-a can contribute to E2; the abutment in degree
  t is Ext^{t+a}(M,N), as required by the shift sign. This checks H^{-j},
  total degree i+j and the support sign j>=-b simultaneously.
- b=0 and t=0: the filtration runs F^0=H to F^1=0, with sole quotient
  E-infinity^{0,0}. Negative i are excluded by IsZero, not by a truncated
  index type that would lose other integer coordinates.
- Any b, t=-b: exactly j=-b contributes, giving i=0 and the same one-step
  filtration. At t=-b-1 the interval is empty, the explicit final conjunct
  gives zero, and F^0=top and F^0=bottom agree on that zero object.
- Arbitrarily negative b and t and unboundedly many negative source degrees
  remain allowed. No boundedness below is imposed on K. For fixed t the
  Hom total degree has only -t<=a<=b, which explains finite convergence.
- No projectivity, perfectness, Noetherianness or finite generation is
  imposed on either module or on cohomology.

Searches actually run through `batch2/msearch.py`, with group NE and this item:

- `leanfinder`, query `Source hyper Ext spectral sequence Ext of cohomology bounded above complex into a module`: 8 hits, including `CategoryTheory.Abelian.Ext` and injective/projective-resolution Ext/cohomology comparisons. None states this spectral sequence.
- `loogle`, query `CategoryTheory.SpectralSequence, CategoryTheory.Abelian.Ext`: 0 hits.
- `grep`, query `[Hh]yper.?[Ee]xt|[Ee]xt.*[Ss]pectral|[Ss]pectral.*[Ee]xt`, subdirectory `Algebra/Homology`: 2 hits, `SpectralSequence.hom_ext` and the generic spectral-object construction; neither is this theorem.
- `leansearch`, query `Spectral sequence Ext from cohomology of a bounded above complex to a module`: 8 hits, Ext definitions, exact sequences and resolution comparisons; no matching theorem.
- Direct `rg` of `lean/WeilConjectures` for this node id: no hits. Direct `rg` of `lean/Sheaf` and `lean/WeilConjectures` for hyper-Ext and RHom/spectral-sequence names finds `BoundedAboveRHomHyperExt`: that is the target-cohomology sequence E2^{p,q}=H^p RHom(K,H^q(L)[0]), a different statement. `BoundedAboveCoherentRHom` cites this still-missing source sequence in its proof docstring; it does not state it.
- Direct name search of Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` found neither `exists_source_hyperExt_module_target` nor `sourceHyperExtAbutment`.

Validation: the prescribed `scompile.py` compiled the delivered file both as
sandbox and library module against the server's published build, with exit
code 0, no errors and no warnings (10.6 s and 11.5 s respectively). The
initial parse-only failure from using an infinity character in an identifier
was repaired to the ordinary identifier `EInf`. Every universe and variable
is explicit and `autoImplicit` is false. No local notation, private helper
or file-local instance enters the statement. The declaration signature was
copied verbatim into `lean.statement`; `lean.declarations` lists both the
helper abbreviation and the theorem. There is no disputed statement or
unresolved node fault.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
