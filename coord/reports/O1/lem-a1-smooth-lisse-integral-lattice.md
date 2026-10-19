## Worker report

The module `Sheaf.Paper.SmoothLisseIntegralLattice` states
`AlgebraicGeometry.ProEtale.exists_smooth_lisse_integral_lattice` with a `sorry` proof.
It keeps the node's statement unchanged. Its auxiliary definitions give the actual
uniformizer section, the sheafified localization of the recorded completion, and its
canonical coefficient map. Site and slice sheafification instances transport the existing Grothendieck-abelian
construction through a small model; they contain no postponed data. The helpers take
`Small` and `LocallySmall` instances in the output universe, both automatic in the
common universe used by the theorem. These size conditions add no theorem hypothesis. A further transport instance uses
`preservesFilteredColimitsOfSize_of_univLE` to restrict preservation by the
forgetful functor from abelian groups to the smaller site-indexing universe. It
prevents an existing instance from unnecessarily identifying these universes.
The base and slice local-bijectivity instances likewise use the existing
essentially-small-site transport. No helper contains a postponed proof.

Hypothesis and conclusion correspondence:

- `K₀ K : Type u`, their `Field` instances, and `Algebra K₀ K` give the field inclusion.
  A unital map of fields is injective. There is no finite-generation or separability
  hypothesis on this extension.
- `T₀ : Scheme.{u}` and `f : T₀ ⟶ Spec (.of K₀)` give the scheme over the smaller field.
  `Smooth f`, `IsSeparated f`, and `LocallyOfFiniteType f` together with `QuasiCompact f`
  give exactly smooth, separated and finite type. Smoothness does not replace the
  global quasi-compactness part of finite type.
- Every occurrence of `T` is the explicit
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))`, the recorded scheme
  base change; no arbitrary scheme or chosen comparison is substituted.
- `l : ℕ`, `Fact l.Prime`, and `_hl : IsUnit (l : K₀)` give the prime invertible in K₀.
- `E : Type v`, `Field E`, `Algebra ℚ_[l] E`, and `FiniteDimensional ℚ_[l] E` give
  the finite coefficient extension, independently of the scheme universe.
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`
  are the dependency's actual valuation ring and chosen uniformizer.
- `WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T` is B_T,
  exactly the limit of the positive finite constant quotient sheaves. It does not
  assume a finite-field base datum. The commutative version has definitionally the
  same underlying ring sheaf.
- `smoothLatticeUniformizerSection` sends the constant uniformizer through the
  recorded canonical quotient-cone map. `smoothLatticeRationalRing` applies the
  recorded sheafified `Localization.Away` to this global section, so it is exactly
  E_T = B_T[1/varpi], including on non-quasi-compact site objects.
- `L : ringedSiteModules ...` over that rational ring and `_hL : L.IsFiniteLocallyFree`
  give precisely the locally finite free E_T-module sheaf in the node.
- The existential integral module `M` and `i : M ⟶ restrictScalars(...).obj L` with
  `Mono i` present an actual B_T-submodule sheaf of L. This is the usual categorical
  presentation of a subsheaf: its section maps are injective, and taking their images
  gives the literal subsets, compatibly with restrictions. Thus it does not merely
  assert existence of an abstract integral model.
- `M.IsFiniteLocallyFree` gives pro-etale local finite freeness of the submodule.
- `e : changeOfRingsOfUniverses ... M ≅ L` gives rationalization. The equation for
  every site object U and m in M(U) says `e(eta(1 tensor m)) = i(m)`, where eta is the
  actual module-sheafification adjunction unit. Tensor generation and the sheafification
  universal property therefore identify e with the map induced by the inclusion.
  The equation adds no choice or extra mathematical conclusion: it expresses the
  node's explicit inclusion-induced qualification.
- The module universe is `max v (u+1)`, containing both the independent coefficient
  universe and the site. Site objects stay in u+1 and arrows in u. No universe equality
  or auxiliary geometric hypothesis is introduced.

Dependency declarations used (their signatures and documentation were read):

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
  These implement the convention-only scheme-morphism dependency.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded note
  specifies `Limits.pullback` for scheme base change. The current source was read
  using `scompile.py --source`; the older local upstream checkout lacks this module.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly retains the integer,
  uniformizer, ideal, quotient and transition constructions in `CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and its imported
  `completedIntegralCoefficientSheafUnrestricted` and
  `completedIntegralCommRingSheafUnrestricted`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation of Mathlib's `SheafOfModules`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, whose local finite rank is allowed to vary.
- Added the already-landed dependency `def-weil-pbc-ringed-section-localization`:
  `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`,
  `ringedLocalizationRingOfUniverses` and `ringedLocalizationRingUnitOfUniverses`.
  Its independent-universe repair already exists and is used without restating it.
- Added the already-landed dependency `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`, reexporting
  `changeOfRingsOfUniverses` and `changeOfRingsPresheafOfUniverses`.

All currently recorded proof-dependency modules are imported without `public`.
The two proof dependencies `lem-a1-normal-proetale-monodromy` and
`lem-per-lisse-completed-system-comparison` have no recorded Lean modules and hence
cannot yet be imported. They are not needed to type this statement. The docstring
retains their exact roles in the seven-step proof, alongside the existing stable-lattice,
Galois comparison, geometric-normality, Noetherian and integral-reduction inputs.

Source checked directly: Bhatt--Scholze PDF pp. 58--60 and 70--71, especially Definition
6.8.3 (local finite freeness), Lemma 6.8.2 (completion and inversion), Proposition
6.8.4, and Lemmas 7.4.7/7.4.10 (normal, hence geometrically unibranch, monodromy).
The source's inversion of l agrees with inversion of the chosen uniformizer in a
finite coefficient extension. No statement fault or disputed clause was found.

Edge cases checked before writing: empty T (zero sheaf and empty trivializing cover),
rank zero, disconnected T with distinct component ranks, Spec K, arbitrary infinite
or inseparable K/K₀, and all primes including 2. There is no connectedness, nonemptiness,
constant-rank or field-extension-finiteness binder. Inverting the uniformizer is sheaf
localization, not an unjustified sectionwise identity on arbitrary site objects.

Searches made:

- `msearch.py leanfinder`: “Every lisse sheaf over a finite extension of the l-adic
  numbers on a smooth scheme has a global integral lisse lattice”. Eight results
  concern integral schemes, condensed modules, invariant rings and finite-type
  module sheaves; none states the item.
- `msearch.py loogle`: `"lattice", "Sheaf"`. Five hits concern complete lattice
  structures on submodule/ideal-sheaf posets; none is the integral-lattice theorem.
- `msearch.py leansearch`: “A locally free l-adic sheaf on a smooth scheme admits a
  global integral lattice”. Eight hits concern free sheaves, Z-lattices and free
  locally constant function modules; none states the item.
- `msearch.py grep`: `lisse|unibranch|[Ll]ocal[Ss]ystem.*lattice`. Three unrelated
  separatedness hits in Mathlib; no matching theorem.
- `rg` in upstream `WeilConjectures` for the item id and smooth/lisse/lattice terms:
  no item-id hit; `EtaleCohomology/Purity/RealSheaves/LocalSystems.lean` is about
  Weil representations and their generic lattices, not sheaves on this geometric fibre.
- `rg` in `lean/Sheaf` for lisse/lattice, finite local freeness, completion and
  localization found the APIs used above. The etale-local lattice theorem only
  gives lattices after a cover; the constructible-integral-lattice theorem gives a
  constructible model with no global lissity. Neither is an exact existing statement.
  The node-name registry and definition records were read to identify the actual
  completion, localization and tensor owners. No duplicate notion is introduced.

Validation: the only postponed proof is the named theorem
`AlgebraicGeometry.ProEtale.exists_smooth_lisse_integral_lattice`. The auxiliary
constructions contain real data. Every compile uses the prescribed `scompile.py`
wrapper with its unchanged 60-second per-file limit; final results are recorded below.

Final file-only compilation through `scompile.py` passed on 2026-10-18: sandbox
7.7 seconds and library-path check 12.5 seconds, with no errors or unexpected warnings.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
