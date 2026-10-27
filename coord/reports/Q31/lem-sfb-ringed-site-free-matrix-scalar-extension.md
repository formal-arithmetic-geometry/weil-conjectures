## Worker report

The module `Sheaf.CategoryTheory.RingedSiteFreeMatrixScalarExtension` states
`CategoryTheory.InternalAbelianSheafModule.ringedSiteFreeMatrixScalarExtension`.
Its sole theorem has proof `sorry`. The theorem's docstring carries all eight DAG
proof steps. The node is unchanged except for its `lean` record.

The module uses the existing internal finite free object `Mod.finiteFree R n`,
the finite biproduct of `Mod.regular R`, rather than defining another free object.
`RingedSiteFreeMatrices` packages the coordinate and matrix conclusions; it is not
an assumption. The theorem constructs this package for both R and S. Coordinates
are fixed by the actual biproduct projections and matrices by global basis images,
so existentially packaging the data does not replace the canonical maps with
arbitrary isomorphisms. `ringedSiteExtensionTmul` is the actual lax tensor comparison
into the sheaf tensor followed by `Mod.extendπ`, with real data throughout.

Hypotheses and clause correspondence:

- The site is `{C : Type v} [Category.{w} C] (J : GrothendieckTopology C)`.
  Site object and arrow universes stay independent. `UnivLE.{max v w, u}`,
  `HasSheafify J AddCommGrpCat.{u}`, and `(J.W ...).IsMonoidal` are precisely
  the applicability hypotheses of the recorded `sectionModuleEquivalence`.
  The tensor is `Sheaf.monoidalCategory`, the sheafification of pointwise abelian
  tensor, with its existing symmetric structure. No additional closedness,
  flatness, points, subcanonicality, nonzero-ring or positive-rank hypothesis.
- The final object is `(one : C) (hOne : IsTerminal one)`, and restriction of
  global entries is along `(hOne.from U.unop).op`.
- `R,S : Sheaf J AddCommGrpCat.{u}` with `MonObj` and `IsCommMonObj` are the
  commutative internal ring objects; `(ψ : R ⟶ S) [IsMonHom ψ]` is their map.
  The rings A and B are literally `(sectionRingSheaf J R).obj.obj (.op one)`
  and its S version, reconstructed by the recorded dependency, not arbitrary
  section rings. The map φ is `ψ.hom.app (.op one)` on these carriers; the
  monoid-morphism condition ensures it preserves their multiplication and unit.
- `Mod.finiteFree R n` is the node's internal `R^{⊕n}`, for every `n : ℕ`.
  `coordinates : ... ≃+ (Fin n → R(U))` gives its section tuples;
  `coordinates_projection` identifies them with the canonical projections.
- `matrix : (Mod.finiteFree R n ⟶ Mod.finiteFree R m) ≃+ Matrix (Fin m) (Fin n) A`
  is the canonical additive bijection for all m,n. `matrix_basis` identifies
  each entry with the i-th component of the global image of e_j, where e_j is
  `coordinates.symm (Pi.single j 1)`; inverse laws of `≃+` give uniqueness.
- `matrix_sections` is exactly the sum of restricted global t_ij times a_j.
  In particular it applies to the inverse image of any matrix, since `matrix`
  is a bijection. `matrix_comp` is `matrix (f ≫ g) = matrix g * matrix f`;
  `matrix_id` gives the identity matrix.
- The theorem existentially supplies `θ n : (Mod.extendScalars ψ).obj
  (Mod.finiteFree R n) ≅ Mod.finiteFree S n`. These are isomorphisms in the
  internal S-module category. Its first conjunct gives the forward local
  pure-tensor formula `b * ψ(a_j)` in reconstructed section rings. The explicit
  `@id` merely types the same element in the reconstructed ring carrier.
- The second conjunct gives the inverse on every tuple `(b_j)` as the finite
  sum of `ringedSiteExtensionTmul ... (b j) ...e_j`. The isomorphism inverse
  laws are part of `≅`; the sheaf tensor and balancing quotient are the
  recorded ordinary constructions, not an arbitrary extension functor.
- The third conjunct identifies the matrix of
  `(θ n).inv ≫ (Mod.extendScalars ψ).map f ≫ (θ m).hom` with the entrywise
  map of `dR.matrix m n f` by `ψ.hom.app (.op one)`.
- The fourth conjunct uses the actual adjunction unit `Mod.extendUnitHom` and
  says its j-th coordinate after θ is `ψ.hom.app U (a_j)` on every section
  ring; n=1 is the stated coefficient-unit map.
- `zero_ranks` in each matrix package states both Hom and matrix types are
  `Subsingleton` when m=0 or n=0. Both are additive groups, hence these are
  singleton zero groups. The final three `IsZero` clauses state that the R
  and S rank-zero free objects and the extension of the R rank-zero object
  are zero. The family θ also explicitly includes its rank-zero isomorphism.
- Every tensor formula starts at the lax tensor comparison and the relative
  coequalizer projection. There is no assertion that arbitrary sheaf tensor
  sections equal tensors of the section rings.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`,
  `sectionModuleFunctor`, `sectionRings`, and `sectionRingSheaf`. The first
  is read with its full site hypotheses and identity-on-sections construction;
  the latter supplies exactly the reconstructed commutative section rings.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`,
  `Mod.Hom`, `Mod.regular`, and `Mod.comap`; these are the recorded module
  object and restriction notions, with the regular action equal to multiplication.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars`, `extendScalarsObj_X`, `extendπ`, `extendScalarsMap`,
  `extendπ_extendScalarsMap`, `extendUnitHom`, `extendUnit`,
  `extendHomEquiv`, and `extendRestrictAdjunction`. These supply the exact
  ordinary relative coequalizer, map on arrows and coefficient unit. The
  general restriction/coextension interfaces are inherited unchanged.
- `Sheaf.CategoryTheory.SheafTensor`: `sfbSheafTensor_properties`, used only
  to obtain its colimit-preservation fields in two named helper instances.
  The sheaf tensor and strong monoidal sheafification are the dependency's
  existing ones; no new tensor is defined. The small-model helper uses
  Mathlib's `essentiallySmall_of_small_of_locallySmall` and universe transports.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`, publicly inherited through the
  equivalence module and used in the documented proof plan.
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.finiteFree`;
  its full abelian, preadditive and finite-colimit hypotheses are inferred
  from the sheaf framework. The helpers do not add any new mathematical
  hypotheses to the theorem.

Sources read: Hemo–Richarz–Scholbach Example 3.1, PDF page 6, and
`literature/stacks-project/sites-modules.tex`, `section-tensor-product`
(Tag 03EK), including the sheafified tensor definition. Example 3.1 supplies
context, whereas the node's explicit finite-basis/coequalizer proof supplies
this general-site statement. No statement correction or disputed clause found.

Edge cases checked mathematically: n=0 and m=0 give empty coordinate or entry
sets; the sums are empty and both types have their unique zero. Rank zero
extension is explicitly zero. n=m=1 gives multiplication by a single global
section, and its base change applies ψ to that section. For composition the
order is V*T for f followed by g. Zero rings are permitted: no `Nontrivial`
instance occurs. A site with an empty covering of its final object causes no
failure: its corresponding section objects can be zero. No flatness, enough
points or sectionwise tensor exactness is used.

Searches performed:

- `msearch.py ... leanfinder`: "Finite free internal sheaf module homomorphisms
  are matrices of global sections and extension of scalars applies a ring
  homomorphism entrywise". Eight hits, including `SheafOfModules.freeHomEquiv`,
  `freeHomEquiv_comp_apply`, `freeHomEquiv_symm_comp`, `freeMap`,
  `map_ιFree_mapFree_hom`, `unitHomEquiv_symm_freeHomEquiv_apply`, and
  `Presentation.mapGenerators`. Read Mathlib's `Sheaf/Free.lean`: the Hom
  bijection is sectionwise and lacks this internal coequalizer compatibility
  and normalized matrix formulas; it is not an exact existing declaration.
- `msearch.py ... loogle "SheafOfModules.freeHomEquiv, Matrix.map"`: zero hits.
- `msearch.py ... grep "freeHomEquiv|extendScalars"
  Algebra/Category/ModuleCat/Sheaf`: sixteen hits, with freeHomEquiv and
  free-module generators/presentations, no exact theorem.
- `rg` on the named Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` trees
  for matrix/free/extension names, and the exact node id: no exact binding.
  Scheme-specific `Scheme.Modules.freeMatrix` and `matrixHom` statements
  concern schemes and a sectionwise pullback, not this arbitrary ringed site.
- Broader declaration search in `CategoryTheory/ModuleObjects` found
  `Mod.finiteFree` in upstream `Free.lean`; read its entire definition and
  replaced the initially considered product realization with this existing
  finite-biproduct definition. No duplicate finite-free definition is delivered.
- Exact proposed declaration-name search in `dag/lean_names_upstream.json`,
  Mathlib, upstream Lean and project Lean found no collisions.

Validation: `scompile.py Q31 lem-sfb-ringed-site-free-matrix-scalar-extension`
compiled the delivered file both in sandbox module mode and at its final module
path, cleanly (3.8 s and 4.3 s). Only the intended theorem is postponed; all
helper definitions and instances have real data. `autoImplicit` is disabled,
all universes are declared, and the module has no local notation, private
construction, file-local instance or diagnostic command.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
