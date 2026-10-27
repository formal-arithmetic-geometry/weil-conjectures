## Worker report

Item: lem-trf-fitting-sheaf-arbitrary-pullback. Group Q58, stage 2, 2026-10-24.

The new module `Sheaf.AlgebraicGeometry.FittingSheafArbitraryPullback` states
`AlgebraicGeometry.Scheme.Modules.fittingSheaf_arbitrary_pullback`, with its proof
`sorry`. Three transparent helper definitions instantiate existing constructions:
`affinePullbackTensor` is Mathlib's extension of scalars applied to the section module;
`affinePullbackOneTensor` is its adjunction unit, hence precisely `1 ⊗ m`;
`affinePullbackPresentation` is the recorded `LinearMap.baseChangePresentation`
for the induced section ring map. They introduce no independent mathematical notion,
no arbitrary map, no choice of data from an existence assertion and no new DAG node.

The node statement, proof, dependencies, and all other pre-existing fields are unchanged.
Only `lean` is added. No definition has a postponed proof or unspecified data. The sole
postponed theorem is the item itself, whose docstring includes all five DAG proof steps
and their cited nodes. There is no statement dispute or source correction.

Hypotheses and clauses, matched against the node:

- Arbitrary schemes and morphism: `{T S : Scheme.{u}} (g : T ⟶ S)`.
  The universe is explicit and arbitrary. There is no flatness, Noetherian,
  separation, finite-presentation or nonempty-scheme assumption.
- The finite-type quasi-coherent module is `(F : S.Modules) [F.IsFiniteType]
  [F.IsQuasicoherent]`. The index `r ≥ 0` is `(r : ℕ)`, including zero.
- The node's G is always the actual `(tensorPullback g).obj F`, defined by the
  dependency's explicit sheaf tensor construction. It is never an arbitrary sheaf.
- The preservation conclusions are `∃ (hft : ...IsFiniteType)
  (hqc : ...IsQuasicoherent), ...`. These bind the two proved properties as conclusions,
  allowing their use in `@fittingIdealSheaf T ... hft hqc r`; they add no hypotheses.
- Every affine pair is quantified by `∀ (U : S.affineOpens) (V : T.affineOpens)
  (h : V.1 ≤ g ⁻¹ᵁ U.1)`. This is exactly `g(V) ⊆ U`. The ring map throughout is
  `(g.appLE U.1 V.1 h).hom`. Thus A, B and M are respectively `Γ(S,U.1)`,
  `Γ(T,V.1)` and `Γ(F,U.1)`, not separately selected rings or modules.
- `affinePullbackTensor g F U V h` is B tensor_A M, as a bundled B-module.
  Its definition uses `ModuleCat.extendScalars` of the actual ring map.
  The finite-free presentation helper installs only that map's `.toAlgebra` and
  applies the existing `baseChangePresentation`; the scalar convention agrees
  definitionally with the extension-of-scalars module.
- The sheaf isomorphism clause is `Nonempty (G.restrict V.1.ι ≅
  (tilde (affinePullbackTensor ...)).restrict V.2.isoSpec.hom)`.
  Both objects are modules on the same open subscheme V: the tilde lives on Spec B
  and is transported along the canonical affine isomorphism V → Spec B. No new
  associated-sheaf definition is introduced.
- The resulting identification of sections is a B-linear equivalence `e` from that
  exact tensor module to `Γ(G,V.1)`. Its formula for every original section m is
  `e (affinePullbackOneTensor ... m) = G.presheaf.map (homOfLE h).op
  (tensorPullbackSection g F U.1 m)`. This is restriction of the actual normalized
  pullback section, so an arbitrary automorphism of sections is not substituted.
- Every finite generating family is represented by `∀ (n : ℕ)
  (m : Fin n → Γ(F,U.1)), Submodule.span A (Set.range m) = ⊤ → ...`.
  The conclusion is `Submodule.span B (Set.range (fun i ↦
  affinePullbackOneTensor ... (m i))) = ⊤`, the same family's tensors with 1.
  The B-linear equivalence transports these to the specified pulled-back sections.
- The affine Fitting calculation quantifies over every finite-free surjection π,
  rather than inventing a second definition of module Fitting ideals. It states
  `(fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r`, surjectivity
  of `affinePullbackPresentation ... π`, the equality of the pullback sheaf's
  ideal on V with that tensor presentation's ideal, and equality of the latter
  with `Ideal.map` of the original ideal. Presentation independence of the
  recorded dependency means these are exactly Fit_r(M), Fit_r(B tensor_A M)
  and φ(I)B. Surjectivity after tensoring does not assert injectivity of the kernel map.
- The global equality is `@fittingIdealSheaf T G hft hqc r =
  (fittingIdealSheaf F r).comap g`. Here `IdealSheafData.comap` is the extended
  ideal subsheaf: it is the kernel of the base-changed closed-subscheme map.
  Its precise affine formula is `IdealSheafData.ideal_comap_appLE` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine` (read lines 95ff):
  `(J.comap g).ideal V = (J.ideal U).map (g.appLE U V h).hom`.
  Thus the final equality means equality of ideal subsheaves, including for
  nonflat maps; it never treats the pulled-back inclusion as monic.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes the recorded finite-type
  and quasi-coherence notions, `SheafOfModules.IsFiniteType` and `IsQuasicoherent`;
  the node also exposes `Scheme.Modules.IsQuasiCoherentFiniteType` and
  `RingedSpace.IsCoherent`. The item requires the first two predicates separately.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: publicly exposes
  `Scheme.Modules.tensorPullback`, `tensorPullbackObj`, and the real-data
  `tensorPullbackSection` used in the normalization formula. The upstream
  tensor construction and the normalized adjunction's full signatures were read.
- `Sheaf.AlgebraicGeometry.FittingIdealSheaf`: `Scheme.Modules.fittingIdealSheaf`,
  taking finite-type and quasi-coherence instances and returning `X.IdealSheafData`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `AlgebraicGeometry.tilde`,
  `tilde.toOpen`, `tilde.toOpen_res`, and the tilde/Gamma adjunction and
  quasi-coherent counit interface of the proof dependency.
- `Sheaf.RingTheory.PresentationFittingIdeal`: `LinearMap.presentationFittingIdeal`,
  `baseChangePresentation`, and `presentationFittingIdeal_independence_baseChange`.
  Its full statement covers arbitrary scalar extension and localization with no
  finiteness assumption on the presentation kernel.

The module also imports the recorded, stated proof dependency modules:
`WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType`
(`tensorPullback_isFiniteType`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
(`isQuasicoherent_pullback`),
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
(`quasicoherent_finite_type_affine`),
`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
(`exists_tensorPullback_affine_sections`),
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`
(`tensorPullbackObjUnitToUnit`, `tensorPullbackObjUnitToUnit_isIso`), and
`WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
(`quasiCoherent_cokernel_image`).
The Mathlib module-base-change and tilde-free-module matches are already publicly
available through the statement imports. `lem-trf-fitting-ideal-sheaf-affine-sections`
is presently unstated and contributes no module to import; it is a proof prerequisite,
not a missing notion needed to type the statement, and is not silently assumed.
No proof dependency was replaced by a new private definition.

Edge cases checked before writing:

- Zero module and n=0: the empty family has span top precisely for the zero module;
  its scalar extension is zero. The empty finite-free presentation is allowed.
- r=0: maximal kernel-row minors give the zeroth Fitting ideal.
- r≥n: both presentation ideals are top by the dependency's explicit convention;
  extension takes top to top, including the zero ring.
- Empty affine opens and the empty scheme: no nonemptiness binder appears; section
  rings/modules can be subsingletons and all displayed comparisons retain meaning.
- Nonflat Z→F_p and M=Z/p: the zeroth Fitting ideal (p) extends to zero,
  as required for the one-dimensional F_p module. Tensoring the ideal inclusion
  need not be injective, which is why the conclusion uses the extended ideal.
- Finite modules with infinitely generated relation modules: all formulas use
  arbitrary kernel rows and finite-free generating surjections only; finite
  presentation is not inferred or required.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder "Fitting ideal sheaf commutes with arbitrary scheme
  pullback"`: eight hits, chiefly `IdealSheafData.comap`, `map`, `comapIso` and
  their functoriality; none states the Fitting or finite-generator assertion.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Modules.pullback, Ideal.map"`:
  zero hits.
- `msearch.py ... grep "fittingIdeal|FittingIdeal|fitting_ideal" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Fitting ideal sheaf arbitrary pullback affine tensor
  finite generating family"`: eight hits on general ideal sheaves, generating
  sections, and free pullback; no Fitting base-change theorem.
- `rg` of the same Fitting patterns in `lean/WeilConjectures` and the item id
  found no upstream declaration. Searches of `lean/Sheaf` found the existing
  Fitting definitions, presentation theorem, and bounded-generator-locus theorem;
  the latter contains the original-affine presentation equality but not this
  item's tensor comparison, finite-family statement and global ideal equality.
  All those usable notions were reused. Searches for `fitting.*pullback`,
  `fitting.*comap`, `arbitrary_pullback` and `arbitraryPullback` found only prose
  references in unrelated consumers, not an exact statement.

Validation: `scompile.py Q58 lem-trf-fitting-sheaf-arbitrary-pullback <module>`
succeeded for both the sandbox compilation and the actual library module with no
errors or warnings. Every universe/variable is bound explicitly (`autoImplicit false`).

## Second reading by Q58

I reopened the node and the compiled module for a separate clause-by-clause self-check.
No other agent was started, as the dispatch brief explicitly forbids that; this section
is not claimed as an independent worker review. The maintainer supplies the independent
review named in the dispatch brief.

The check compared the arbitrary-morphism and finite-type/quasi-coherent binders,
the nonnegative index, each affine pair and its actual induced ring map, the tilde
transport to V, the B-linear section comparison and its normalization, every finite
family including the empty family, both affine Fitting equalities, and the global
ideal-subsheaf equality. The first compile exposed that `F.presheaf.obj` is an
abelian-group object rather than a bundled module; the helpers now use
`ModuleCat.of A Γ(F,U)` with its existing scalar action. Recompilation is clean.
No mathematical statement correction or dependency-interface repair was needed.
The helper definitions only specialize existing constructions belonging to this
node, and all four declarations carry this node's blueprint tag.
