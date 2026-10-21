## Worker report

The delivery states `lem-sfb-scalar-normalized-constant-models` in
`Sheaf.CategoryTheory.ScalarNormalizedConstantModels`, namespace
`CategoryTheory.ScalarNormalizedConstantModels`. All six theorems have `sorry`
proofs. Every definition and instance has actual data. No statement correction,
new definition node, or dependency-record repair is needed.

The retained import-only module and scratch probes were checked against current
sources. The published-library failure reported by the earlier attempts no longer
occurs. The final module compiles in both wrapper modes within the ordinary
60-second limit. Compilation is exclusively through the prescribed `scompile.py`.

Source read: the complete DAG statement and its eleven proof steps; Stacks
`sites-modules.tex`, labels `lemma-sheafification-presheaf-modules` (03CY) and
`lemma-sheafification-exact` (03EI); current blueprint
`sec-proetale-coefficients/sk-def-sfb-change-of-scalars/_section.md` (clause 2).
The source explicitly identifies this comparison as the node's agent-written
finite-presentation argument, rather than a theorem literally stated in Stacks.
There is no `blueprint_update` or maintenance repair note for the item.

Hypotheses and constructions, clause by clause:

* The site is `C : Type v`, `[Category.{w} C]`, `J : GrothendieckTopology C`.
  The object, morphism and coefficient universes stay independent. The
  `UnivLE.{max v w, u}` bound and its two component bounds express precisely that
  the site is small in the coefficient universe; the component bounds are
  spelled out because Lean does not infer them from the maximum bound.
  They impose no equality between site universes. Grothendieck topology is the
  topology component of the recorded site convention; the source uses only its
  sheaves and localized sites here. No extra pullbacks, terminal object or
  nonemptiness of the site is required.
* Exact abelian sheafification is `[hSheafify : HasSheafify J AddCommGrpCat.{u}]`.
  `[(J.W (A := AddCommGrpCat.{u})).IsMonoidal]` expresses tensor compatibility of
  sheafification. The tensor is the actual `Sheaf.monoidalCategory`, the same
  canonical structure as `sfbSheafTensorStructure`; `tensorLeftPreserves` and
  `tensorRightPreserves` use the recorded `sfbSheafTensor_properties` for its
  closedness consequences. The coefficient tensor is the integer tensor on
  `AddCommGrpCat`, including its `ULift ℤ` unit, never the cartesian tensor.
* The coefficient ring is `B : Type u`, `[CommRing B]`. The commutative internal
  ring is `R : Sheaf J AddCommGrpCat.{u}`, `[MonObj R]`,
  `[hRcomm : IsCommMonObj R]`. The map `σ : (constantRing B J).X ⟶ R` with
  `[IsMonHom σ]` is the specified ring-object map from the sheafified constant
  commutative ring. `constantRing` is the image of `CommMon.mk (AddCommGrpCat.of B)`
  under the constant-presheaf and sheafification functors on commutative monoids;
  no arbitrary ring, module action, or isomorphism is chosen.
* Internal modules are Mathlib `Mod`, with regular module `Mod.regular R`.
  `E` is exactly the specified equivalence from these internal modules to
  `Sheaf J (ModuleCat.{u} B)`, and `[hEadd : E.functor.Additive]` is retained in
  the existence theorem. `t` has the exact regular-module identification type.
  `include hSheafify hRcomm hEadd in` retains these stated hypotheses even where
  elaboration alone could omit them.
* `constantPresheaf` is the ordinary constant module presheaf over its
  reconstructed constant section ring. Its scalar data is the existing scalar
  action transported by the identity ring homomorphism. The identity's unit
  proof uses `Int.cast_one` because the reconstructed ring unit is expressed
  through the integer tensor unit. `constantInternalPresheaf` uses the recorded
  `InternalAbelianSheafModule.internalPresheafMod` and `internalPresheafMap`.
  `constantInternalModule` sheafifies that very action by `mapMod`, so its
  underlying abelian sheaf is the prescribed sheafification of the constant
  module presheaf. These are concrete specializations of the existing interfaces,
  not private replacements of internal modules, sheafification or extension.
* `model B J R σ` is `constantInternalModule B J ⋙ Mod.extendScalars σ`.
  The upstream extension is the actual balancing coequalizer from the dependency,
  with the action on the first factor. Thus its object at `P` is exactly
  `M_R(P) = R ⊗_{B̲} P̲`. It is defined on every ordinary module and linear map;
  finite presentation is required only in the comparison theorem.
* `constantElement` maps the tensor unit to the constant abelian sheaf by the
  integer map sending 1 to `p`. `modelGenerator P p` applies the canonical
  extension unit and `Mod.regularLift`, hence is exactly `r ↦ r ⊗ p`.
  `scalarEndomorphism b` similarly is multiplication by `σ(b)` on `R`.
* `scalarNormalized` says
  `E.map (scalarEndomorphism b) ≫ t.hom = t.hom ≫ constantSheaf.map (b • -)`
  for every `b : B`. This is precisely the conjugation equality in the node,
  with composition written in Lean's order. It does not assume that E is
  monoidal, already B-linear on arbitrary morphisms, or equipped with constant
  model comparisons.
* `Module.FinitePresentation B P` is Mathlib's ordinary finitely presented module
  predicate. It includes exactly the modules admitting a finite free cokernel
  presentation. `presentationComparison` also quantifies over the concrete
  presentations `q : (Fin m → B) ⟶ (Fin n → B)`, `π : (Fin n → B) ⟶ P`, with
  `Function.Exact q.hom π.hom` and `Function.Surjective π.hom`. No chosen
  presentation is built into `P` or the comparison.

Conclusions, clause by clause:

* `exists_comparison` states `∃! θ`, where every `θ P hP` is the required
  isomorphism `E(model P) ≅ (constantSheaf J (ModuleCat B)).obj P`.
  The first conjunct of `comparisonCondition` is naturality for every ordinary
  linear map between finitely presented modules.
* The second conjunct of `comparisonCondition` is normalization on the actual
  canonical maps `r ↦ r ⊗ p`. It is equivalent to the node's finite-free
  normalization: on `P = B^n` and `p = e_j` it uses t on each regular summand;
  for arbitrary P, the same equation follows by naturality of the map
  `B → P`, `b ↦ b • p`. In particular `p = 1` on B gives the regular-model
  identification. Thus this condition neither adds a scalar-linearity assumption
  on E nor changes the uniqueness being requested.
* `presentationComparison` states both actual cokernel universal properties:
  existential zero-composite proofs and `Nonempty (IsColimit
  (CokernelCofork.ofπ ...))` for the transported scalar matrix and for the
  sheafified constant matrix. Its last equation identifies their quotient
  projections by θ on the finite free source and θ on P. The extension of q is
  the matrix σ(q) under the generator identifications above. No arbitrary
  isomorphism between cokernel objects replaces their specified projections.
* θ is indexed by P, not by a presentation. Existence with `∃!` and the
  preceding quotient equation for every presentation express presentation
  independence and uniqueness among all natural comparisons with the stated
  finite-free normalization. The proof docstring gives the basis-lift and
  epimorphic-cancellation arguments explicitly.
* Localization is in the recorded sectionwise coordinates of internal modules.
  `sectionRing` uses the actual reconstructed ring sheaf from
  `InternalAbelianSheafModule.sectionRingSheaf`. `restriction U` is
  `sectionModuleFunctor J R ⋙ SheafOfModules.overFunctor (sectionRing J R) U`.
  The recorded equivalence retains the underlying abelian sheaf and map, so this
  is exactly `M|_U`, not a second restriction functor or an arbitrary transport.
  An internal equivalence E_U is written as `EU` on these coordinates of the same
  local ringed site; its supplied comparison is the natural isomorphism `eU`.
* The local tensor model is represented by `restriction U (model P)`: restriction
  takes the balancing coequalizer to the balanced tensor on the slice and takes
  its generator `r ⊗ p` to the same generator. For finite presentations this
  also follows directly from its restricted finite scalar cokernel presentation.
  `localPresentationComparison` explicitly states these local scalar cokernel
  universal properties and their normalized quotient equation. This fixes the
  actual local model through the same universal property as
  `M_{R|_U}(P)`; it is not an unspecified isomorphic object.
* `localComparison` has real data: `eU.app (model P)`, followed by the actual
  restriction of `θ P`, then `overPullbackConstantSheafIso.app P`.
  `localComparison_properties` takes the supplied `tU` and the equation `htU`
  expressing preservation of regular identifications. It asserts local naturality,
  the identical generator normalization using tU, and uniqueness among all local
  natural comparisons with that normalization. Naturality of eU at each scalar
  endomorphism, the global normalization, and htU are precisely preservation of
  the scalar endomorphisms in the node. No enough-points test occurs.
* `moduleRelocalization` is Mathlib `overFunctorMap` on the section module;
  `constantRelocalization` is built from the actual constant restriction and
  `Sheaf.pushforwardOverMapIso`. `localComparison_coherent` quantifies over every
  arrow `f : V ⟶ U`, the further local equivalence EV, its comparison eV, and
  the supplied natural isomorphism δ for further restriction. Its hypothesis
  `hcoh` is exactly the two-composite coherence equation. Its conclusion is the
  corresponding two-composite equation on θ, with these actual restriction
  maps. This includes identity arrows and the usual identification of iterated
  slices; it imposes no pullback or point hypothesis.
* `coverModels_iff` fixes the object X, index type I, individual objects W i,
  arrows `f i`, covering condition `Sieve.ofArrows W f ∈ J X`, module M and
  the individual finitely presented modules `P i`. Its left side is existence
  of the specified model isomorphism on every W i; its right side is existence
  of the corresponding constant model isomorphism for `(E M)|_(W i)` on exactly
  those members, with exactly those P i. EW and eW are the supplied local
  equivalences and their comparisons, not new realizations. Full faithfulness
  supplies the inverse direction without changing the cover or coefficients.
* There is no `Finite B`, `IsNoetherianRing B`, enough-points hypothesis,
  projectivity hypothesis on constant free sheaves, or monoidality hypothesis on E.

Dependency declarations used (full signatures and source docstrings were read):

* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`,
  `Mod.Hom`, `Mod.regular`, `Mod.regularLift`.
* `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `CategoryTheory.Mod.extendScalars`, `extendScalarsObj_X`, `extendUnitHom`,
  `extendRestrictAdjunction`, `extendπ`, and the balancing coequalizer interface.
* `Sheaf.CategoryTheory.SheafTensor`: `CategoryTheory.sfbSheafTensor_properties`;
  its structure is the existing `sfbSheafTensorStructure` from
  `Sheaf.CategoryTheory.SheafTensorStructure`.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  `WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal` supplies its
  canonical monoidal structure.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.presheafRings`, `internalPresheafMod`,
  `internalPresheafMap`, `sectionRingSheaf`, `sectionModuleFunctor`,
  `sectionModuleEquivalence`. Its node was already a proof dependency and has
  now also been added to `stmt_deps`, since actual constructions use its interface.
* `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`,
  `overPullback`, `overMapPullback`, `Sheaf.over`,
  `Sheaf.pushforwardOverMapIso`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `overMap`, `overFunctorMap`.
* `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `GrothendieckTopology.overPullbackConstantSheafIso` (the canonical continuous,
  cocontinuous sheafification comparison).
* The site's recorded `SiteCoveringAxioms` module is imported; the size-convention
  node is implemented by explicit universes and bounds, as its record requests.
  The original proof dependencies on module sheafification, constant-ring module
  equivalence, restriction exactness and equivalence preserving limits/colimits
  are also imported where their recorded modules exist. The unstated proof-only
  node `lem-sfb-modobj-cokernels` has no importable recorded module; the statement
  does not depend on an absent declaration from it.

Searches for an existing statement:

* Prescribed `msearch.py leanfinder`, query “additive equivalence of internal
  module sheaves normalized on regular scalar multiplication identifies finitely
  presented constant modules naturally”: eight hits, including
  `SheafOfModules.Presentation.map_generators_I`, `Presentation.mapGenerators`,
  `freeHomEquiv`, `presentationOfIsCokernelFree` and
  `PresheafOfModules.Sheafify.one_smul`. These give presentation/sheafification
  machinery, not this normalized equivalence comparison or localization coherence.
* `msearch.py loogle '"constantSheaf", "cokernel"'`: zero hits.
* `msearch.py grep 'scalarNormalized|scalar_normalized|constant.*[Mm]atrix.*[Cc]okernel'`:
  zero Mathlib hits. Earlier retained LeanFinder/Loogle/grep results in
  `searches.jsonl` agree, including the condensed-discrete special cases, which
  do not concern arbitrary sites with the specified σ and t.
* `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item id: no match.
  Searches for `scalarNormalized|scalar_normalized` found unrelated private
  evaluation/mate-pasting lemmas. Broader constant/internal-module searches found
  and were used to read `InternalAbelianSheafModuleEquivalence`,
  `ConstantInternalModuleSheafEquivalence`, `FiniteComparisonCoefficients`,
  `ConstantCoefficientScalarExtension` and the upstream ring/module functors.
  Their general interfaces or specialized finite/pro-etale realizations do not
  state this result. The delivery specializes the existing general interfaces.

Edge cases checked before finalizing the signatures:

* m = 0 and n = 0 use `Fin 0 → B` and honest cokernel universal properties;
  no positive-rank or nonzero-matrix condition appears.
* P = 0, the zero ring B, and zero sheaf R are allowed. The generator equations
  reduce to the appropriate zero maps; no `Nontrivial` instance is assumed.
* Empty and degenerate sites and empty covering families are allowed. No point,
  inhabited site, nonempty cover index or nondegeneracy assumption is introduced.
* B may be infinite and non-Noetherian. Only individual `P` need finite
  presentation. No constant free sheaf is assumed projective: the proof lifts
  maps only between ordinary finite free modules before applying sheafification.
* The three universes remain independent; no equality between object and
  morphism universes is forced by a specialized downstream API.
* The normalized comparison is natural for arbitrary linear maps, including
  nonisomorphisms, zero maps and maps between zero modules. Scalar normalization
  is quantified over every b, including 0 and 1.
* `localComparison_coherent` includes V = U and f = identity, and all further
  localization arrows. Its coherence is an equation of the two actual composites.

No `STATEMENT-DISPUTED` issue remains. The node's statement and proof are unchanged;
only its `lean` record and the added, already-landed statement dependency change.

## Second reading by Q42

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
