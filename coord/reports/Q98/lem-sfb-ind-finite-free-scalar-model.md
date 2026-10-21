## Worker report

Item: `lem-sfb-ind-finite-free-scalar-model`. Module:
`Sheaf.Algebra.Homology.IndFiniteFreeScalarModel`. Primary declaration:
`SheafOfModules.IndFiniteFree.ind_finite_free_scalar_model`.

This states the entire node, including coefficient maps, indexing functors, local
pure-tensor normalization, arbitrary K-flat resolutions, and ordinary unbounded
localization. Its one theorem has proof `sorry`. The auxiliary definitions contain
real data. Only the item's `lean` field changes; there are no statement corrections,
new DAG nodes, or dependency repairs.

The helper definitions belong to this node's canonical comparison, and are all listed
in `lean.declarations`. `Modules` and `restriction` transparently abbreviate the recorded
module category and Mathlib restriction, respectively. `algebraModules` sends an object
`R → S` of `Under R` to its restricted regular module; on morphisms it uses the original
section maps, whose R-linearity follows from the triangle over R. `tensorComplex` applies
the existing monoidal tensor termwise. `tensorDiagram` and `tensorColimit` are the actual
coefficient-tensor diagram and its categorical colimit. `pureTensor` and `extensionPure`
apply the existing sheafification units, followed only by the existing tensor comparison
or the model's prescribed object equality. They do not introduce another tensor or
another scalar-extension object. `Normalized` and `CoefficientCompatible` spell out
clauses of this node as propositions so the main statement remains readable.

Hypotheses, one by one:

- A site small in the coefficient universe: `{C : Type u} [Category.{v} C]
  [EssentiallySmall.{r} C] {J : GrothendieckTopology C}`. The object, Hom, and coefficient
  universes remain independent. The explicitly declared sheaf-compose, sheafification,
  and locally-bijective instances are the infrastructure for the abelian module
  category on this essentially-small site, as in the dependencies. They impose no
  geometric or coefficient-ring restriction.
- The commutative ring sheaf is `{R : Sheaf J CommRingCat.{r}}`. `Modules R` is the
  recorded `CategoryTheory.ringedSiteModules`, definitionally `SheafOfModules` over
  the underlying ring sheaf `derivedChangeRingIndependentCoefficients J R`.
- Cochain complexes and ordinary derived categories are Mathlib's
  `CochainComplex (Modules R) ℤ`, `DerivedCategory (Modules R)`, and `DerivedCategory.Q`.
  The source and target localization universes are independent `wR` and `wS`, with a
  further independent `wT` for the other coefficient diagram. No derived-complete,
  bounded, or constant-coefficient category is substituted.
- A small filtered indexing category is `{I : Type r} [SmallCategory I] [IsFiltered I]`.
  This includes general filtered categories, not just directed posets.
- Exact I-colimits are `[HasExactColimitsOfShape I (Modules R)]`: Mathlib's exactness of
  the actual colimit functor. Colimits themselves exist from the small-site module
  infrastructure.
- The algebra diagram is `D : I ⥤ Under R`. Thus each object is exactly a commutative
  ring sheaf with its R-algebra structure map, and every transition respects R.
- `c : Cocone D` and `hc : IsColimit c` give S as the algebra colimit, where
  `S = c.pt.right`, the structure map is `c.pt.hom`, and `q_i = (c.ι.app i).right`.
- Finite freeness is `hfree : ∀ i, ∃ d : ℕ, Nonempty ((algebraModules R).obj (D.obj i) ≅
  ∏ᶜ fun _ : Fin d ↦ unit (... R))`. A finite product in this abelian category is the
  finite direct sum R^d. Only existence of each basis is assumed; there is no compatible
  basis, positive-rank, or uniform-rank hypothesis.
- The second colimit hypothesis is `hcModules : IsColimit
  ((algebraModules R).mapCocone c)`, using exactly the same coprojections and apex.
- The ordinary extension E and K-flat-derived extension are the fields `m.E`, `m.T`,
  and `m.ε` of an arbitrary existing `DerivedChangeOfRingsCochainModel c.pt.hom`.
  That interface fixes E on objects to `changeOfRings` and on maps to
  `changeOfRingsHom`, supplies its additivity and universal left-derived counit, and
  computes it on K-flat complexes. Taking an arbitrary presentation does not impose
  another hypothesis: the recorded dependency supplies its existence, and all such
  universal pairs are canonically isomorphic. U is `restriction c.pt.hom`.

Conclusions, one by one:

- Exact E: the first two existential witnesses are `PreservesFiniteLimits m.E` and
  `PreservesFiniteColimits m.E`; additivity is already a field of the existing model.
  Exact U is also supplied so its derived restriction can be used below.
- Preservation of every quasi-isomorphism: the first conjunct quantifies over all
  `A B : CochainComplex (Modules R) ℤ` and every `f : A ⟶ B`, with conclusion
  `QuasiIso ((m.E.mapHomologicalComplex (.up ℤ)).map f)` whenever `QuasiIso f`.
- The natural isomorphism counit is `IsIso m.ε`, the existing canonical counit itself,
  rather than existence of an unrelated isomorphism between the two objects.
- For **every** K-flat resolution `p : P ⟶ A`, the next conjunct gives an isomorphism
  `e : m.T.obj (Q.obj A) ≅ Q.obj (E(P))` with precisely
  `e.hom = m.T.map (inv (Q.map p)) ≫ m.ε.app P`, and
  `e.hom ≫ Q.map (E(p)) = m.ε.app A`. Thus under the canonical K-flat identification
  the counit is Q(Ep), with the correct direction. There is no assumption that A is
  K-flat, and no degreewise-flatness or surjectivity requirement on the chosen p.
- The chain comparison is a **natural isomorphism**
  `κ : tensorColimit D ≅ E.mapHomologicalComplex (.up ℤ) ⋙
  U.mapHomologicalComplex (.up ℤ)`. `tensorColimit D` really uses `colim` in the
  category of cochain complexes; its colimits are computed termwise by Mathlib's
  homological-complex colimit instances.
- `Normalized D c m κ` says, for all A, i, n, V, s, a, that the degree-n component of
  `colimit.ι (tensorDiagram D A) i ≫ κ.hom.app A` sends the **sheafification-unit**
  image `pureTensor ... s a` to `extensionPure m ... (q_i(s)) a`. This is the exact
  local normalization in the node, not a formula on arbitrary hypothetical generators.
- Compatibility with chain maps is the naturality of κ. The next conjunct also states
  that `tensorColimit D` preserves quasi-isomorphisms.
- Compatibility with inverted quasi-isomorphisms is made explicit by a localized
  functor KD, its factorization `θ : Q ⋙ KD ≅ tensorColimit D ⋙ Q`, and a **natural
  isomorphism** `κD : KD ≅ m.T ⋙ U.mapDerivedCategory`. The displayed equation identifies
  its restriction along Q with Q(κ) using the actual counit and the canonical
  `U.mapDerivedCategoryFactors` comparison. Hence the comparison respects all derived
  morphisms, including inverses of quasi-isomorphisms.
- `CoefficientCompatible` quantifies over another filtered coefficient diagram satisfying
  the same exact-colimit, algebra-colimit, underlying-colimit, and finite-free
  hypotheses, with arbitrary model m' and any normalized κ'. It allows any indexing
  functor `F : I ⥤ I'`, a natural transformation `τ : D ⟶ F ⋙ D'`, and an algebra map
  `h : c.pt ⟶ c'.pt` satisfying exactly `q_i ≫ h = τ_i ≫ q'_(F i)`.
- In that clause, `βS : m.E ⟶ m'.E ⋙ restriction h.right` is characterized on all local
  sheafification-unit tensors by `s ⊗ a ↦ h(s) ⊗ a`. Its underlying R-linear map β has
  the same section maps. The colimit map L is characterized on **every colimit leg**
  by tensoring τ_i and then taking the target coprojection. These equations specify
  canonical maps; they do not substitute unconstrained maps for coefficient change.
- The coefficient square `L.app A ≫ κ'.hom.app A = κ.hom.app A ≫ β_complex.app A`
  states the chain compatibility. The final square for `βD : m.T ⟶ m'.T ⋙
  (restriction h.right).mapDerivedCategory` states the counit compatibility **in D(S)**
  after restriction along h:S→S', using Q_S(βS) and the canonical restriction
  factorization. Its normalization uniquely determines the derived coefficient map
  since both counits are invertible and Q is essentially surjective. Naturality of
  βD also covers inverted quasi-isomorphisms. The claim is not weakened by forgetting
  an equality in D(S) to an equality in D(R).
- Every complex quantifier is over ℤ-indexed cochain complexes. No boundedness appears.

Dependency declarations used/read:

- `def-weil-size-convention`: metatheoretic convention; explicitly independent universes
  and `EssentiallySmall.{r} C` here, as its convention-only record directs.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its independent-site additive instances;
  the tensor is the existing localization tensor. The actual unit comparison is
  `SheafOfModules.tensorObjIsoSheafification`, not a second tensor.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `colimit`,
  `colimit.ι`, `colim`; filteredness is `CategoryTheory.IsFiltered`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.

The stated proof dependencies are imported as ordinary (non-public) proof-plan imports:
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`;
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`;
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison`;
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`;
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`;
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
`Mathlib.CategoryTheory.Localization.Predicate`.
Mathlib's `Functor.homologyFunctorIso` and `Functor.mapDerivedCategoryFactors` give
respectively the exact-complex cohomology and exact derived-factorization leaves; the
latter module is publicly imported because its actual factorization maps occur in the
statement. Module sheafification is the recorded
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` construction and adjunction,
used by `pureTensor`; all its types/docstrings and those of the other recorded
statement dependencies were read. No unusable statement dependency was replaced.

Edge cases checked before and during drafting: rank d=0 (the empty finite product is
the zero module); the zero coefficient ring; zero modules and the zero complex;
nonzero differentials and complexes unbounded on both sides; a one-object filtered
category; filtered categories with parallel arrows; I cannot be empty by its stated
filteredness, with no additional nonemptiness assumption; independently sized site
objects/Homs/coefficients/localizations; identity coefficient maps; indexing functors
rather than just maps on a fixed poset; any K-flat resolution, not a fixed chosen one.
No freeness of S itself, nontriviality, field, Noetherian, stalk/points, or positive
characteristic assumptions appear. No statement fault or dispute was found.

Searches actually made (2026-10-21):

- `msearch.py ... leanfinder`: "For sheaves on a small ringed site scalar extension by a
  filtered colimit of finite free algebra sheaves is exact and computes unbounded
  derived extension with its tensor colimit comparison". Eight hits included condensed
  AB5 and exact-colimit facts, light-condensed projectivity, and
  `CategoryTheory.Functor.mapExactFunctor_smul`; none stated this ringed-site result.
- `msearch.py ... loogle`: `SheafOfModules, "changeOfRings"`: zero hits.
- `msearch.py ... grep`: `finite.free|indFinite|scalarModel`, subdirectory
  `Algebra/Category/ModuleCat/Sheaf`: zero hits.
- `msearch.py ... leansearch`: "Exact scalar extension for filtered colimits of finite
  free ring sheaves and unbounded derived extension counit". Eight hits, including
  ordinary ModuleCat extension/restriction counits, `ModuleCat.FilteredColimits.colimitHasSMul`
  and `colimitModule`, and `Condensed.profiniteSolidCounit`; no match.
- `rg` of both `lean/Sheaf` and `lean/WeilConjectures` for
  `indFiniteFree|ind_finite_free|scalarModel|finite.free.*[Ss]calar|` the item ID found
  related DVR, finite-constant, finite-completed and derived-internal-Hom files, not
  this full statement. The dedicated name search for `IndFiniteFree` and
  `ind_finite_free_scalar_model` in both libraries and `dag/lean_names_upstream.json`
  had no matches. The literal `grep -rn` for this item ID in `lean/WeilConjectures`
  also had no matches.
- Source inspection found `CategoryTheory.commAlgebraSheafModuleFunctor` in
  `WeilConjectures.CategoryTheory.CommAlgebraSheafModule`; its signature is restricted
  to the open-set site of a topological space. The present helper generalizes its
  ordinary sectionwise construction to the arbitrary small ringed site of the item;
  no topological-space or open-site restriction is imposed on this theorem.
- Read the nearby filtered-flat-sheaf theorem: it concerns directed posets and
  flatness only, and has neither the canonical unbounded derived counit nor these
  normalized coefficient/colimit squares. The ordinary-module K-flat counit theorem
  likewise has ordinary rings/modules, rather than this general ringed site.

Server verification: every compile used the prescribed `scompile.py Q98
lem-sfb-ind-finite-free-scalar-model <module path>`. The initial helper module, the full
statement, and the corrected full D(S) coefficient square each compiled in both sandbox
and library mode with no errors or warnings. The last run reported 7.6 s and 6.8 s.
There is one named postponed theorem and one `sorry`; its docstring carries all eight
DAG proof steps and their dependencies. All lines are at most 100 characters and
`autoImplicit` is disabled. Final preflight/compile is also run through `deliver2.py`.

## Second reading by Q98

Author's second reading, not an independent reviewer: reopened the node and the complete
module after the first clean compile, following the direct-worker brief (no subagents).
Checked every hypothesis and conclusion listed above against both texts. The initial
coefficient-counit equation was expressed only after restriction to R; that could forget
information in the derived category. Replaced it by the actual square in D(S), using
`βS`, exact restriction along `h.right`, and the corresponding `βD`. Kept the underlying
R-linear map only for the κ square, and explicitly identified its section maps with βS.
Recompiled cleanly after this change.

Rechecked that `Normalized` uses the true sheafification-unit tensor and the original
q_i, that `tensorColimit` is a genuine colimit of chain complexes, and that κ is natural
rather than an unrelated collection of object isomorphisms. Rechecked the direction of
the K-flat representative isomorphism and the equation giving Q(Ep). Rechecked that
all three localization universes are independent and that no boundedness, rank positivity,
compatible basis, or arbitrary-complex K-flatness hypothesis slipped in. The coefficient
clause covers indexing functors and supplies maps determined by explicit local/cocone
normalizations. No further mismatch found; the JSON signature is extracted verbatim from
the theorem keyword through the type, before `:=`.
