## Worker report

The main module `Sheaf.Paper.FlatExtendedCechComparison` states
`SheafOfModules.flat_extendedLocalizationCech_comparison_quasiIso`, with proof `sorry`.
It states the flat coefficient comparison of Stacks Tag 099H. The auxiliary module
`Sheaf.Paper.ExtendedLocalizationCech` supplies the previously missing actual extended
localization complex, its augmentation, its coefficient map, and the canonical quotient map.
Neither a theorem nor a definition with this general ringed-site scope existed in the searched
sources. No original node statement was corrected and no dependency record was replaced.

The statement-to-Lean correspondence is as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A small site | `{C : Type u} [Category.{u} C] {J : GrothendieckTopology C}`. The ring and module universe is `u`, so this includes all sites small relative to their coefficients. |
| Two sheaves of commutative rings | `(R B : Sheaf J CommRingCat.{u})`. `LocalizationCech.rings` is only the transparent underlying-ring-sheaf abbreviation `sheafCompose ... forget₂`. |
| A morphism of coefficient sheaves | `(φ : R ⟶ B)`. |
| A finite family of global sections, allowing r=0 | `(r : ℕ)` and `(f : Fin r → (unit (LocalizationCech.rings R)).sections)`. The rank-one module has exactly the ring sheaf's sections and restrictions. Indexing from zero only relabels the paper's indices 1,...,r. |
| B is flat over O | `hflat : IsFlat ((LocalizationCech.restriction φ).obj (unit (LocalizationCech.rings B)))`. This is the recorded flat-module definition applied to B with precisely its scalar action through φ. |
| The canonical quotient-ring-sheaf map is an isomorphism | `hquot : IsIso (LocalizationCech.quotientComparison φ r f)`. `idealRow` has generator components multiplication by f_i. Its cokernel is the sheafified quotient by their ideal, not a quotient of global sections. `quotientComparison` is the map induced by φ to the restriction of the B-cokernel. A canonical ring-sheaf morphism is invertible exactly when its underlying module morphism is; its inverse then respects multiplication and one by transport through the bijection. Thus this is precisely the ring-sheaf quotient hypothesis. |
| Degree zero is O | In `koszul`, degree zero is the coproduct over the unique empty subset. `degreeZeroFold` identifies it with `unit (rings R)`. Every degree-zero transition is the empty product, the identity, so its colimit has the same canonical identification. |
| Degree q=1,...,r is the product of the indicated localizations | `term R r q` is the finite free coproduct on `Indices r q`; `transitionTerm` multiplies summand I by the product of its f_i. `complex` is the sequential colimit of these complexes. The explicit fraction cocone sends a at stage n to a/(product_I f_i)^(n+1). Every fraction occurs; equality of fractions is eventual equality in the repeated-multiplication system. Colimits of module sheaves are sheafified sectionwise colimits, and finite coproducts are finite products. Consequently these are exactly the requested localization sheaves and finite products, with their canonical identifications. This is the construction of Tag 0913, not an arbitrary complex assumed to have the requisite properties. |
| Every other degree is zero | For q<0 or q>r, `Indices r q` is empty at every stage, so `term` and its sequential colimit are zero. No truncation hypothesis is imposed on a supplied complex. |
| Differential is alternating localization | `differential` inserts j with sign `(-1)^card({i in I : i<j})` and scalar f_j^(n+1). In fraction coordinates this scalar cancels the added denominator f_j^(n+1), leaving the localization map with exactly that sign. |
| Augmentation is identity in degree zero and zero elsewhere | `augmentationStage` is `HomologicalComplex.mkHomToSingle (degreeZeroFold R r) ...`; `augmentationCocone` and `augmentation` descend it through the actual colimit. `mkHomToSingle` is zero in the other degrees. Under the preceding degree-zero identification this is the identity. |
| The B-complex is constructed by the same formula with φ(f) | `complex B r (mapSection φ ∘ f)`. `mapSection` applies the component of φ to each section. |
| Canonical termwise φ map, with restriction of scalars | `comparisonTerm` uses `unitMap φ` on the same subset label; `comparisonStage` makes this a chain map. `comparisonCocone` descends these maps into the restriction of the target colimit using Mathlib's actual `SheafOfModules.restrictScalars`. Thus `comparison` sends a/g^k to φ(a)/φ(g)^k. It is not an unconstrained supplied map or a bare existence of a quasi-isomorphism. |
| Quasi-isomorphism, or equivalently invertibility of its image in D(O) | The conclusion is `QuasiIso (LocalizationCech.comparison φ r f)`, exactly the recorded definition of quasi-isomorphism of module-sheaf complexes. Mathlib's derived category localizes these same complexes at this same predicate. |

All universes and variables are bound explicitly. No local notation, private definition, local
instance, `let` in a statement, or extra mathematical hypothesis is introduced. Importing
`Mathlib.Algebra.Category.Grp.FilteredColimits` lets the standard small-site sheafification
and locally-bijective instances resolve automatically; there are no added sheafification
assumptions in the final signatures.

Dependency declarations read and used:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`: `SheafOfModules.IsFlat`, exactness of tensoring
  with the coefficient module. Its public dependency
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` supplies the recorded tensor and
  scalar-extension definitions for the proof plan.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently
  Mathlib's `SheafOfModules`, used in all constructed term and complex types.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used by the transparent `restriction` abbreviation.
- `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`, isomorphisms on all integer cohomology objects.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and `HasDerivedCategory`,
  the localization of these cochain complexes at quasi-isomorphisms. No derived-category
  universe choice is needed to state the complex-level quasi-isomorphism.
- Proof imports follow the existing plan: `CategoryTheory.Functor.homologyFunctorIso` in
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`,
  `CategoryTheory.moduleSheaves_colimits_forgetful` in
  `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`, and
  `CategoryTheory.Sheaf.hasExactColimitsOfShape` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`.

Edge cases checked mathematically before and against the definitions:

- r=0: only the empty subset occurs, the differential is zero, every transition is identity,
  and the augmentation identifies the complex with O[0]. `idealRow` has zero source, so
  `hquot` is exactly invertibility of φ. No `Nonempty (Fin r)` was added.
- r=1: the stage differential is multiplication by f^(n+1), with transition identity in
  degree zero and multiplication by f in degree one. The colimit is O → O[1/f], with
  its usual localization map, and the comparison has the expected two components.
- Every f_i zero: all nonempty-subset transitions are zero, so their colimits vanish;
  the complex is O[0] and the quotient hypothesis forces φ to be an isomorphism.
- A unit among the generators: localization at that unit gives the standard contraction;
  the quotient is zero, consistently allowing every coefficient map subject to flatness.
- The zero coefficient sheaf and the empty site are permitted. Empty finite indexing sets
  are handled by the actual empty coproduct, and no nontriviality or characteristic
  restriction has been imposed.
- Negative degrees and degrees greater than r are retained as integer degrees with empty
  indexing sets, not silently omitted from the quasi-isomorphism predicate.

Searches made:

- `msearch.py leanfinder`, "Flat extension of ring sheaves isomorphism modulo ideal quasi
  isomorphism extended localization Cech complex": eight ordinary flat-localization
  criteria (`Module.flat_of_isLocalized_span`, `Module.flat_of_localized_span`, etc.);
  none states this sheaf-complex comparison.
- `msearch.py loogle`, "Localization.Away, CochainComplex, SheafOfModules": no hits.
- `msearch.py leansearch`, "extended localization Cech complex of sheaves of rings as
  colimit of Koszul complexes": unavailable, Internal Server Error; no mathematical
  conclusion drawn from the unavailable service.
- `msearch.py grep`, "extended.*[Cc]ech|[Kk]oszul", Mathlib `Algebra/Homology`:
  one TODO in `LocalCohomology.lean:45` about Koszul homology, not this complex.
- `msearch.py leanfinder`, "Extended alternating localization Cech complex on a ringed site
  defined as the sequential colimit of positive power Koszul complexes": eight hits,
  headed by `localCohomology.diagram`, with Mayer-Vietoris square objects, a sheaf
  presentation colimit, and unrelated resolution constructions; none defines this complex.
- `rg` in the upstream `WeilConjectures` and current `lean/Sheaf`, with
  `extended|[Cc]ech|[Čč]ech|Localization.*[Cc]omplex`: upstream's
  `CategoryTheory/Sites/CechComplex` is the ordered Čech complex of a family of morphisms.
  The landed scheme `KoszulCech*` and `PrincipalCech*` files concern principal affine covers
  and complexes of quasi-coherent scheme modules. Their signatures were inspected;
  they do not give a general ringed-site localization complex. No applicable declaration.
- `rg` of the upstream name table and source for the proposed declaration names: no clashes.
  `rg` of the item id in the upstream source: no hits.
- All definition-node statements were searched for extended alternating Čech/localization
  complexes: no node supplies this notion. `tools/blueprint_refs.py search 'extended
  alternating'` reports zero blueprint nodes. The statement nodes mentioning the complex
  do not define it or have a usable declaration for it.

Both delivered modules were compiled separately in dependency order with `scompile.py`,
on the server at nice 19, two threads, and 60 seconds per file. The final run was clean:
`ExtendedLocalizationCech.lean` 3.5 seconds and `FlatExtendedCechComparison.lean` 1.3 seconds,
with no errors or warnings. No local compiler or global build was run.

The remaining `sorry`s are the main theorem and the named structural obligations
`insert_degree`, `differential_sq`, `transition_comm`, `mapSection_naturality`,
`unitMap_existsUnique`, `comparison_comm`, `comparisonCocone_naturality`,
`idealRow_comparison_zero`, `augmentation_incoming`, and `augmentation_naturality`.
Every one has its source, blueprint node, and complete natural-language proof in its docstring.
Every definition's data is a concrete finite-coproduct, specified matrix, colimit, cokernel,
or associated universal map. The sole use of theorem-chosen map data is `unitMap`;
`unitMap_existsUnique` fixes every sectionwise value and asserts uniqueness, so this does
not select an undetermined object from a mere existence claim.

## New nodes

`def-weil-pbc-extended-localization-cech` supplies the extended localization complex and the
canonical coefficient constructions missing from Mathlib, the upstream source, and the DAG.
Its module is `Sheaf.Paper.ExtendedLocalizationCech`, with primary declaration
`SheafOfModules.LocalizationCech.complex`. The complete construction is the explicit
positive-power cochain Koszul colimit of Stacks Tag 0913, as used on ringed sites in Tag 099H.
The node states the subset-indexed terms, insertion differential, product transitions,
fraction identification, augmentation, coefficient map, and quotient comparison. It cites
and imports the existing module category, complex, and scalar-restriction definitions;
it does not replace any of them. Its search records include the actual results listed above.
The original item gains this definition node in `stmt_deps` and otherwise changes only `lean`.

## Second reading by NI

I independently read the repository node, both sandbox modules, the new definition node,
Stacks algebraization.tex at lemma-map-identifies-koszul-and-cech-complexes (099H),
and more-algebra.tex at lemma-extended-alternating-Cech-is-colimit-koszul (0913).
099H assumes a site, a flat ring-sheaf map, global generators and the canonical quotient
isomorphism; it adds no separatedness, Noetherianity, characteristic or nonzero condition.
The surrounding discussion is about commutative ringed sites. The shifted exterior-basis
model in 0913 changes signs on complementary subsets; the delivered model directly uses
the alternating insertion signs, so its fraction identification has the required signs.

My statement checklist, with verdicts:

| Object, hypothesis or conclusion clause | Lean rendering and independent verdict |
| --- | --- |
| Small site C | `C : Type u`, `Category.{u} C`, `J : GrothendieckTopology C`: correct. |
| Commutative coefficient sheaves O and B | `R B : Sheaf J CommRingCat.{u}`; `rings` forgets only commutativity for the existing module category: correct. |
| Ring-sheaf map | `φ : R ⟶ B`: correct, with no extra condition on φ. |
| Finite global family with r at least zero | `r : ℕ`, `f : Fin r → (unit (rings R)).sections`: correct. Mathlib's unit has the coefficient presheaf as its underlying module and sections are compatible families, not just values at an assumed terminal object. |
| B flat with its φ action | `IsFlat ((restriction φ).obj (unit (rings B)))`: correct. I read `SheafOfModules.IsFlat`, whose tensor-right functor is exact, and `restrictScalars`, whose object uses the φ-restricted presheaf action. |
| Canonical quotient ring-sheaf map invertible | `IsIso (quotientComparison φ r f)`: correct. `idealRow` has precisely the multiplication-by-f components; its cokernel is O/I. The target row includes arbitrary B coefficients, giving B/IB. `unitMap` fixes the induced map sectionwise. The underlying module map is invertible exactly when the canonical ring-sheaf map is invertible, since its inverse preserves multiplication and one locally. |
| Degree zero O | `Indices r 0` has its unique empty subset; `term` is its coproduct of `unit`, and `subsetScalar` there is identity: correct. Its sequential colimit is canonically O. |
| Degrees 1 through r, finite products of the stated localizations | `complex := colimit (diagram ...)`, with `transitionTerm` the subset-product multiplication: correct. On subset I the cocone is a divided by g_I^(n+1). Every fraction is represented and equality is eventual equality. Sheafifying this calculation yields the localization sheaf. Finite coproducts equal products here. |
| Zero in all other integer degrees | `Indices r q` is empty for q negative or greater than r; both terms and their colimits are zero: correct. |
| Alternating localization differential | `differential` has sign `(-1)^card(filter (· < j) I)` and coefficient f_j^(n+1): correct. Dividing by g_(I union {j})^(n+1) cancels that coefficient and gives exactly the indicated localization map. |
| Augmentation to O[0] | `degreeZeroFold`, `augmentationStage`, `augmentationCocone`, `augmentation`: correct. The empty-subset component is identity and all other components of `mkHomToSingle` are zero. The only incoming source has negative degree and is zero. |
| Same B complex with images of f | `complex B r (mapSection φ ∘ f)`: correct, using componentwise φ on compatible sections. |
| Canonical termwise comparison into restricted B complex | `comparisonTerm`, `comparisonStage`, `comparisonCocone`, `comparison`: correct. On the I summand, the map is φ followed by the corresponding target coprojection. Passing to fractions gives φ(a)/φ(g_I)^k, with the specified restriction of scalars. |
| Comparison is a quasi-isomorphism | `QuasiIso (LocalizationCech.comparison φ r f)`: correct. I read Mathlib's predicate: every integer-degree homology map is invertible. `DerivedCategory` localizes these complexes at the same predicate, so this renders the node's derived assertion without adding a localization-choice hypothesis. |

I checked the remaining recorded dependencies and signatures: `ringedSiteModules` is exactly
Mathlib `SheafOfModules`, not the older scheme-only category; `Functor.homologyFunctorIso`
is the exact-functor homology comparison; `moduleSheaves_colimits_forgetful` gives the
faithful exact forgetful functor and sheafified colimit model; and
`Sheaf.hasExactColimitsOfShape` transfers exact colimits through sheafification on general
sites. Their imports and uses agree with the node's seven proof steps. The main docstring
carries those steps, including ideal-power induction and the filtered-colimit passage.

The new node `def-weil-pbc-extended-localization-cech` was also read as a new stage-1
notion. Its explicit subset terms, positive exponents, transitions, fraction coordinates,
augmentation, coefficient comparison and quotient map all match its module and 0913/099H.
Its definition-node fields, cited dependencies, ancestor/via, empty proof fields, searches,
creation record and Lean record follow brief-stage2 section 5. There are no dependency
replacement modules or statement corrections. The structural sorry theorems all belong
to this construction node, have source/proof docstrings, and only postpone proof fields.
`unitMap_existsUnique` determines every component and asserts uniqueness, so choosing its
map is allowed and does not hide undetermined data. All other construction data are explicit.

Edge cases checked independently: r=0 gives the singleton empty-subset term, identity
transitions, O[0], and quotient comparison φ itself; r=1 gives O → O[1/f]. If all f vanish,
positive-degree colimits vanish. A unit generator gives a contractible localization
complex and zero quotient. Zero coefficient rings and the empty site are allowed.
Negative degrees and degrees above r are included in `QuasiIso`. There is no characteristic
restriction. The common universe u can be enlarged to contain any given small site and
coefficient sheaves; no independent test-object quantifier becomes vacuous. All variables
and universes in the signatures are bound, with no hidden local notation or instances.

Independent searches used different wording:

- LeanFinder: "Stable Koszul cochain complex of global sections on a ringed site and
  invariance under flat change of rings" returned eight hits, headed by
  `PresheafOfModules.DifferentialsConstruction.instHasDifferentials`, with sheaf H,
  scheme flat_appLE and generic cochain factorization results; none matches.
- Loogle: `"Koszul"` returned no hits.
- LeanSearch: "Canonical map between extended localization complexes of ring sheaves
  unchanged by flat base change modulo the generators" was unavailable (Internal Server
  Error), recorded as unavailable rather than treated as a negative result.
- `rg` independently searched Mathlib Algebra, upstream WeilConjectures, project
  lean/Sheaf and DAG statements for stable Koszul, Koszul colimit, localization complexes
  and extended alternating complexes. I inspected `localCohomology.diagram` (Ext colimit
  over ideals), upstream `Presheaf.cechComplex` (cover nerve), project `KoszulComplex`
  (ring-module chain exterior complex), and `koszulCechHomDiagram_exists` (ring-module
  Hom complex). None supplies this general ringed-site construction or comparison;
  no existing definition node supplies it. No duplicate declaration should replace it.

No mathematical or signature mismatch was found, so I preserved both modules and both
node records. The only change is this independent review section. Both delivered modules
compiled cleanly through scompile.py in dependency order, server nice 19, two threads,
60 seconds per file: ExtendedLocalizationCech 3.4 s and FlatExtendedCechComparison 1.3 s.
No local compiler or global build was run. Lean signatures and node lean.statement fields
were checked verbatim; no warning was emitted.
