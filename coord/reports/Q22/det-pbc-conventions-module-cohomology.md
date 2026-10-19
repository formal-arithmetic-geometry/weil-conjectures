## Worker report

Item: det-pbc-conventions-module-cohomology. Module:
`Sheaf.AlgebraicGeometry.ModuleCohomologyConventions`; main declaration:
`AlgebraicGeometry.Etale.module_cohomology_conventions`.

The theorem states the blueprint's three numbered assertions as four conjuncts:
the last numbered assertion has both its higher-direct-image and its D+ parts.
Its proof is `sorry`. The only other declarations are the concrete identity
`moduleEvaluationForgetIso` and its canonical derived transformation
`moduleEvaluationForgetComparison`. They belong to this node's canonical-map
interface and introduce no independent notion. The identity is `Iso.refl`; the
higher transformation is the existing `Functor.rightDerivedBaseChange` applied
to it. A `letI` in that definition supplies Mathlib's existing coefficient-forgetful
colimit instance with explicit universes; it neither adds a theorem hypothesis nor
creates a new category or a new exactness axiom. There are no file-local instance declarations, file-local notation,
auto-bound variables, or further postponed theorems.

Source read: blueprint main-20261015, sec-proper-base-change,
`sk-def-pbc-conventions/sk-def-pbc-conventions-module-cohomology.md` and its
companion `.proof.md`. The node now has the completed six-step stage-1 split;
the theorem docstring follows those six steps, naming their dependencies. The
blueprint's arguments use Stacks 03FD, 03F3 and 0D6J(3).

Hypotheses and clauses:

| Node text | Lean rendering |
| --- | --- |
| Any commutative ring Λ and any scheme T | `(Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})`; `u` is explicitly declared. This is the coefficient-size convention recorded in the sheaf and derived-category dependencies. |
| Mod(T_et,Λ), Ab(T_et), and For | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`, and the existing `moduleAbelianForget Λ T`. The latter is exactly `sheafCompose` with `forget₂ (ModuleCat Λ) AddCommGrpCat`. |
| (1) Every injective module sheaf I | The first conjunct quantifies over `I` in that module-sheaf category and over `[Injective I]`. There is no injectivity hypothesis on its underlying abelian sheaf. |
| (1) Every étale U → T | `(U : T.Etale)` is arbitrary. Evaluation is `sheafToPresheaf ... ⋙ (evaluation _ _).obj (op U)`. Its derived functors are cohomology over U. Localization identifies this with cohomology of the restriction on U_et, as in the recorded localization dependencies. |
| (1) H^q(U_et,For I)=0 for q>0 | `(q : ℕ), 0 < q → IsZero (...)`, applied to the q-th right-derived abelian evaluation at `(moduleAbelianForget Λ T).obj I`. The object is in AddCommGrpCat, where IsZero is vanishing of the abelian group. |
| (2) Every module sheaf F, every U, every cohomological degree | The second conjunct quantifies over arbitrary `F`, `(U : T.Etale)` and `(q : ℕ)`, with no positivity restriction. |
| (2) The canonical For H^q_Λ(U,F) → H^q(U,For F) is an isomorphism | `IsIso ((moduleEvaluationForgetComparison Λ T U q).app F)`. Its source is the forgotten right-derived ModuleCat-valued evaluation, and its target is right-derived abelian evaluation after For. The map is derived from the identity on section groups, using the unit-compatible base-change construction, not an arbitrary chosen isomorphism. It is a natural transformation in F, so componentwise IsIso supplies the natural comparison isomorphism. |
| (3) Every morphism f:S → T and every F on S | The third conjunct binds `(S : Scheme.{u}) (f : S ⟶ T)` and an arbitrary module sheaf `F` on S. There are no properness, finiteness, flatness, or torsion assumptions. |
| (3) For R^q f_* F → R^q f_* For F is an isomorphism | The third conjunct asserts `IsIso` of the component at F of `Functor.rightDerivedBaseChange (moduleAbelianLowerStarIso Λ f).hom q`. G and G' are the recorded `lowerStar` functors for ModuleCat and AddCommGrpCat; β and γ are For on S and T. Thus both endpoints and the specified canonical map are fixed. It includes q=0. |
| (3) Every K in D+(S_et,Λ) | The fourth conjunct binds `K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. This is the existing bounded-below derived category with the global derived-category instance. |
| (3) For R f_* K → R f_* For K is an isomorphism in D+(T_et,Z) | `IsIso ((moduleAbelianDerivedLowerStarComparison Λ f).app K)`, reusing the existing canonical comparison. Its source is `R+ lowerStarModule ⋙ For.mapDerivedCategoryPlus`, its target is `For.mapDerivedCategoryPlus ⋙ R+ lowerStarAb`, and its ambient category is the bounded-below derived category of abelian étale sheaves on T. |
| Warning: For need not preserve injectives; only its acyclicity is used | Only I in the module-sheaf category is required to be injective. The first conjunct says precisely the needed positive-degree abelian evaluation acyclicity. The proof docstring explicitly avoids claiming preservation of injectives by For. |

Cohomology is expressed using Mathlib's existing right-derived evaluation, not a
new cohomology definition. The sites-and-cohomology node retains Mathlib's Sheaf.H'
and cohomologyPresheafFunctor convention; the standard derived-evaluation
identification and the two localization dependencies give its section-cohomology
meaning. At the terminal object this is the right-derived global-sections
interpretation recorded by `def-weil-pbc-etale-cohomology`.

The ModuleCat encoding is explicitly allowed by both
`def-weil-pbc-etale-sheaves` and `def-weil-pbc-derived-categories`. The source of
`Scheme.etaleConstantModuleFunctor_isEquivalence` was obtained with
`scompile.py --source WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`
when it was absent from the local source checkout. Its construction and inverse
retain the underlying abelian presheaf; this identifies the encoding with modules
over the constant ring sheaf, including the direct-image constant-scalar action.
No dependency interface was replaced and no other DAG node is stated.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded `CategoryTheory.Sheaf`,
  `SheafOfModules`, constant sheaves, and the small-étale coefficient conventions.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`;
  `InjectiveResolution` was read in its Mathlib Resolution module.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and `.cohomology`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` and its record's retained Mathlib
  cohomology conventions.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; right derivation uses the existing generic
  `Functor.rightDerived`, `Functor.rightDerivedFunctorPlus`, and their comparison
  maps. The record's older spelling `rightDerivedLowerStarPlus` is not required.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: existing `DerivedCategory`,
  `DerivedCategory.Plus` and the recorded ModuleCat encoding.
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`:
  `AlgebraicGeometry.Etale.moduleAbelianForget`, `.moduleAbelianLowerStarIso`,
  `.moduleAbelianDerivedLowerStarComparison`, and
  `.isIso_moduleAbelianDerivedLowerStarComparison`. This is already a proof
  dependency; its concrete canonical-map declarations are publicly imported
  because they occur in the statement. They are reused rather than copied.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`
  (publicly imported by that comparison module): `Functor.rightDerivedBaseChange`.
  Its docstring and full signature were read: its source is γ(R^qG F), its target
  R^qG'(βF), and its normalization comes from the derived-functor units.
- Proof imports, exactly following the node's plan:
  `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
  (`Scheme.etaleModule_enoughInjectives`),
  `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
  (`CategoryTheory.moduleSheaves_colimits_forgetful`),
  `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
  (`CategoryTheory.cohomology_over_object_localization`),
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
  (`Scheme.Etale.overEquiv`, `.overSheafEquiv`),
  `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`
  (`CategoryTheory.module_abelian_evaluation_comparison`),
  `Mathlib.CategoryTheory.Abelian.RightDerived`
  (`Functor.isZero_rightDerived_obj_injective_succ`), and
  `WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`
  (`Scheme.etaleConstantModuleFunctor_isEquivalence` and its concrete functors).

Edge cases checked before finalizing:

- Λ may be the zero ring: no Nontrivial assumption, and all comparisons still have
  their stated endpoints and canonical maps.
- T, S, or the étale object U may be empty: no inhabitedness or nonemptiness is
  required. Evaluation and its right-derived functors remain defined.
- q=0 is included in both comparison clauses but excluded from the vanishing
  clause. A nonzero injective over a point can have nonzero sections.
- For T=Spec of an algebraically closed field and Λ=F_p, an injective Λ-module can
  have an underlying abelian group that is not injective; the theorem does not
  assume that stronger property.
- Identity morphisms and arbitrary scheme morphisms f are included. There is no
  auxiliary isomorphism, representative, acyclic resolution, or comparison lift
  supplied as a hypothesis. The D+ clause includes all bounded-below complexes,
  with no upper bound or torsion restriction.
- The scheme universe and coefficient universe follow the already recorded
  u/u+1 convention; site object and morphism universes have not been equated.

Searches for an existing full statement (through msearch.py Q22 with this item):

- LeanFinder: `module cohomology sheaves etale forgetful functor injective derived
  functor Gamma`. Eight results including Sheaf.H, cohomologyPresheaf and
  injective-presheaf material; none states all three clauses.
- Loogle: `SheafOfModules, sheaf cohomology, derived functor, forgetful functor`.
  Invalid identifier `sheaf`; no useful conclusion from that query. A valid
  subsequent query `CategoryTheory.Functor.rightDerived` returned twelve results,
  including rightDerived, rightDerivedZeroIsoSelf, and injective vanishing.
- Mathlib grep: `rightDerived|sheafCompose|SheafOfModules` in CategoryTheory/Sites.
  Returned section/sheaf-composition infrastructure, not the complete statement.
  An earlier query with Mathlib-prefixed subdirectories was not a usable search.
- LeanSearch: `Forgetting the coefficient ring on etale module sheaves commutes
  with higher direct images and cohomology`. Eight results concerning toSheaf and
  module-sheaf infrastructure; no complete theorem.
- Source and side-library rg: searches for module/cohomology/forget/derived
  combinations found `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget` and
  `EtaleModuleInjectiveForgetAcyclic`. Both were read: they are global-sections
  special cases, so neither is an existing match for arbitrary étale U and all
  direct images. The canonical direct-image comparison was found, read, and reused.
- Exact item-id and new-declaration searches in WeilConjectures/, lean/Sheaf/,
  Mathlib and dag/lean_names_upstream.json found no duplicate of this complete
  statement or of the added helper names.

No statement correction, new DAG nodes, dependency modules, or statement dispute.
Only the item's `lean` field changes in its copied JSON. All variables are bound
explicitly and the single postponed theorem has the matching node and complete
proof docstring. The module compiled cleanly with scompile.py. The independent second reading
is left to the second reader, as required.

## Second reading by Q22

I read the unchanged node statement against the main-20261015 blueprint detail and
its companion proof, then Stacks `sites-cohomology.tex`,
`lemma-cohomology-modules-abelian-agree` (03FD), including its injective-acyclicity
proof, and `lemma-modules-abelian-unbounded` (0D6J), part (3). Those sources assume
a site and a sheaf of rings, not Noetherianity, properness, torsion, flatness, or an
invertible characteristic. The small-etale specialization adds no such hypothesis.
No repair note for this item is present. No `statement_change`, new definition
node, or dependency module is present in this delivery.

My object/hypothesis/conclusion checklist, independently matched to the file:

| Node item | Lean and verdict |
| --- | --- |
| Arbitrary commutative ring Lambda | `Λ : Type (u + 1)` and `[CommRing Λ]`. Pass: no `Nontrivial`, finiteness, or characteristic assumption. |
| Arbitrary scheme T | `T : Scheme.{u}`. Pass: no geometric property is assumed. |
| Module sheaves, abelian sheaves, and For | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`, and the imported `moduleAbelianForget Λ T`. Pass: I opened its abbreviation; it is `sheafCompose` of `forget₂`. The sheaves and derived-categories dependency records explicitly permit this encoding. |
| Injective I only in the module category | First conjunct: arbitrary module sheaf `I` with `[Injective I]`. Pass: Mathlib's `Injective.factors` is the extension property along every mono. There is no abelian-injectivity hypothesis. |
| Every etale object U and positive degree q | First conjunct: `U : T.Etale`, `q : ℕ`, `0 < q`. Pass: no restriction on U and no positive degree omitted. |
| Vanishing of underlying abelian cohomology | First conjunct: `IsZero` of abelian evaluation's `rightDerived q` at `For I`. Pass: an object of AddCommGrpCat, so this is zero group cohomology. Evaluation at U is the derived section functor in 03FD; localization identifies it with restriction to U_et. |
| Arbitrary module F, U, and q, including zero | Second conjunct: arbitrary `F`, `U : T.Etale`, `q : ℕ`. Pass: no injectivity or positivity is imposed. |
| Canonical forgotten module-cohomology comparison is invertible | Second conjunct: `IsIso ((moduleEvaluationForgetComparison Λ T U q).app F)`. Pass: I expanded both helper types. The source is forgotten ModuleCat-valued derived evaluation; the target is abelian derived evaluation after For. The input identity `moduleEvaluationForgetIso` is `Iso.refl`, and `rightDerivedBaseChange` derives that identity with its unit normalization. Naturality in F is part of the transformation. |
| Every morphism S to T and every F on S | Third conjunct: arbitrary `S : Scheme.{u}`, `f : S ⟶ T`, and module sheaf `F` on S. Pass: no extra geometric hypothesis. |
| Canonical comparison of all higher direct images | Third conjunct: `IsIso` of `Functor.rightDerivedBaseChange (moduleAbelianLowerStarIso Λ f).hom q` at F. Pass: G/G' are exactly the recorded module/abelian `lowerStar`; beta/gamma forget coefficients on S/T. I read `lowerStar`'s pullback-precomposition definition and its section formula. |
| Every bounded-below K on S | Fourth conjunct: `K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Pass: Mathlib's Plus is the full bounded-below derived subcategory, without a chosen bound, an upper bound, or torsion condition. |
| Canonical For Rf_*K to Rf_*For K in D+(T,Z) | Fourth conjunct: `IsIso ((moduleAbelianDerivedLowerStarComparison Λ f).app K)`. Pass: I opened that existing definition; its endpoints are the two stated composites and its construction derives the underived coefficient-forgetting identity. It is precisely the unit-compatible comparison of 0D6J(3). |
| Warning about failure to preserve injectives | No conjunct asserts preservation of injectives by For; the first conjunct states acyclicity. Pass. |

Dependency-interface reading: I opened the signatures and defining formulas in
`EtaleSheaves`, Mathlib `Injective.Basic`, `Derived.LowerShriek`,
`SiteCoveringAxioms`, `UpperLowerStar.Defs`, and `DerivedCategories`, and read the
module/abelian direct-image comparison module and upstream `PlusBaseChange`.
In particular, `rightDerivedBaseChange` is obtained by applying cohomology to the
bounded-below comparison on F[0], so the third and fourth conjuncts use compatible
canonical maps, not unrelated isomorphisms. I also retrieved and read the current
`EtaleConstantRingModuleEquivalence` source via `scompile.py --source`: the
restriction functor retains the abelian presheaf, and extension and restriction
are inverse equivalences via identity maps on sections. This validates the
constant-ring-module interpretation used in the node and its proof.

Edge cases: the zero ring, zero sheaf, zero complex, empty S or T, empty etale U,
and identity f are all admitted by the binders and constructions. There is no
index family in this statement. Degree zero is included in both comparison
clauses and correctly excluded from injective vanishing. For a point with
coefficients F_p, an injective module need not be an injective abelian group;
this does not invalidate or strengthen any hypothesis. There is no characteristic
restriction. The explicitly bound universe u, site object universe u+1 and
morphism universe u, and coefficient-value universe u+1 follow the two dependency
records' size convention; no equality of site object and morphism universes is
imposed and no independent small test universe makes a hypothesis vacuous.

Independent H4 searches (msearch.py, recorded in searches.jsonl):

- LeanFinder: `Scalar restriction of coefficient sheaves commutes with right derived sections at every object of the small etale site` returned eight scalar-restriction and module-sheafification declarations, not the complete theorem.
- Loogle: `"rightDerived", "forget"` was valid and returned zero hits.
- LeanSearch: `Cohomology of an injective module sheaf after restriction of scalars to abelian groups vanishes on every etale object` returned eight results, including `Sheaf.H`, restriction of scalars, and injective replacement infrastructure, not this statement.
- Direct rg over Mathlib CategoryTheory and ModuleCat, upstream WeilConjectures,
  and project Sheaf searched `(forget|restrictScalars|toSheaf).*(rightDerived|cohomology)`
  and the reversed order. I opened `EtaleModuleCohomologyForget` (global-sections
  comparison only) and `InjectiveModuleAbelianAcyclic` (the injective-vanishing
  clause only, in the constant-ring encoding). The existing derived-direct-image
  comparison supplies clause (3) only and is already reused. None is an existing
  match for the full conjunction. Exact helper-name searches found no collision.

H5/H6/H8/H9: the two helpers contain real constructions, with no postponed data
or proof inside a definition. The only theorem is the named node theorem with
`by sorry`. Its docstring has all six node-proof steps with their dependencies;
all three declarations have source and blueprint docstrings. All Lean lines are
at most 100 characters; there is no file-local instance, private definition,
notation, statement `let`, or unbound variable. I checked that `lean.statement`
is verbatim the theorem signature, with the proof delimiter omitted.

No mismatch was found; no Lean or node repair was needed, and I preserved both.
I added only this independent second-reading record and search evidence.
The prescribed single-file `scompile.py` check passed cleanly on 2026-10-17
(sandbox 1.7 s, library 2.0 s), with no warnings or errors.

## Maintainer review fix (2026-10-17)

One proof import changed, from `import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`
to the side module `import Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`. That side module is
the import that every side citer uses, and it provides the same declarations. The published live build still
holds a full copy of these declarations under `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`,
because the shim that re-exports them has not been rebuilt yet. With the delivered import, a full (non-`module`)
importer of this item failed with "environment already contains
'AlgebraicGeometry.Scheme.etaleConstantModuleCounitIso'". Nothing else changed. The statement, helpers,
docstrings and node record are unchanged, and the module compiles cleanly.
