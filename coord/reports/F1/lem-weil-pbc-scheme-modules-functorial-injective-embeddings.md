## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeModulesFunctorialInjectiveEmbeddings` states
`AlgebraicGeometry.Scheme.Modules.exists_functorialInjectiveEmbeddings`. Its only proof is
`sorry`; it introduces no definition or auxiliary node and changes only the item's `lean` record.

Hypothesis and clause correspondence:

- A scheme X: `(X : Scheme.{u})`, without finiteness, separation, nonemptiness, or field hypotheses.
- The abelian category of O_X-modules: `X.Modules`, Mathlib's definition
  `SheafOfModules.{u} X.ringCatSheaf`; its existing Abelian instance is used unchanged.
- An endofunctor J: `∃ (J : X.Modules ⥤ X.Modules)`.
- A natural transformation from the identity: `(j : 𝟭 X.Modules ⟶ J)`. The bundled natural
  transformation includes compatibility for every module morphism.
- Every component is monic: `∀ M : X.Modules, Mono (j.app M)`.
- Every value is an injective object: `∀ M : X.Modules, Injective (J.obj M)`.
- A directed index set: `∀ (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)]`.
  No antisymmetry is required. No colimit is taken, so there is no index-size restriction;
  `v` is an explicit independent universe. No nonemptiness hypothesis excludes the empty case.
- The system and its identity/composition laws: `(F : I ⥤ X.Modules)`. The category associated
  to the preorder has the map `homOfLE h` for `h : i ≤ i'`.
- The resulting system has objects J(F_i) and maps J(phi): the composite functor `F ⋙ J`.
  Its bundled functor laws give precisely the identity and composition clauses in the node.
- Its objects are injective: `∀ i : I, Injective ((F ⋙ J).obj i)`.
- Its embedding maps are the same monomorphisms: `∀ i : I, Mono (j.app (F.obj i))`.
- Compatibility for i ≤ i': `j.app (F.obj i) ≫ (F ⋙ J).map (homOfLE h) =
  F.map (homOfLE h) ≫ j.app (F.obj i')`, where Lean writes composition in traversal order.
- The parenthetical reference to arbitrary ringed spaces identifies the generality of the
  source; the node's assertion specializes it to schemes, as does the Lean statement.

Dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Mathlib.AlgebraicGeometry.Scheme`.
  Read its full structure/docstring and the scheme morphism signature.
- `def-weil-sheaf-of-modules-category`: its `mathlib_match` is `SheafOfModules`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, with its `Hom` and category instance;
  read also `SheafOfModules.instAbelian` in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
  The imported `Mathlib.AlgebraicGeometry.Modules.Sheaf` supplies the exact specialization
  `AlgebraicGeometry.Scheme.Modules`, not a new copy of the notion.
- `def-sp-injective-resolutions`: the first clause of its match is `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, whose `factors` field expresses extension
  along every mono. Read also `CategoryTheory.InjectiveResolution` and its complete fields in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; no resolution is needed here.

Source checked: local Stacks TeX files are absent. Read the complete proof at
https://stacks.math.columbia.edu/tag/01DI and the directed-system passage at
https://stacks.math.columbia.edu/tag/01FF instead. The seven proof steps of the node, including
all cited mathematical inputs, are carried in the theorem docstring. No correction or dispute.

Edge cases checked before drafting: empty scheme (products over its points are empty products,
and its module category has only zero objects up to isomorphism); the zero sheaf (still embeds
into an injective object); empty index type (system clauses vacuous); singleton directed set;
identity transitions and arbitrary composable transitions (encoded by functor laws). The
statement requires neither additivity of J nor preservation of monomorphisms by J, neither
of which is asserted by the source. Universes u and v are explicitly declared.

Searches for an existing statement (msearch.py, group F1, this item):

- LeanFinder query: `Sheaves of modules on a scheme admit a functorial monomorphism into
  injective objects`. Eight hits, including `PresheafOfModules.injective_of_mono` (injectivity
  of component functions, not injective objects), `mono_of_injective`, sheaf mono criteria,
  and sheafification maps. No matching theorem.
- Loogle query: `SheafOfModules, CategoryTheory.Injective`. Zero hits.
- LeanSearch query: `sheaves of modules have functorial injective embeddings`. Service
  unavailable (Internal Server Error); recorded as unavailable, no search verdict.
- Mathlib grep query: `functorial|EnoughInjectives|IsGrothendieckAbelian` in
  `Algebra/Category/ModuleCat/Sheaf`. Zero hits.
- Local rg query: `functorial.*[Ii]njective|[Ii]njective.*[Ee]mbed` in both
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf`. Found general
  K-injective-complex replacements, group-ring and discrete-representation injective
  embeddings, and etale-sheaf enough-injectives statements. None is this statement about
  modules on the underlying topological space of a scheme. Read the group-algebra example.
- Local rg query: this item's full id in `WeilConjectures`. No hits.
- Name check rg: `functorialInjectiveEmbeddings|exists_functorial_injective_embeddings` in
  `dag/lean_names_upstream.json` and pinned Mathlib. No hits.

Validation: `scompile.py` compiled the 66-line module on the server in 1.6 seconds,
exit code 0, with no warnings. `deliver2.py F1
lem-weil-pbc-scheme-modules-functorial-injective-embeddings --no-push` printed
`OK (dry run)`: server compilation and preflight passed except for the independent second
reading, which the next worker writes. Nothing was pushed.

## Second reading by F1

I independently opened the sandbox node and the complete 66-line module, all three
statement-dependency nodes, and their actual Mathlib declarations. Verdict: the statement
matches the node clause by clause. No Lean or node change is needed; this reading adds only
this report section. There are no new nodes, dependency modules, or statement corrections.

The source TeX is absent from this machine's literature tree. I read the source itself from
https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex (lines 493-553,
label lemma-sheaves-modules-space) and cohomology.tex (lines 3210-3245), and checked the
rendered tags https://stacks.math.columbia.edu/tag/01DI and
https://stacks.math.columbia.edu/tag/01FF. The former assumes only a ringed space; the latter's
quasi-compact-basis and intersection assumptions concern its cohomology/colimit theorem,
not the injective-embedding passage invoked here. The node specializes 01DI to schemes;
its parenthetical reference to ringed spaces does not assert a second quantified theorem.

Objects, hypotheses, and conclusion clauses, listed independently from the node:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary scheme X | `(X : Scheme.{u})` | Exact; no extra geometric hypothesis. |
| Abelian category of O_X-modules on the underlying space | `X.Modules` | Exact specialization of the recorded `SheafOfModules`, not etale sheaves. |
| One endofunctor J | `∃ (J : X.Modules ⥤ X.Modules)` | Exact; functor laws are bundled. |
| Natural transformation from identity to J | `(j : 𝟭 X.Modules ⟶ J)` | Exact; naturality for every module morphism is bundled. |
| Every embedding is mono | `∀ M : X.Modules, Mono (j.app M)` | Exact categorical monomorphism. |
| Every value is injective in this category | `∀ M : X.Modules, Injective (J.obj M)` | Exact extension property, not injectivity of a function. |
| A directed index set I | `∀ (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)]` | Covers all directed sets; preorders also work by the same functor laws. |
| A system with identity and composition transition laws | `(F : I ⥤ X.Modules)` | Exact: preorder arrows encode inequalities and the bundled functor laws encode both laws. |
| The resulting objects are precisely J(F_i) | `(F ⋙ J).obj i` | Exact, definitionally `J.obj (F.obj i)`. |
| The resulting transitions are precisely J(phi) and form a system | `(F ⋙ J).map (homOfLE h)` | Exact; composite functor laws give identity and composition. |
| Every resulting object is injective | `∀ i : I, Injective ((F ⋙ J).obj i)` | Exact. |
| Embeddings in the system are the same monomorphisms | `∀ i : I, Mono (j.app (F.obj i))` | Exact. |
| Compatibility for every i ≤ i' | `∀ (i i' : I) (h : i ≤ i'), j.app (F.obj i) ≫ (F ⋙ J).map (homOfLE h) = F.map (homOfLE h) ≫ j.app (F.obj i')` | Exact; Lean composition is in traversal order. |
| Quantifier order | X, then J and j, then all modules and all directed systems | Exact: one choice serves every system, rather than a separate choice per system. |

Dependency checks: `Scheme` in Mathlib.AlgebraicGeometry.Scheme is a locally ringed
space with affine neighbourhoods, with no nonemptiness or finiteness premise. In
Mathlib.AlgebraicGeometry.Modules.Presheaf, `ringCatSheaf` is the underlying structure
sheaf with its commutative rings forgotten to rings. In Modules.Sheaf, `Modules` is
`SheafOfModules.{u} X.ringCatSheaf`, with module-sheaf morphisms and the existing abelian
instance. I read SheafOfModules, its Hom and category instance in ModuleCat/Sheaf.lean,
and the abelian instance in Sheaf/Abelian.lean; no sheafification hypothesis is added to
this theorem because the scheme specialization supplies it. I read Injective.factors in
Preadditive/Injective/Basic.lean: every map into the object extends along every mono,
exactly clause one of def-sp-injective-resolutions. InjectiveResolution in Resolution.lean
serves the dependency's other clause and is not an object used in this statement.

Edge cases: empty schemes are allowed by the Scheme binder; no point is chosen. The zero
module is included in the universal M binder. Empty index types are not excluded: directedness
is pairwise and the system's conclusions are vacuous. Singleton indices, identity transitions,
and all composable transitions are covered by F's functor laws. There is no degree n,
characteristic, field, Noetherian, quasi-coherence, or separation restriction. Universes u and v
are explicitly bound. Modules have the standard same-universe scheme encoding, with u arbitrary;
v is independent and can be larger or smaller, since this statement takes no indexed limit or
colimit. The directed-preorder and empty-index clauses are consequences of the already asserted
universal natural transformation, so they impose no stronger existence requirement.

Independent searches, using different queries from the first writer:

- LeanFinder via msearch: `natural embedding of sheaves of modules into injective sheaves`.
  Eight hits: sheafification, locally injective sheafification maps, presheaf mono/component
  criteria, forgetful functors, and Module.injective_object_of_injective_module. None gives
  the node's endofunctor and natural transformation for scheme modules.
- Loogle via msearch: `CategoryTheory.Injective, CategoryTheory.NatTrans`: zero hits.
- LeanSearch via msearch: `there exists an endofunctor of sheaves of modules and a natural
  monomorphism from identity with injective values`: service unavailable, Internal Server
  Error; no negative search verdict inferred from that failure.
- rg in pinned Mathlib, WeilConjectures, and repository lean/Sheaf for natural/functorial
  injective embeddings and presentations. I opened AdjunctionTransferFunctorialInjectives,
  EtaleModuleEnoughInjectives, and the signature of FunctorialInjectiveComplexEmbedding:
  these respectively transfer given embeddings, assert enough injectives on the etale site,
  and give quasi-isomorphic complex embeddings through injective subobjects; none states
  this node. Pinned Mathlib's GrothendieckCategory/EnoughInjectives has functorial
  factorization data, but not this scheme statement with its system clause. Its instance
  needs a Grothendieck category and must be specialized/assembled to obtain this statement.
- Full-name rg of `exists_functorialInjectiveEmbeddings` in dag/lean_names_upstream.json,
  WeilConjectures, and repository lean/Sheaf found no existing declaration.

H5-H9: there are no definitions or hollow data; the only theorem has exactly `by sorry`.
The module and theorem docstrings name 01DI, 01FF and this blueprint id. The theorem docstring
carries all seven node proof steps: stalk embeddings, skyscraper injectivity, their product,
functoriality, monicity by germs, naturality, and the directed-system conclusion, with the
corresponding dependency ids. Imports serve module sheaves, injective objects and preorder
categories. All Lean lines fit 100 characters. The namespace has no Sheaf prefix. All variables
and universes are bound. The node's lean.statement equals the theorem signature verbatim.

Validation: scompile.py with the absolute sandbox module path compiled the module remotely
in 1.6 seconds, exit code 0, with no warnings. An initial relative-path invocation from the
read-only repository could not locate the sandbox file; it was immediately rerun with the
absolute path. No mathematical mismatch or tooling defect remains.
