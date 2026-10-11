## Worker report

The module `Sheaf.AlgebraicGeometry.FlatModuleDescent` states
`AlgebraicGeometry.exists_eventually_isFlatOver_of_limit`, with its sole proof `sorry`.
Relative flatness reuses the existing affine-local definition in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage`. No result is proved.

Hypothesis and conclusion correspondence:

- The directed set is `{I : Type v} [PartialOrder I] [IsDirectedOrder I]`.
  Fixing `i : I` supplies nonemptiness without adding a separate assumption.
- The rings and their forward transition maps are `R : I ⥤ CommRingCat.{u}`.
  The scheme inverse system is `R.op ⋙ Scheme.Spec`, with objects `Spec (R.obj k)`.
  All these schemes are affine, hence quasi-compact and quasi-separated, and their
  transitions are affine. Thus these clauses of the node hold by the objects' construction,
  rather than extra binders. The given Noetherian hypothesis is retained verbatim as
  `[∀ k : I, IsNoetherianRing (R.obj k)]`, although the source proof does not need it.
- `c : Cone (R.op ⋙ Scheme.Spec)` and `hc : IsLimit c` give the inverse limit and its
  projections. `[IsAffine c.pt]` says precisely that this limit is isomorphic to a spectrum
  of a commutative ring, as required by the node's `S = Spec R`. The choice of the ring and
  spectrum isomorphism is immaterial to the statement and is not fixed. No Noetherian
  condition on the limit is imposed.
- `f : Xi ⟶ Spec (R.obj i)` is the chosen stage scheme over its base.
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]` is exactly the
  definition of a morphism of finite presentation in the convention dependency.
- `M : Xi.Modules` and `[M.IsFinitePresentation] [M.IsQuasicoherent]` encode the finitely
  presented quasi-coherent structure module, using Mathlib's local finite presentation.
  The latter class follows from the former, but is included to display both node clauses.
- `pullback f (c.π.app (op i))` is `X = Xi ×_{Si} S`, with projections `pullback.fst`
  and `pullback.snd`. `tensorPullback` along the first projection gives the module
  pullback; `hflat` asserts its `IsFlatOver` along the second projection.
- `∃ j : I, ∃ hij : i ≤ j` gives a sufficiently late stage.
  `∀ (k : I) (hjk : j ≤ k)` includes EVERY later stage, including `k = j`.
  `Spec.map (R.map (homOfLE (hij.trans hjk)))` is the transition `S_k → S_i`.
  The conclusion uses its fibre product, the pulled-back module, and flatness over
  `S_k` through the second projection. It does not merely assert flatness at one stage.

Dependency declarations inspected and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; full structure signatures and docstrings read.
- `def-pc-morphism-conventions` has an intentional convention record with no declaration.
  Its note directs citers to Mathlib's named classes. Here the classes are
  `AlgebraicGeometry.LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`,
  from `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` and its imports.
  Morphism flatness alone would not express this node's module flatness.
- `def-pc-base-change`: `Sheaf.AlgebraicGeometry.BaseChangeConventions` inspected in full.
  The node's note expressly directs scheme-base-change citers to `Limits.pullback`,
  `pullback.fst`, and `pullback.snd`. Its recorded `moduleBaseChange` is for an already
  base-changed module under a morphism of objects over the base; this theorem starts with
  `M` on `Xi`, so it uses the underlying recorded `tensorPullback` from
  `Sheaf.AlgebraicGeometry.TensorPullback` (imported by BaseChangeConventions).
- Added `def-pc-scheme-module-flat-over`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`,
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage`.
- Finite-presentation and quasi-coherence classes reuse
  `SheafOfModules.IsFinitePresentation` and `SheafOfModules.IsQuasicoherent`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` (full definitions read).
  Finite presentation already has the DAG leaf
  `def-weil-pbc-module-finite-type-presentation`; it is not redefined.
- The existing predicate's full signature is `def IsFlatOver (ℱ : X.Modules)
  (f : X ⟶ T) : Prop`; its full docstring and body were read at DirectImage.lean:186–197.
  It quantifies over all affine opens in the source and base with source image inside
  the base open, equips sections with `Module.compHom` along `f.appLE`, and asks for
  `Module.Flat` over the base section ring. Tag 01U4 identifies this condition with
  stalkwise relative flatness for quasi-coherent modules, which are precisely the
  modules in this theorem. Its arguments are module first, morphism second.


Edge cases checked: empty source and zero module give vacuous/zero stalk flatness;
no nonempty-source or nonzero-module hypothesis appears. Empty index sets are already
excluded by the node's fixed `i`, exactly as in Lean. Singleton systems and stationary
systems are allowed. The conclusion includes the boundary `k = j`. Zero rings and empty
spectra are allowed; Noetherian includes the zero ring. No characteristic, separatedness
of the morphism, or flatness of transition maps is assumed. Index and scheme universes
are independent. The limit ring need not be Noetherian.

Sources: the local Stacks checkout is absent on this machine. Read the official pages
https://stacks.math.columbia.edu/tag/05LY,
https://stacks.math.columbia.edu/tag/01U4, and
https://stacks.math.columbia.edu/tag/01U3. Tag 05LY with its target equal to the base gives
one stage; flat base change gives all later stages, as the node already states. No
statement correction or disputed statement is needed.

Searches (also logged by msearch.py in sandbox searches.jsonl):

- LeanFinder, “eventual flatness of finitely presented quasi coherent module over inverse
  limit of schemes”: eight hits, including the finite-presentation sheaf classes and
  AdicCompletion.flat_of_isNoetherian; no scheme-module descent theorem.
- Loogle, “Module.Flat, SheafOfModules.IsFinitePresentation”: zero hits.
- Mathlib grep, “FlatOver|IsFlat|eventually.*flat”, AlgebraicGeometry: zero hits.
- LeanSearch, “sheaf of modules flat over morphism stalk modules”: unavailable,
  Internal Server Error, recorded without a mathematical verdict.
- LeanFinder, “flat sheaf of modules over scheme morphism all stalks flat over base local
  ring”: eight hits, all concerning flat morphisms or flat ring maps, not arbitrary modules.
- Initial rg restricted to source and project modules directories for relative flatness,
  eventual flatness and flat descent found affine module descent and flat pullback results.
  The final source-wide IsFlatOver search found the existing predicate in Cohomology,
  and the final implementation reuses it. The affine theorem concerns rings and one affine chart, not this statement.
- rg for this item id in WeilConjectures found no declaration. The upstream-name lookup
  has no declaration attached to this item.
- DAG definition searches and `tools/blueprint_refs.py search 'flat module'` found no
  relative module-flatness definition node. `def-pc-flat-sheaf-modules` is tensor exactness
  over the structure sheaf on one ringed site; it is not flatness over a base morphism.

The final server compile checks the single theorem module with the existing definition
imported. The duplicate draft definition has been removed. The preflight found the
existing name in the source audit; a repository-wide search then located DirectImage.lean,
which the earlier modules-directory search had missed. The final declaration uses this
existing definition. All binders and universes are explicit.

## New nodes

`def-pc-scheme-module-flat-over` records the EXISTING declaration
`AlgebraicGeometry.Scheme.Modules.IsFlatOver` in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage`, branch slopmaster2, with
`existing: true` and no Lean module in the delivery. No existing DAG definition node
carried this relative notion. Its statement gives the affine-local flatness condition
and the equivalent stalk condition, following Stacks Tags 01U3 and 01U4. The source
signature, docstring and body match the affine-local clause exactly; the equivalence
is applied only to quasi-coherent modules. The searches recorded on the new node include
the initial unavailable LeanSearch call, LeanFinder, Loogle, Mathlib grep, DAG search,
source and Sheaf grep, and the final repository-wide `IsFlatOver` search that found the
existing definition. `def-pc-flat-sheaf-modules` concerns tensor exactness on one ringed
site and `def-weil-flat-morphism` concerns the structure ring, so neither carries this
relative module notion. The item cites the new node. No new definition is implemented.

## Second reading by F1

Independent reading: the node and FlatModuleDescent.lean were open together. The
statement is faithful; no Lean signature or node statement was changed. The only
repair is in proof-docstring step 2: the common upper bound now explicitly includes
`i`, and the empty affine cover takes `i`. This closes the empty-source corner of
that proof description without changing the theorem.

Object, hypothesis and conclusion checklist (H3):

1. Directed set `I`: `{I : Type v} [PartialOrder I] [IsDirectedOrder I]`.
   A directed set is a partially ordered set here, not a totally ordered set.
   Verdict: exact. The fixed `(i : I)` supplies the source's nonemptiness.
2. Inverse system with stages `S_k = Spec R_k`: `(R : I ⥤ CommRingCat.{u})`
   and `R.op ⋙ Scheme.Spec`. For `i ≤ k`, `R.map (homOfLE ...)` runs from
   `R_i` to `R_k`; `Spec.map` runs from `S_k` to `S_i`. Verdict: exact variance
   and coherence. Spectra are qcqs and every morphism between these affine schemes
   is affine, so the qcqs and affine-transition clauses are present by construction.
3. Noetherian stage rings: `[∀ k : I, IsNoetherianRing (R.obj k)]`.
   Verdict: exact, including stages before `i`. No Noetherian limit-ring assumption.
4. Affine inverse limit `S`: `(c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c)`
   and `[IsAffine c.pt]`. The limit projections are `c.π.app (op i)`.
   Verdict: exact; writing an affine scheme rather than choosing its spectrum
   isomorphism does not restrict the object or its projections.
5. Fixed stage and finitely presented scheme over it: `(i : I) {Xi : Scheme.{u}}`
   and `(f : Xi ⟶ Spec (R.obj i))`, with `[LocallyOfFinitePresentation f]`,
   `[QuasiCompact f]`, `[QuasiSeparated f]`. Verdict: exact finite presentation,
   as explicitly defined by def-pc-morphism-conventions; separatedness is not assumed.
6. Finitely presented quasi-coherent structure module: `(M : Xi.Modules)` with
   `[M.IsFinitePresentation] [M.IsQuasicoherent]`. Verdict: exact; finite presentation
   already implies quasi-coherence in Mathlib, so the displayed second instance
   adds no extra hypothesis. It is local finite presentation, not finite global sections.
7. Limit source and pulled-back module: `pullback f (c.π.app (op i))`, with
   `tensorPullback` along `pullback.fst` applied to `M`. Verdict: exact fibre product
   and tensor module pullback, not the sectionwise functor `Modules.pullback`.
8. Limit flatness over `S`: `hflat` is `Scheme.Modules.IsFlatOver` of that module
   along `pullback.snd`. Verdict: exact relative module flatness; it does not assume
   that the source morphism itself is flat.
9. Sufficiently late stage: `∃ j : I, ∃ hij : i ≤ j`. Verdict: exact existential
   ordering; the witness is at or after the fixed stage.
10. EVERY later stage: `∀ (k : I) (hjk : j ≤ k)`, with transition
    `Spec.map (R.map (homOfLE (hij.trans hjk)))`, the fibre product against `f`,
    `tensorPullback` along its first projection, and `IsFlatOver` along its second
    projection. Verdict: exact, including `k = j`; the base is `S_k`, not `S_i`.

Source reading: the repository has no Stacks .tex checkout. I obtained the official
Stacks master limits.tex and morphisms.tex into this item's scratchpad and read
`lemma-descend-finite-presentation` (standing assumptions),
`lemma-descend-module-flat-finite-presentation` (05LY), `definition-flat` (01U3),
and `lemma-flat-module-characterize` (01U4). I also checked the official rendered
pages https://stacks.math.columbia.edu/tag/05LY,
https://stacks.math.columbia.edu/tag/01U3 and
https://stacks.math.columbia.edu/tag/01U4. The inherited assumptions are directedness,
affine transitions and qcqs stages. Setting the target `Y_i = S_i` specializes
05LY exactly to this node; base change preserves relative flatness and therefore
supplies all later stages. The node explicitly adds Noetherian stage rings and
retains them in Lean; this is not a correction of the source to make it easier.

Dependency reading (H4/H13): read def-pc-scheme and Scheme.lean's `Scheme` and
`Scheme.Hom`; def-pc-morphism-conventions and its convention record, together with
FinitePresentation.lean's `LocallyOfFinitePresentation`; def-pc-base-change and
BaseChangeConventions.lean, including `moduleBaseChange` and its note authorizing
`Limits.pullback` for scheme base change. Read TensorPullback.lean's concrete
`tensorPullbackObj`, `tensorPullbackMap` and `tensorPullback` definitions. Its named
sorry theorems provide only proof fields, not missing data. Read the finite-module
presentation leaf def-weil-pbc-module-finite-type-presentation and the actual
`SheafOfModules.IsFinitePresentation` and `IsQuasicoherent` classes in
Quasicoherent.lean: these are finite local presentations and local quasi-coherent
data. Read `Scheme.Modules` in Modules/Sheaf.lean and `SheafOfModules` itself.
No unusable dependency or additional dependency module was found.

New-node reading (H12): def-pc-scheme-module-flat-over records an existing predicate,
not an implementation. I read DirectImage.lean:186–197, including the universe and
scheme variables at 147–153. `IsFlatOver` quantifies over precisely the affine pairs
in the node, with `e : U.1 ≤ f ⁻¹ᵁ V.1`, and uses `Module.compHom` along `f.appLE`.
The predicate accepts arbitrary modules, but this node defines its restriction to
quasi-coherent modules, on which 01U4 gives exactly the stated stalk equivalence.
Both original and pulled-back modules in our theorem are quasi-coherent (tensor
pullback preserves quasi-coherence). The unrestricted upstream docstring's equivalence
is not being used outside that restriction. The new node's two cited prerequisites,
source, empty proof fields, searches, created record, chapter/unit, audit records,
existing Lean record and ancestor were inspected. `blueprint_refs.py ancestor` gives
lem-pc-rf-perfect-base-change, matching its provenance. A parsed search of every
existing definition node's `lean` record found no node recording `IsFlatOver`.
The other flatness nodes describe flat morphisms or tensor exactness on one structure
sheaf, not flatness of a module over a base scheme. No duplicate definition is delivered.

Edge cases: the empty index type has no fixed `i`, exactly as in the node. Singleton
and stationary systems are allowed. An empty source has an empty affine cover, and
one may take `j = i`; this is now explicit in the proof docstring. The zero module
and zero rings (empty spectra) are allowed, as are non-Noetherian limit rings.
The boundary `k = j` uses the reflexive inequality. Finite presentation allows zero
generators and zero relations. No characteristic, field, nonzero-ring or transition
flatness assumption appears. The two universe parameters are explicit and independent:
`v` for indices, `u` for all scheme/ring data; a common larger universe accommodates
any chosen collection. `Xi.Modules` is Mathlib's standard scheme-module universe;
finite local presentations can be represented there. There is no countability or
finite-index restriction. All variables in the signature are bound.

Independent searches, with wording different from the first reader's:

- LeanFinder via msearch: "quasi coherent finitely presented sheaf flat after inverse
  limit descends to some stage". Results concern sheaf finite-presentation classes
  and their consequences, not this eventual scheme-module theorem.
- Loogle via msearch: `"IsFlatOver"`: zero Mathlib hits.
- LeanSearch via msearch: "flatness of a quasi coherent finitely presented module
  descends along an inverse system of affine schemes": service unavailable (Internal
  Server Error), logged as unavailable, not as evidence of absence.
- rg on all WeilConjectures, project's lean/Sheaf and Mathlib/AlgebraicGeometry for
  `IsFlatOver`, descent/flatness in either order, and eventual flatness. This finds
  the existing relative predicate in DirectImage.lean, whose body was checked, and
  fpqc descent statements about morphism properties, which are different statements.
- rg for flatness with limits/colimits and existential flatness in source Modules,
  project AlgebraicGeometry and Mathlib/RingTheory/Flat. Opened
  `AlgebraicGeometry.exists_eventually_flat_of_finitePresentation` in
  AffineFlatModuleDescent.lean: it states affine algebra/module descent, not our theorem
  for an arbitrary finitely presented source scheme. It is the proof dependency,
  not an existing exact statement for this item.
- rg in dag/lean_names_upstream.json for this item and `IsFlatOver`, and parsed search
  of DAG definition-node Lean records: no existing node carrying the relative predicate
  and no upstream declaration assigned to this theorem.

H5/H6/H8/H9: the delivery has no new Lean definitions, only one named theorem with
`by sorry`. Its module and declaration docstrings name 05LY and this blueprint id;
the three proof steps match the node's affine cover, affine descent/common bound,
and gluing argument. Imports supply the displayed notions or the recorded dependency.
No declaration has a Sheaf namespace prefix; all lines are at most 100 characters.
The node's lean.statement remains verbatim equal to the unchanged theorem signature.
The first independent server compile completed cleanly in 3.3 seconds; final
compilation and preflight are also run by deliver2.py before any push.
