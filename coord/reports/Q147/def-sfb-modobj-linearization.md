## Worker report

Record the exact existing construction
`CategoryTheory.Functor.ProjectionFormula.mapModLeft` in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`, lines 259–282.
No module is supplied: the rule of one definition per notion requires reuse.
Only the item's `lean` field changes. No new nodes, dependency repairs, statement
correction, or postponed theorems are needed.

Source read: the current main-20261015 blueprint file
`blueprint/sec-proetale-coefficients/sk-def-sfb-transport/def-sfb-modobj-linearization.md`.
The node's full seven-step proof and all four statement dependencies were read,
including their recorded declarations and docstrings. The existing construction
also has exactly the declaration named by the blueprint's `lean` field. There is
no repair note for this item.

Hypotheses and clauses, matched individually:

- Monoidal categories C and D: the upstream context at lines 66–75 declares
  independent universes `v₁ v₂ u₁ u₂`, with `{C : Type u₁}`,
  `[Category.{v₁} C] [MonoidalCategory C]`, and the corresponding D assumptions.
- Strong monoidal S : D → C: `{S : D ⥤ C} [S.Monoidal]` at line 197.
- Functor P : C → D and its given projection formula π: `{P : C ⥤ D}` and
  `(pf : S.ProjectionFormula P)` in that same context. The recorded dependency
  `CategoryTheory.Functor.ProjectionFormula` has precisely `iso`, `natural_left`,
  `natural_right`, `unit`, and `assoc`. No adjunction is assumed in MapModLeft.
- Monoid B of D: `(B : D) [MonObj B]` at line 215. Under the upstream
  `CategoryTheory.Obj` scope, Mathlib's `Functor.monObjObj` gives `MonObj (S.obj B)`
  with unit `ε S ≫ S.map η[B]` and multiplication
  `Functor.LaxMonoidal.μ S B B ≫ S.map μ[B]`. These are the source's transported
  monoid operations; the strong structure identifies ε and μ with the inverses
  of the source's ε and δ. No different coefficient monoid is introduced.
- An SB-module M: `(M : C) [ModObj (S.obj B) M]` in `pf.smul` and `pf.modObj`,
  and the bundled `M : Mod C (S.obj B)` in the functor.
- The displayed action: `pf.smul B M` is definitionally
  `(pf.iso B M).inv ≫ P.map γ[S.obj B,M]` (lines 219–220). Lean's `≫` writes
  composition in diagrammatic order, exactly matching the two displayed arrows.
- This makes PM a B-module: `pf.modObj B M : ModObj B (P.obj M)` has
  `smul := pf.smul B M`, `one_smul`, and `mul_smul` (lines 230–254).
  The proofs use inverted naturality, the projection formula's unit and
  associativity, and M's module axioms, as in the node proof. Its data is explicit.
- Pf is B-linear for every SB-linear f: the `map` field of `pf.mapModLeft B`
  is `Mod.Hom.mk' (P.map f.hom)` with the required action compatibility,
  using `Mod.act_hom` and inverted naturality (lines 263–269).
- The functor P_B: the exact signature is
  `noncomputable def mapModLeft : Mod C (S.obj B) ⥤ Mod D B`.
  Its `obj` field is P on underlying objects, equipped with `pf.modObj`, and its
  `map_id` and `map_comp` fields give the functor laws (lines 261–271).
  `mapModLeft_obj_X`, `mapModLeft_map_hom`, and `mapModLeft_obj_smul` expose these
  formulas as reflexive equalities (lines 273–279).
- Commutation with the forgetful functors: `pf.mapModLeft_comp_forget B` states
  `pf.mapModLeft B ⋙ Mod.forget B = Mod.forget (S.obj B) ⋙ P`, proved by `rfl`
  at line 282. This is equality of the whole functors, including their maps.

Dependency declarations used (all reused without copies):

- `def-sfb-projection-formula`: the recorded
  `CategoryTheory.Functor.ProjectionFormula` in
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` (lines 82–99).
- `det-def-sfb-ring-object-monoid`: Mathlib's
  `CategoryTheory.MonObj`, `Mon`, `IsMonHom`, `Mon.Hom`, `Mon.id`, `Mon.comp`,
  `Mon.forget`, and `IsCommMonObj` in `Mathlib.CategoryTheory.Monoidal.Mon`.
  Their recorded full signatures and axioms were read. The present construction
  uses only `MonObj B`; it does not require B to be commutative or D braided.
- `det-def-sfb-ring-object-transport`: `CategoryTheory.Functor.mapMon` and its
  defining `Functor.monObjObj` in `Mathlib.CategoryTheory.Monoidal.Mon`.
  Its remaining clauses are supplied by `Functor.mapCommMon` and
  `Functor.isCommMonObj_obj` in `Mathlib.CategoryTheory.Monoidal.CommMon_`, and
  `Functor.mapMonNatTrans` / `Functor.mapMonNatIso` in Mon. The current node
  uses only transport of a monoid, the first clause.
- `sk-def-sfb-module-objects`: the recorded `CategoryTheory.Mod` in
  `Mathlib.CategoryTheory.Monoidal.Mod`, together with `ModObj`, `Mod.Hom`,
  `Mod.Hom.mk'`, `Mod.regular`, and `Mod.forget`. Mathlib permits a general
  monoidal action; here the canonical self-action gives exactly the dependency's
  internal modules, not a new module category. No pro-etale specialization is
  required by this generic linearization node.

Edge cases checked by reading the actual binders and construction: B may be
noncommutative, and neither ambient category needs to be braided, symmetric,
preadditive, abelian, complete, or cocomplete. P need not be monoidal, additive,
exact, or have an adjoint. Those later sections of the upstream module introduce
additional assumptions only after the declarations used here. The zero module,
when it exists, is admitted with no nonzero hypothesis. The tensor-unit monoid
and regular modules are admitted. Empty ambient categories cause no spurious
existence claim: B and each input module are supplied explicitly. Object and
morphism universes remain independent for both categories. No disputed statement
or node fault was found.

Searches made on 2026-10-21 (msearch results are retained in searches.jsonl):

- LeanFinder: “A projection formula relative to a strong monoidal functor lifts
  a functor to categories of internal left module objects over a monoid”:
  eight hits, including `Mod_.comap`, `Mod_.scalarRestriction`, `ModObj`, and
  `Functor.LeftLinear`; none is the exact projection-formula construction.
- Loogle: `"ProjectionFormula"`: zero hits.
- msearch grep: `ProjectionFormula|mapModLeft|linearization` in
  `CategoryTheory/Monoidal`: zero hits.
- LeanSearch: “Linearization of a functor with a coherent projection formula
  to internal module objects over a monoid”: eight hits, including
  `Rep.linearization` and `Functor.LeftLinear.μₗIso`; these do not define the
  generic module-object linearization in the item.
- Direct rg with `ProjectionFormula|mapModLeft|linearization` in Mathlib's
  CategoryTheory/Monoidal: zero hits. Direct rg of `lean/WeilConjectures`
  located the exact construction and its companion formulas in
  `CategoryTheory/ModuleObjects/ProjectionFormula.lean`. The blueprint-id grep
  there gave no hit; the name/concept search is what found the declaration.
- Direct rg of `lean/Sheaf` for `def mapModLeft`, this node id, and
  `linearization` found no competing definition of this construction. The
  upstream-name index likewise adds no replacement for the exact source read.

Validation: deliver2.py's prescribed dry run checks all seven existing recorded
declarations with a server compiler probe through scompile.py and runs the
maintainer's preflight. No worker proof or new Lean module is delivered.

## Second reading by Q147

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
