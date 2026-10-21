## Worker report

Recorded an exact existing declaration; no Lean module is added:
`CategoryTheory.Adjunction.mapModLeftAdjunction` in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`, source lines 535–550.
Its signature verbatim is
`noncomputable def mapModLeftAdjunction : adj.mapModLeft B ⊣ S.mapMod B`.
The source was read locally and confirmed against the live server with
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`.
The only changed node field is `lean`. No new definition, theorem, sorry, or node is introduced.

Source comparison: read the item's full node and its source markdown at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/` 
`sk-def-sfb-transport/def-sfb-modobj-linearization-transport-adjunction.md`, and clause 4
of that unit's `_section.md`. Both specify exactly this upstream declaration, including
the original underlying adjoint map. There is no statement correction or disputed claim.

Hypotheses and clauses, with their Lean renderings:

- The ambient monoidal categories are `{C : Type u₁} [Category.{v₁} C]
  [MonoidalCategory C]` and `{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]`
  in the enclosing section (lines 71–80). The four universe variables are independent.
- The adjunction is `{P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S)` (line 499).
- Strong monoidality of S is `[S.Monoidal]`; this supplies the lax monoidal structure
  used by the transport functor, without assuming P monoidal.
- The canonical adjunction satisfies the projection formula by
  `[adj.HasProjectionFormula]` (line 499). This is the dependency's exact class,
  requiring invertibility of `adj.projectionFormulaMap L M` for every L and M;
  that map is the inverse adjoint of `S.obj L ◁ adj.unit.app M ≫
  Functor.LaxMonoidal.μ S L (P.obj M)` (lines 118–120, 182–193).
- The coefficient object is `(B : D) [MonObj B]` (line 500); `variable {B}`
  (line 519) makes it implicit at the recorded declaration. There is no commutativity
  hypothesis.
- The specified left linearization is `adj.mapModLeft B`. This is the abbreviation
  defined at line 504 as `adj.projectionFormula.mapModLeft B`, so it uses exactly the
  canonical projection formula of `def-sfb-adjunction-projection-formula`, rather than
  an arbitrary projection-formula datum. Its source is `Mod C (S.obj B)` and its
  target is `Mod D B`. The action is the inverse projection formula followed by
  P of the original action, as specified by `def-sfb-modobj-linearization`.
- The right functor is exactly `S.mapMod B : Mod D B ⥤ Mod C (S.obj B)`, the
  dependency's transport, with action `Functor.LaxMonoidal.μ S B N.X ≫ S.map γ[B,N.X]`.
- Left adjointness is the actual adjunction datum `adj.mapModLeft B ⊣ S.mapMod B`;
  `Adjunction.mkOfHomEquiv` supplies its naturality from the original adjunction.
- The final correspondence clause is present in the definition's data: its `toFun φ`
  is `Mod.Hom.mk' (adj.homEquiv M.X N.X φ.hom) ...`, and `invFun ψ` has underlying map
  `(adj.homEquiv M.X N.X).symm ψ.hom`. The proof used to construct each linear
  morphism is `adj.projectionFormulaSMul_comp_eq_iff M N ...` (lines 524–532).
  Thus the bijection is precisely restriction of the original adjunction's bijection.

Dependency declarations read with full signatures, docstrings, and constructions:

- `def-sfb-adjunction-projection-formula`: `CategoryTheory.Adjunction.projectionFormula`,
  in `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`, lines 187–197.
  It constructs the coherent projection formula from the canonical adjunction maps.
- `def-sfb-modobj-linearization`:
  `CategoryTheory.Functor.ProjectionFormula.mapModLeft` and its action/forgetful
  declarations in the same module, lines 215–282. These are exactly the functor
  used by `CategoryTheory.Adjunction.mapModLeft`.
- `def-sfb-modobj-transport`: `CategoryTheory.Functor.mapMod`,
  `CategoryTheory.Functor.modObjObj`, and `CategoryTheory.Functor.act_mapMod_obj`,
  in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`, lines 141–172 and 199–201.
  Its lean record currently gives a declarations list; the closed slopmaster2 audit
  supplies the module and exact names. This is a usable existing dependency.
- `def-sfb-adjunction-has-projection-formula`:
  `CategoryTheory.Adjunction.HasProjectionFormula`, in the ProjectionFormula module,
  lines 180–185, together with the defining mate `projectionFormulaMap` at lines 118–120.

Also read the proof-dependency interfaces `Functor.ProjectionFormula.mapModRight`
and `Functor.ProjectionFormula.mapModAdjunction`, and the specialized mate computation
`Adjunction.projectionFormula_theta`, all in the same module. The general-adjunction
node currently has no lean record, but the requested specialization already exists in
full, so no missing declaration is needed and no dependency record is changed.

Edge cases checked before recording the declaration: arbitrary noncommutative monoid
objects are allowed; there are no additive, abelian, symmetry, exactness, closedness,
nonzero-object, finiteness, or nonempty-category assumptions. Object and morphism
universes of C and D are independent, so there is no smallness specialization. The
identity adjunction and coefficient monoidal unit are admitted. When zero module
objects exist they are included without restriction. The typed module categories
have the displayed source and target; the right-to-left arrow in the node's
adjunction notation denotes the right adjoint and is correctly implemented.

Searches actually run:

- `msearch.py ... leanfinder` with query "An adjunction with strong monoidal right
  adjoint satisfying the projection formula lifts to module objects, with right adjoint
  transport along the monoidal functor": eight hits, including `Adjunction.mapMon`,
  `ModuleCat.adj`, and ordinary scalar restriction results; none is the exact module-object
  projection-formula adjunction.
- `msearch.py ... loogle` with query `CategoryTheory.Adjunction, CategoryTheory.Mod_`:
  zero hits.
- `msearch.py ... grep` with query
  `mapModLeftAdjunction|mapModAdjunction|ProjectionFormula` in Mathlib CategoryTheory:
  zero hits.
- `rg -n 'mapModLeftAdjunction|mapMod.*Adjunction|mapModLeft.*adj|linearization.transport'`
  on `lean/WeilConjectures` and `lean/Sheaf`: found this exact construction at upstream
  ProjectionFormula.lean:538 and many downstream users. Opened and read the construction.
- `rg -n 'def-sfb-modobj-linearization-transport-adjunction' lean/WeilConjectures`:
  no node-id annotation found; this does not affect the declaration's exact match.
- `rg -n 'mapModLeftAdjunction' dag/lean_names_upstream.json`: no indexed hit;
  the local and live source declarations establish the match directly.

Validation: this is an `existing: true` record with no delivered Lean file, as required
by brief-stage2 §1. No duplicate module is compiled or delivered. The prescribed
`deliver2.py --no-push` performs the server-side preflight for the existing attachment.

## Second reading by NZ

Worker reread against the open node, source markdown, and upstream definition;
the maintainer supplies the independent delivery review, and no other agent was started.
Checked the context at lines 71–80 and 499–500, the implicit coefficient binder at 519,
and the actual `mapModLeftAdjunction` construction at 538–550. The source requires
P left adjoint to strong monoidal S, invertibility of the canonical projection maps,
and a monoid B; those are exactly the binders listed above. The left side unfolds to
the recorded linearization with the canonical projection formula, and the right side
is the recorded transport functor. Inspected both directions of `homEquiv`: they use
the original adjoint maps on underlying morphisms and enforce precisely the required
module linearities. No hypothesis or clause is missing, no new assumption is introduced,
and no correction was necessary. The new lean record changes no mathematical statement.
