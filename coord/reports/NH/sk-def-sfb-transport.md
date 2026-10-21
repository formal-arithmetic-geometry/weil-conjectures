## Worker report

Recorded an existing binding for the entire four-part definition; no Lean module is added.
The primary declaration is `CategoryTheory.Functor.ProjectionFormula` in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`. The record's
`declarations` includes all nine constructions named by the blueprint, together with the
canonical actions, unit monoid morphism, forgetful identities, and mate identity needed to
read all clauses literally. Its `statement` is the primary structure signature verbatim.
The `slopmaster2` branch label follows the existing WeilConjectures binding convention.
Only the item's `lean` field changes.

Source read: current blueprint
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-transport/_section.md`,
all four numbered paragraphs, and the item's seven-step proof. Read all twelve statement
dependency nodes, their recorded declarations, signatures, enclosing contexts and docstrings.
The current live server sources of `ProjectionFormula` and `MapMod` were also read using
`scompile.py --source`; they agree with the local sources inspected. No repair note for this
item exists in `coord/repair-notes`.

Hypotheses common to all clauses: the source has independent universes `u₁`, `u₂`, `v₁`,
`v₂`, with `{C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]` and
`{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]`. No symmetry, commutativity,
additivity, abelianness, closedness, existence of limits, or equality of universes is
assumed by the recorded constructions. These hypotheses occur in other sections of the
same files but do not occur in these definitions' contexts.

Clause 1, every hypothesis and assertion:

- `F : C ⥤ D` with `[F.LaxMonoidal]` is precisely the given lax monoidal functor;
  `(R : C) [MonObj R]` is the arbitrary monoid object. Mathlib's scoped instance
  `Functor.monObjObj` supplies `MonObj (F.obj R)`. In
  `Mathlib.CategoryTheory.Monoidal.Mon:826–847`, its `one` is
  `Functor.LaxMonoidal.ε F ≫ F.map MonObj.one` and its `mul` is
  `Functor.LaxMonoidal.μ F R R ≫ F.map MonObj.mul`. Thus it is the transported monoid,
  rather than an arbitrary structure on the same underlying object.
- In `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod:145–172`, `Functor.modObjObj`
  takes `(X : C) [ModObj R X]` to a module over `F.obj R` with action
  `Functor.LaxMonoidal.μ F R X ≫ F.map (Mod.act X)`. `Functor.mapMod` bundles these
  objects as `Mod C R ⥤ Mod D (F.obj R)` and maps a module morphism `f` through
  `F.map f.hom`. The construction includes its linearity and functor laws.
  `Functor.act_mapMod_obj` at 199–201 gives the action as an equality.
- `Functor.mapMod_comp_forget`, in `MapMod:76–77`, is the exact equality
  `F.mapMod R ⋙ Mod.forget (F.obj R) = Mod.forget R ⋙ F`.

Clause 2, every hypothesis and assertion:

- `MapMod:201–286` binds `{F : C ⥤ D} {G : D ⥤ C}`, `(adj : F ⊣ G)`,
  `[F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]`, and `(R : C) [MonObj R]`.
  `F.Monoidal` is strong monoidality; `adj.IsMonoidal` is the compatibility of the
  adjunction and the structures (the mate condition). It is not an unrelated
  monoidality assumption on an otherwise arbitrary adjunction.
- `Adjunction.unitAlgHom adj R` is literally `adj.unit.app R` with target
  `G.obj (F.obj R)`. `Adjunction.isMonHom_unitAlgHom` uses the twice-transported
  monoid structure; no extra algebra morphism is chosen.
- `Adjunction.mapModAdjunction` has type
  `F.mapMod R ⊣ G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)`.
  Lean composes functors left to right, so the right side is exactly transport by
  `G` followed by restriction along the unit, as in the node. Its `homEquiv`
  uses `adj.homEquiv M.X N.X` and its inverse on the underlying morphisms,
  restricted by the two module-linearity lemmas. No alternative adjunction is used.

Clause 3, every hypothesis and assertion:

- `ProjectionFormula:76–98` binds `(S : D ⥤ C) [S.Monoidal] (P : C ⥤ D)`.
  `Functor.ProjectionFormula` has precisely the fields `iso`, `natural_left`,
  `natural_right`, `unit`, and `assoc`. Its `iso L M` is
  `P.obj (S.obj L ⊗ M) ≅ L ⊗ P.obj M` for every `L : D`, `M : C`.
  The unit field uses the inverse unit structure `Functor.OplaxMonoidal.η S`, and
  the associativity field uses `Functor.OplaxMonoidal.δ S`; these are the exact
  coherent unit/associativity constraints of the source.
- For `pf : S.ProjectionFormula P` and `(B : D) [MonObj B]`, `pf.smul B M` is
  `(pf.iso B M).inv ≫ P.map γ[S.obj B,M]`. The domain of `mapModLeft` is modules
  over `S.obj B` with its transported monoid structure. `pf.modObj` provides the
  module laws, and `pf.mapModLeft B : Mod C (S.obj B) ⥤ Mod D B` sends `M.X` to
  `P.obj M.X` and `f.hom` to `P.map f.hom` (`ProjectionFormula:215–282`).
  `mapModLeft_comp_forget` is the equality of the forgetful composites.
- For an arbitrary specified right adjoint `{G : D ⥤ C}` and `(adj : P ⊣ G)`,
  `pf.theta adj L N` is
  `adj.homEquiv _ _ ((pf.iso L (G.obj N)).hom ≫ L ◁ adj.counit.app N)`.
  Thus the mate uses exactly the counit described in the proof. `pf.rightSMul adj B N`
  is `pf.theta adj B N ≫ G.map γ[B,N]`. `pf.rightModObj` supplies the laws, and
  `pf.mapModRight adj B : Mod D B ⥤ Mod C (S.obj B)` sends underlying objects/maps
  through `G`. See `ProjectionFormula:333–450`.
- `pf.mapModAdjunction adj (B := B)` is an actual adjunction
  `pf.mapModLeft B ⊣ pf.mapModRight adj B` (`ProjectionFormula:456–487`). Its
  underlying Hom bijection is the given `adj.homEquiv`; `smul_comp_eq_iff` says
  exactly that this bijection restricts to linear maps. No monoidal structure on
  the arbitrary right adjoint `G` is required.

Clause 4, every hypothesis and assertion:

- For `(adj : P ⊣ S) [S.Monoidal]`, `Adjunction.projectionFormulaMap adj L M`
  (`ProjectionFormula:109–113`) is exactly
  `(adj.homEquiv _ _).symm
    (S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M))`.
  This is the canonical map specified in the node, including its orientation.
- `Adjunction.HasProjectionFormula` (`ProjectionFormula:173–179`) requires
  `IsIso (adj.projectionFormulaMap L M)` for every `L` and `M`. This is the
  two-sided-invertibility condition, not an arbitrary family of chosen maps.
  Under this assumption, `adj.projectionFormula` at 184–189 uses `asIso` of these
  exact maps and their naturality, unit and associativity theorems.
- `Adjunction.projectionFormula_theta` (`ProjectionFormula:509–516`) states
  `adj.projectionFormula.theta adj L N = Functor.LaxMonoidal.μ S L N`.
  Substitution in `rightSMul` identifies its action with the `S.mapMod B` action;
  both functors send objects to `S.obj N.X` and maps to `S.map f.hom`.
  This is the asserted equality of the right linearization and transport,
  not an assertion about an arbitrary unrelated projection formula on `P`.
- `Adjunction.mapModLeft` is the abbreviation
  `adj.projectionFormula.mapModLeft B`. `Adjunction.mapModLeftAdjunction`
  (`ProjectionFormula:535–550`) has precisely type
  `adj.mapModLeft B ⊣ S.mapMod B`; its Hom bijection again uses the original
  `adj.homEquiv` on underlying maps.

Dependency declarations used, by recorded module:

- `sk-def-sfb-ring-object`: `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`,
  including Mathlib `CategoryTheory.MonObj`, `IsMonHom`, and `Mon`. This item uses
  the general monoid-object clause, not the additional sheaf specializations.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, module morphisms and forgetful functors.
- `sk-def-sfb-change-of-scalars`:
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, with
  `CategoryTheory.Mod.comap` from Mathlib. This item uses only restriction;
  the stronger braided/closed/colimit assumptions for extension/coextension
  are not imposed here.
- `def-sfb-modobj-transport`:
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Functor.mapMod`, `modObjObj`, `act_mapMod_obj`.
  The dependency's closed upstream audit supplies the module and declaration names.
- `def-sfb-modobj-transport-adjunction`:
  `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`,
  `CategoryTheory.Adjunction.mapModAdjunction`, `unitAlgHom`, `isMonHom_unitAlgHom`.
- The remaining seven recorded dependency nodes use
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`:
  `def-sfb-projection-formula` uses `Functor.ProjectionFormula`;
  `def-sfb-modobj-linearization` uses `Functor.ProjectionFormula.mapModLeft`;
  `def-sfb-modobj-linearization-right-adjoint` uses `Functor.ProjectionFormula.mapModRight`;
  `def-sfb-modobj-linearized-adjunction` uses `Functor.ProjectionFormula.mapModAdjunction`;
  `def-sfb-adjunction-has-projection-formula` uses `Adjunction.HasProjectionFormula`;
  `def-sfb-adjunction-projection-formula` uses `Adjunction.projectionFormula`;
  `def-sfb-modobj-linearization-transport-adjunction` uses `Adjunction.mapModLeftAdjunction`.
  All names in this list have prefix `CategoryTheory.`.

Edge cases checked against the definitions: identity functors and identity adjunctions
recover the original action and ordinary adjunction; the monoidal unit monoid is allowed;
noncommutative monoids are allowed throughout; zero/trivial modules in an additive
specialization are allowed without imposing an additive hypothesis generally; empty
categories cause no unintended inhabitedness hypothesis (quantification over a monoid
object is simply empty there). There is no index set, degree, characteristic or finite-rank
restriction. The four independent object/morphism universes include sites with different
object and morphism universes. For clause 4 the canonical projection formula is essential:
an arbitrary coherent projection formula need not have the stated theta identity, and
this record uses exactly `adj.projectionFormula`.

Searches actually run:

- `msearch.py leanfinder`: “Transport module objects along lax monoidal functors and
  linearize adjunctions by projection formulas”. Eight hits, including
  `CategoryTheory.Adjunction.mapMon`, `Mod_.comap`,
  `Adjunction.rightAdjointLaxMonoidal_μ`, and representation linearization. These give
  partial ingredients, not the complete module constructions.
- `msearch.py loogle`: `CategoryTheory.Functor.mapMod, CategoryTheory.Functor.ProjectionFormula`.
  Zero hits; the service reported unknown identifier `CategoryTheory.Functor.mapMod`.
- `msearch.py grep`: `mapMod|ProjectionFormula|mapModAdjunction`, subdirectory
  `CategoryTheory/Monoidal`. One hit: Mathlib `Mon.lean:856`, the `mapMod` TODO.
- `msearch.py leansearch`: “A projection formula linearizes a functor and its right
  adjoint to categories of modules over monoid objects”. Eight hits concerning action
  categories, module forgetful/presheaf adjoints, Grothendieck projection and projectives;
  none gives the complete construction.
- `rg -n 'mapMod|ProjectionFormula|mapModLeftAdjunction'` in project
  `WeilConjectures/CategoryTheory/ModuleObjects` and the upstream Mathlib extension
  `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Mod.lean`: found all nine exact
  blueprint constructions; read their complete signatures, contexts, data and docstrings.
- `rg -n 'sk-def-sfb-transport' lean/WeilConjectures dag/lean_names_upstream.json`:
  no textual node-id hit. The name/concept search above nevertheless finds the exact APIs.
- `rg` over `lean/Sheaf` for `mapMod|ProjectionFormula|sk-def-sfb-transport`, followed by
  declaration-focused search: consumers and specialized projection formulas exist;
  no replacement for this general upstream interface is needed.

No new nodes, dependency repairs, statement correction, disputed statement, new proofs,
new definitions, or new `sorry` are included. The existing binding is checked by the
required delivery wrapper's server compile probe, which imports the recorded module and
`#check`s every recorded declaration, followed by the server preflight.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
