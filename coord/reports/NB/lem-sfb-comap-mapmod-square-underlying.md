## Worker report

This is an existing-declaration delivery. No Lean module is added. The live declaration
`CategoryTheory.Mod.comapMapModComapIso_hom_app_hom` in
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare` says exactly what
lem-sfb-comap-mapmod-square-underlying says. Only the item’s `lean` field changes.
The current server source was read with `scompile.py --source`; its lemma and dependency
agree with the local source. There is no repair note for this item.

Source: main-20261015, sec-six-functors-basics /
sk-def-sfb-coefficient-comparisons / lem-sfb-comap-mapmod-square-underlying.md,
order 1728, and its proof file. The source names this exact Lean declaration.

Hypothesis and clause correspondence:

- The inherited monoidal categories are `{C : Type u₁} [Category.{v₁} C]
  [MonoidalCategory C]` and `{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]`.
  The four universes are independent.
- The inherited lax monoidal functor is `(F : C ⥤ D) [F.LaxMonoidal]`.
  There is no strong monoidal, braided, commutative, exactness or colimit hypothesis.
- The inherited square has `{R_X S_X : C}`, `{R_Y S_Y : D}`, each with its
  `MonObj` instance, and `(φ_X : R_X ⟶ S_X)`, `(φ_Y : R_Y ⟶ S_Y)`,
  `(η_R : R_Y ⟶ F.obj R_X)`, `(η_S : S_Y ⟶ F.obj S_X)`, each with
  `IsMonHom`. Its sole equality is `(sq : φ_Y ≫ η_S = η_R ≫ F.map φ_X)`.
  This is precisely the dependency’s square, in Lean’s left-to-right composition order.
- “For every S_X-module M” is `(M : Mod C S_X)`.
- “The isomorphism of def-sfb-comap-mapmod-square” is the dependency’s recorded
  `comapMapModComapIso F φ_X φ_Y η_R η_S sq`, not an arbitrary comparison.
- “The component at M” is `.hom.app M`; “underlying morphism” is its final `.hom`.
- “The identity of F(M)” is `= 𝟙 (F.obj M.X)`.

The signature in the node is copied verbatim from the keyword `lemma` to before `:=`.
Section variables supply exactly the inherited context just listed.

Dependency declarations read and used:

- def-sfb-comap-mapmod-square records `CategoryTheory.Mod.comapMapModComapIso`
  in `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`.
  Its full section, docstring and body were read. The body factors through
  `comapComp`, `comapCongr sq`, and the inverse of `F.mapModComapIso φ_X`, with
  the required functor associators, so it is the specified common-composite comparison.
- def-sfb-modobj-restriction has the Mathlib match `CategoryTheory.Mod.comap`
  in `Mathlib.CategoryTheory.Monoidal.Mod`; its definition retains both the underlying
  object and the underlying arrow. This needs no replacement record.
- sk-def-sfb-module-objects records `CategoryTheory.Mod` in the same Mathlib module.
  Its `ModObj`, `Mod.Hom`, and underlying-object/underlying-arrow projections were read.
- def-sfb-modobj-transport records `CategoryTheory.Functor.mapMod` and `modObjObj`.
  These are defined in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`.
  The action is the lax tensorator followed by F of the original action; maps are F
  of the underlying module morphisms. `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`
  supplies `mapMod_comp_forget` and `mapModComapIso`.

Proof correspondence: the existing lemma unfolds the canonical comparison to a composite
of identities of `F.obj M.X` and simplifies. Reading the constituent definitions verifies
all three node proof steps: restriction-composition and equal-map comparisons have identity
components; transport/restriction uses naturality of the lax tensorator and has identity
components; associators and whiskering preserve these identities. No tensorator is inverted.
No theorem or definition is restated or newly proved in this delivery.

Edge cases checked against the full source: F may be the identity; any square edge may be
an identity; monoid objects may be noncommutative; a zero module is included whenever the
ambient category has one; no nonemptiness or nonzero condition is introduced. The formula
uses only the lax structure, so a noninvertible tensorator is permitted. Independent object
and morphism universes remain intact. No statement correction or dispute was found.

Searches made:

- `msearch.py leanfinder`, query “the component of the canonical scalar restriction lax
  monoidal module transport square isomorphism has identity underlying morphism”: eight
  hits, including `Mod_.scalarRestriction_hom`, `Mod_.scalarRestriction`, and ordinary
  `ModuleCat.restrictScalarsId`/`restrictScalarsComp` component formulas; no exact general
  module-object square theorem in Mathlib.
- `msearch.py loogle`, query `CategoryTheory.Mod.comapMapModComapIso_hom_app_hom`:
  unknown identifier, zero hits. This service does not index this project; this is not
  evidence that the project declaration is absent.
- `msearch.py grep`, query `comapMapModComapIso|mapModComapIso|comap_map_hom`,
  under `CategoryTheory/Monoidal`: zero hits from that service.
- Direct `rg` in the local Mathlib `CategoryTheory/Monoidal/Mod.lean` finds `comap`
  and scalar restriction, whose signatures and bodies were read.
- Direct `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `comapMapModComapIso` and the item id finds
  the exact lemma at ChangeOfScalarsSquare.lean:95 and consumers in the project,
  including ContinuousIntegralPullComposition and CondensedOverlapFactorTranspose.
  The existing declaration is therefore reused. The only DAG occurrence of its full
  name outside the item is the blueprint unit’s inventory, not a competing definition.

Validation: a sandbox-only probe imports the recorded live module, checks the existing
lemma at four explicit independent universes, and prints its axioms through `scompile.py`.
The probe passed without warnings (sandbox 5.7 s; library check 3.5 s). The only
reported axioms were `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
The delivery tool also checks the recorded existing declaration on the server.

## Second reading by NB

No independent worker second reading was performed: the dispatcher brief forbids starting
other agents and requires direct delivery. The maintainer’s independent review reads this
packet. A final self-check compared the blueprint, node, dependency’s square and source
lemma clause by clause as above; no mismatch or source correction was found.
