## Worker report

Bind def-sfb-comap-mapmod-square to the exact existing definition
`CategoryTheory.Mod.comapMapModComapIso` in
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
(lines 71–92 of the source read locally and on the current server using
`scompile.py --source`). There is no new Lean module, theorem, definition node,
dependency repair, or statement change. Only the item's lean record changes.
The blueprint's explicit Lean name is this same declaration. The recorded
signature is verbatim from `noncomputable def` up to, excluding, `:=`;
the section parameters are checked below.

Clause-by-clause correspondence:

- Monoidal categories C and D are `{C : Type u₁} [Category.{v₁} C]
  [MonoidalCategory C]` and `{D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory D]`. All four universes are explicitly declared and independent.
- A lax monoidal functor is `(F : C ⥤ D) [F.LaxMonoidal]`.
  No strong-monoidal or preservation hypothesis occurs.
- The two source monoids are `{R_X S_X : C} [MonObj R_X] [MonObj S_X]`;
  the two target monoids are `{R_Y S_Y : D} [MonObj R_Y] [MonObj S_Y]`.
  The transported monoid structures use the existing scoped Obj instances.
- The source arrow is `(φ_X : R_X ⟶ S_X) [IsMonHom φ_X]`,
  and the target arrow is `(φ_Y : R_Y ⟶ S_Y) [IsMonHom φ_Y]`.
- The vertical arrows are `(η_R : R_Y ⟶ F.obj R_X) [IsMonHom η_R]`
  and `(η_S : S_Y ⟶ F.obj S_X) [IsMonHom η_S]`.
- Commutativity is exactly `(sq : φ_Y ≫ η_S = η_R ≫ F.map φ_X)`.
  Lean's left-to-right composition is the source's
  `η_S ∘ φ_Y = Fφ_X ∘ η_R`, with the same orientation.
- The left composite in the natural isomorphism is
  `(F.mapMod S_X ⋙ comap η_S) ⋙ comap φ_Y`. Its source is `Mod C S_X`
  and its target is `Mod D R_Y`.
- The right composite is `comap φ_X ⋙ (F.mapMod R_X ⋙ comap η_R)`,
  with the same source and target. The result is `≅`, a natural isomorphism,
  in exactly the direction in the node.
- The final clause specifies which isomorphism. The actual definition is
  the chain of functor associators, whiskering by `F.mapMod`,
  `(comapComp φ_Y η_S).symm`, `comapCongr sq`,
  `comapComp η_R (F.map φ_X)`, and the inverse of
  `F.mapModComapIso φ_X` whiskered by `comap η_R`.
  Thus it explicitly factors through restriction along the two equal
  composites; it is not an arbitrary natural isomorphism. The existing lemma
  `CategoryTheory.Mod.comapMapModComapIso_hom_app_hom` immediately below
  states that its component has underlying morphism `𝟙 (F.obj M.X)`.

Dependency declarations read and used:

- sk-def-sfb-transport records
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`;
  its public import of `MapMod` supplies `CategoryTheory.Functor.mapMod`,
  `Functor.modObjObj`, `Functor.act_mapMod_obj`, and
  `Functor.mapMod_comp_forget`. The actual mapMod definition in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod` has underlying object
  `F.obj M.X`, action `LaxMonoidal.μ F R M.X ≫ F.map (act M.X)`, and sends
  a morphism to `F.map f.hom`. The existing `Functor.mapModComapIso`
  in `MapMod` compares scalar restriction and transport by identity components.
- sk-def-sfb-change-of-scalars records
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, including
  `CategoryTheory.Mod.comap`. Mathlib's `CategoryTheory.Monoidal.Mod`
  defines scalarRestriction by `f ⊵ₗ M ≫ γ[B,M]`, and comap retains
  the underlying object and morphism. With the tensor self-action this is
  precisely the restriction in the node. The extension/coextension clauses
  of that dependency are not assumptions on this square isomorphism.
- Proof dependencies agree with these definitions:
  def-sfb-modobj-transport records `Functor.mapMod`, `Functor.modObjObj`,
  `Functor.act_mapMod_obj`; def-sfb-modobj-restriction's Mathlib match is
  `CategoryTheory.Mod.comap`; sk-def-sfb-module-objects records Mathlib
  `CategoryTheory.Mod`. No private replacement of any dependency is made.

Source checked: the entire main-20261015 blueprint file
`sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-comap-mapmod-square.md`
and its identical DAG statement. Its named declaration, square, functor direction,
and common-composite normalization agree exactly with the existing source.
The local CompactObject example is withdrawn; its DAG record now binds the
existing upstream compact-object definition. This delivery follows the analogous
existing-declaration record format, without a new module.

Edge cases checked by inspection of the construction: identity F; identity
horizontal and/or vertical morphisms; noncommutative monoid objects in a
nonbraided monoidal category; a genuinely lax functor with noninvertible
structure maps; zero modules when present; unrelated source and target object
and morphism universes. The definition only uses identities, lax naturality,
restriction composition, and the square equation, so these cases introduce
no excluded case. No abelian, braided, closed, commutative, exactness, or
(co)limit assumptions occur in the applicable section. The hypotheses in
later sections of ChangeOfScalarsSquare are outside this definition's scope.

Searches (2026-10-21):

- msearch.py leanfinder, query: "Restriction of scalars for internal module
  objects commutes with lax monoidal transport along a commutative square of
  monoid objects". Eight hits: scalarRestriction, its linearity/action facts,
  comap, and ordinary ModuleCat restriction-composition naturality. These
  are ingredients or special cases, not the complete square.
- msearch.py leansearch, query: "natural isomorphism restriction of scalars
  lax monoidal functor commutative square module objects". Eight hits on
  ModuleCat.restrictScalars, its pseudofunctor/congruence, internal
  scalarRestriction/comap and presheaf restriction. None gives the whole square.
- msearch.py loogle, query: "CategoryTheory.Mod.comap". Four hits:
  comap, comap_obj_X, comap_obj_mod, comap_map_hom in
  Mathlib.CategoryTheory.Monoidal.Mod. These give scalar restriction only.
- msearch.py grep, query: "comapMapModComapIso|mapModComap|comapComp",
  Mathlib/CategoryTheory. Four hits on Pi/GradedObject reindexing composition;
  no complete square comparison.
- rg over lean/WeilConjectures and lean/Sheaf, query:
  "comapMapModComapIso|mapModComap|comap.*[Mm]apMod|mapMod.*comap".
  Exact match: ChangeOfScalarsSquare.lean:85; the defining expression at
  lines 87–92 and identity-component lemma at lines 94–98 were read.
  Project hits elsewhere are applications of existing mapMod/comap APIs.
- rg for the item id in lean/WeilConjectures: no hit. The declaration is
  present by name and source, despite having no blueprint-id annotation.
- rg for comapMapModComapIso in dag/lean_names_upstream.json: no hit;
  the current live Lean source, confirmed by scompile.py --source, provides
  the exact declaration missing from that older name index.

No STATEMENT-DISPUTED flag or mathematical node fault was found.

Validation: deliver2.py's dry run and delivery generate a temporary existing-
declaration #check probe and compile it using scompile against the live
published build, then run the server's maintainer preflight. No Lean file
is included in this existing-only delivery.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
