## Worker report

Existing match: `CategoryTheory.Functor.ProjectionFormula.mapModLeftComapIso` in
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`, lines 172–191.
No Lean module is delivered: the source already constructs precisely this natural
isomorphism. I read its full context, docstring and construction both locally and via
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`.
There is no repair note for this item. Only the item's `lean` field changes.

Hypothesis and clause correspondence:

- Monoidal categories C and D: `{C : Type u₁} [Category.{v₁} C]
  [MonoidalCategory C]` and `{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]`.
  The four universes are explicitly declared and independent.
- Strong monoidal S: `{S : D ⥤ C} [S.Monoidal]`.
- Functor P with the specified coherent projection formula: `{P : C ⥤ D}
  (pf : S.ProjectionFormula P)`. Its `iso`, `natural_left`, `natural_right`, `unit`
  and `assoc` fields give precisely the dependency's projection formula.
- Every monoid B and B′ in D: `{B B' : D} [MonObj B] [MonObj B']`.
  Their transported monoid structures are `S.monObjObj` via the global scoped
  `CategoryTheory.Obj` instance. `S.map φ` is a monoid morphism by
  `CategoryTheory.Functor.map.instIsMonHom`.
- A morphism of monoid objects: `(φ : B ⟶ B') [IsMonHom φ]`.
- Linearizations P_B and P_B′: `pf.mapModLeft B` and `pf.mapModLeft B'`,
  using the recorded dependency rather than a second construction.
- The displayed isomorphism: `pf.mapModLeft B' ⋙ Mod.comap φ ≅
  Mod.comap (S.map φ) ⋙ pf.mapModLeft B`. Lean's `⋙` composes in the
  opposite written order to the source's `∘`, so both sides and their direction
  agree exactly. Both are functors `Mod C (S.obj B') ⥤ Mod D B`.
- Identity on underlying objects: both object formulas give `P.obj M.X`.
  The existing construction is `NatIso.ofComponents (fun M ↦
  Mod.isoMk (Iso.refl _) ...) ...`; consequently the underlying component maps
  of both hom and inv are the identity, not an arbitrary chosen isomorphism.
- Naturality is part of the resulting natural isomorphism and is established in
  its construction on the common underlying morphism `P.map f.hom`.

The proof agrees with all four node proof steps: restriction and linearization
produce the two actions; `pf.whiskerRight_iso_inv_assoc` (inverse naturality in
B) and `P.map_comp` identify them; `Mod.isoMk (Iso.refl _)` gives the two inverse
identity module arrows; equality of the underlying `P.map f.hom` proves naturality.
This existing proof is reused unchanged; no new proof is written in stage 2.

Dependency declarations read and used:

- `sk-def-sfb-transport`, `def-sfb-projection-formula`, and
  `def-sfb-modobj-linearization`: `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`,
  `CategoryTheory.Functor.ProjectionFormula`, `.smul`, `.modObj`, `.mapModLeft`,
  `.mapModLeft_obj_X`, `.mapModLeft_map_hom`, `.mapModLeft_obj_smul`, and
  `.mapModLeft_comp_forget`. The latter object and morphism formulas are literal
  `P.obj M.X` and `P.map f.hom`, and the action is
  `(pf.iso B M.X).inv ≫ P.map γ[S.obj B,M.X]`.
- `sk-def-sfb-change-of-scalars` and `def-sfb-modobj-restriction`:
  `CategoryTheory.Mod.comap` and `.scalarRestriction` in
  `Mathlib.CategoryTheory.Monoidal.Mod`. The former node's recorded module is
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, which imports
  this API. Only restriction (clause 1) is used here; extension/coextension and
  their extra colimit/closedness assumptions are not required.
- `det-def-sfb-ring-object-transport`: `Mathlib.CategoryTheory.Monoidal.Mon`,
  `CategoryTheory.Functor.monObjObj`, `.map.instIsMonHom`, and `.mapMon`.
  Its other clauses (`mapCommMon`, `mapMonNatTrans`, `mapMonNatIso`) are not
  needed for this construction.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.ModObj`, `CategoryTheory.Mod`, `CategoryTheory.Mod.Hom`,
  `CategoryTheory.Mod.forget`; module arrows retain their underlying maps.

Edge cases checked before attachment: φ = identity still gives identity
components; B and B′ need not be commutative; φ need not be invertible;
there is no braiding, adjunction, exactness, closedness or colimit hypothesis.
Different object and morphism universes for the two categories remain allowed.
No nonempty-object assumption or zero-object assumption is imposed. The two
module actions coincide for an arbitrary φ by projection-formula naturality.
There is no statement dispute, correction, missing notion or dependency repair.

Searches performed:

- `msearch.py ... leanfinder`, query “The linearization of a functor satisfying
  a projection formula commutes with restriction of scalars along a morphism of
  monoid objects”: eight hits, including the `Mod_` scalarRestriction/comap
  aliases, `Action.res_linear`, and representation linearization; none gives
  this whole comparison.
- `msearch.py ... loogle`, query `"Mod_", "comap"`: one hit,
  `CategoryTheory.Mod_.comap`, the alias for restriction alone.
- `msearch.py ... grep`, query
  `ProjectionFormula|mapModLeftComapIso|scalarRestriction|def comap`, subdirectory
  `CategoryTheory/Monoidal`: five hits for scalarRestriction and its lemmas;
  no Mathlib projection-formula comparison.
- `rg` over the project's `lean/WeilConjectures/CategoryTheory/ModuleObjects`
  and `lean/Sheaf/CategoryTheory` for `mapModLeftComapIso`, projection formula,
  and the blueprint id found the exact declaration in ChangeOfScalarsSquare.
  The blueprint-id search over all `lean/WeilConjectures` gave no hit: the
  existing declaration uses its mathematical name rather than this node id.
  The Sheaf hits concern other projection-formula constructions.
  A further exact-name/id search over all `lean/Sheaf` and an exact-name search
  in `dag/lean_names_upstream.json` gave no hits.

Validation: an existing-only attachment introduces no file requiring a new
single-file compile (brief-stage2 §1). The delivery wrapper performs its required
existing-declaration and preflight checks. The live source was read through the
prescribed server wrapper. No local compiler, build, direct Git command, or
write to the shared repository is used.
The prescribed dry run passed preflight and both generated server compile checks
(`Sheaf.Stage2.Sandbox0` and `Sheaf.Stage2.Check`) on 2026-10-21.

## Second reading by Q47

I reread the source node, its blueprint statement and proof, and the existing
full declaration after selecting the binding. Each hypothesis above is present
in the declaration context; the independently quantified universes are retained.
I checked the order of both functor composites and the source and target module
categories. The final identity clause is realized by `Iso.refl` inside `Mod.isoMk`,
including the inverse map. No mismatch was found and no statement was changed.
This is a self-check: the dispatcher forbids starting another worker, and the
maintainer's independent review remains the separate review of this delivery.
