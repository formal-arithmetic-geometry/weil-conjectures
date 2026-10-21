## Worker report

Recorded the existing upstream definition
`CategoryTheory.Mod.extendScalarsComapIsoOfIsIso` in
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
(source lines 101–129; declaration at line 120). No Lean module is delivered,
no proof is written, and no new sorry is introduced. Only the item's `lean`
field changes. The declaration was read both locally and from the current
server via `scompile.py --source` and the relevant source is identical.
There is no repair note for this item.

Source checked: the current main-20261015 blueprint file
`sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-extend-comap-iso-of-iso.md`
and its adjacent proof file. The following gives every hypothesis and clause,
including section variables on which the existing declaration depends.

| Node text | Existing Lean |
| --- | --- |
| Category C | `{C : Type u₁} [Category.{v₁} C]`, with independent explicit universes |
| Braided monoidal closed | `[MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]` |
| Equalizers and coequalizers | `[HasEqualizers C] [HasCoequalizers C]` |
| Tensoring on each side preserves colimits | `[∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]` and the same for `tensorRight X` |
| R, S, R', S' monoid objects | `{R S R' S' : C}` with `[MonObj R]`, `[MonObj S]`, `[MonObj R']`, `[MonObj S']` |
| R and S commutative | `[IsCommMonObj R] [IsCommMonObj S]` |
| Four monoid morphisms | `(φ : R ⟶ S) [IsMonHom φ]`, `(ψ : R' ⟶ S') [IsMonHom ψ]`, `(a : R ⟶ R') [IsMonHom a]`, `(b : S ⟶ S') [IsMonHom b]` |
| a and b isomorphisms | `[IsIso a] [IsIso b]`; no invertibility of φ or ψ |
| ψ ∘ a = b ∘ φ | `(sq : a ≫ ψ = φ ≫ b)` |
| Resψ ∘ Extb | `extendScalars b ⋙ comap ψ` |
| Exta ∘ Resφ | `comap φ ⋙ extendScalars a` |
| Natural isomorphism | `≅` in the functor category |
| Source ModS(C), target ModR'(C) | `extendScalars b : Mod C S ⥤ Mod C S'`, then `comap ψ : Mod C S' ⥤ Mod C R'`; on the right `comap φ : Mod C S ⥤ Mod C R`, then `extendScalars a : Mod C R ⥤ Mod C R'` |

The tensor-colimit size annotation is the existing change-of-scalars API's
smallest-universe convention. It suffices for its relative coequalizers. It
excludes none of the node's categories: arbitrary colimit preservation implies
it. Conversely in this braided closed setting both tensor functors are left
adjoints (on the right use the braiding), so preservation of all existing
colimits is automatic. No extra size equality or restriction of C is imposed.

Dependency declarations read and used by the existing construction:

- `sk-def-sfb-change-of-scalars` records
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `CategoryTheory.Mod.extendScalars`, `coextendScalars`, `extendScalarsObj_X`,
  `extendRestrictAdjunction`, `restrictCoextendAdjunction`, `extendScalarsId`,
  and `extendScalarsComp`. Their signatures and docstrings were read.
  Extension is the prescribed relative coequalizer, with genuine data.
- `CategoryTheory.Mod.comap` is the recorded restriction declaration,
  defined in `Mathlib.CategoryTheory.Monoidal.Mod` and publicly available
  through that dependency module. Its action and underlying maps were read.
- The upstream module imports `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`,
  whose `CategoryTheory.Mod.extendScalarsIsoComapInv` identifies extension
  along an isomorphism with restriction along its inverse.
  Composite restrictions and equality transport are `Mod.comapComp` and
  `Mod.comapCongr` from the same upstream module chain.

The existing data follow all four proof steps of the node: whisker the b
comparison, combine the two restrictions, transport along
`ψ ≫ (asIso b).inv = (asIso a).inv ≫ φ`, split the right composite
restriction, and whisker the inverse of the a comparison. This is the
specified canonical comparison, rather than a choice from mere existence.

Edge cases checked by reading the signatures and construction: identity a
and b give the usual restriction comparison; φ and ψ may be noninvertible;
R' and S' need no independently supplied commutativity; a zero module, when
present, is allowed; no inhabitedness, nonzero object, characteristic, or
finite-rank hypothesis appears. C's object and morphism universes are
independent. The natural-isomorphism type supplies inverse and naturality
on every module and every module morphism.

Searches performed:

- `msearch.py ... leanfinder` query: "In a commutative square of monoid objects
  with vertical isomorphisms, restriction of scalars commutes with extension
  of scalars along those isomorphisms". Eight hits, including ordinary
  `ModuleCat` composite-restriction statements and
  `CategoryTheory.Mod_.scalarRestriction_hom`; none is this general square
  construction in Mathlib.
- `msearch.py ... loogle` query:
  `CategoryTheory.Mod.extendScalarsComapIsoOfIsIso, CategoryTheory.Mod.extendScalars, CategoryTheory.Mod.comap`.
  Zero hits; the service reports the first upstream identifier unknown.
- `msearch.py ... grep` query
  `extendScalarsComap|extendScalarsIsoComapInv|comapComp` in
  `CategoryTheory/Monoidal`: zero Mathlib hits.
- `rg -n` of `extendScalarsComapIsoOfIsIso|extendScalarsIsoComapInv|extendScalarsComap`
  in `lean/WeilConjectures` and `lean/Sheaf`: the exact upstream definition
  at `ChangeOfScalarsSquare.lean:120`, many upstream and project consumers,
  and related inverse-restriction comparisons. The blueprint-id search in
  upstream sources found no marker; the declaration-name search is decisive.
- `rg -n` of the exact name in `dag/lean_names_upstream.json` and the module
  source: the index has no match, but the actual upstream file does.

No statement fault or dispute was found. No new nodes, dependency repairs,
or statement corrections are needed. As required for an `existing: true`
attachment, there is no new module to compile; the delivery dry run checks
the attachment against the live server.

## Second reading by Q87

Re-read the node, its current blueprint statement and proof, and the complete
upstream `ExtendScalarsOfIsIso` section after preparing the record. This is
a second pass by this worker; the dispatcher forbids starting other agents,
and the maintainer supplies the independent review.

Checked every row of the correspondence table against the actual section
binders. In particular, the square equation has the right composition order,
the natural isomorphism has source Mod C S and target Mod C R', and only a
and b must be invertible. Both commutativity assumptions are exactly on R
and S. The existing docstring calls a and b the "horizontal" sides, whereas
the node draws them vertically; this is only a diagram-wording slip, since
the actual types are R → R' and S → S' and the formal construction matches
the node. No declaration or node statement needed changing. The signature
in `lean.statement` is copied verbatim from the existing declaration before
`:=`; its implicit section variables are documented above.
