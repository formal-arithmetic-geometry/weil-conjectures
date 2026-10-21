## Worker report

Existing declaration: `CategoryTheory.Mod.restrictCoextendAdjunction` in
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, lines 828–839.
No Lean module is added. Only the item's `lean` field changes. The current blueprint
explicitly names this declaration in its `lean` list; its statement agrees with the DAG.
No repair-note file for this item was found in `coord/repair-notes`.

The full inherited context is `universe v u`, `{C : Type u} [Category.{v} C]
[MonoidalCategory C] [MonoidalClosed C] {R S : C} [MonObj R] [MonObj S]
(φ : R ⟶ S) [HasEqualizers C] [IsMonHom φ]`. Reading the section boundaries
confirms that the earlier extension-of-scalars hypotheses do not apply to this section.
Thus both object and morphism universes are arbitrary, and no braiding, commutativity,
preadditivity, coequalizers, or tensor preservation is assumed.

Clause-by-clause correspondence:

- The situation of `def-sfb-modobj-coextension` is exactly the above context and
  `Mod.coextendScalars φ`. Its object is `coextendScalarsObj φ N`, the equalizer of
  `coextendFst φ N` and `coextendSnd S N`. These are the dependency's recorded declarations,
  in the same upstream module. `coextendEv φ N : S ⊗ (coextendScalarsObj φ N).X ⟶ N.X`
  is the evaluation obtained from the equalizer inclusion into the internal Hom.
- The monoid morphism is `(φ : R ⟶ S) [IsMonHom φ]`, with `[MonObj R] [MonObj S]`.
- Evaluation at the unit is `Mod.coextendCounitHom φ N`, defined literally as
  `(λ_ _).inv ≫ η[S] ▷ _ ≫ coextendEv φ N` (lines 750–752).
- Its R-linearity on the restricted module is bundled by
  `Mod.coextendCounit φ N : (comap φ).obj (coextendScalarsObj φ N) ⟶ N`
  (lines 766–776); `coextendCounit_hom` identifies its underlying morphism with that
  evaluation. In Mathlib, a `Mod.Hom` contains the `IsModHom` instance, so this type
  expresses the linearity, rather than merely an underlying arrow.
- The S-module `M` and R-module `N` are respectively `(M : Mod C S)` and `(N : Mod C R)`.
  The equivalence `Mod.coextendHomEquiv φ N M` has type
  `((comap φ).obj M ⟶ N) ≃ (M ⟶ coextendScalarsObj φ N)` (lines 817–826).
  Its inverse is literally `fun g ↦ (comap φ).map g ≫ coextendCounit φ N`, the
  node's map from S-linear maps to R-linear maps. Lean's `≫` reverses the printed
  order of the node's function-composition notation.
- The inverse of the node's map is the equivalence's `toFun := coextendHom φ`.
  `coextendHom` is constructed by `coextendHomMk φ (γ[S,M.X] ≫ f.hom)`.
  `whiskerLeft_coextendHom_hom_coextendEv` states
  `S ◁ (coextendHom φ f).hom ≫ coextendEv φ N = γ[S,M.X] ≫ f.hom`.
  This is exactly the ordered-tensor meaning of `m ↦ (s ↦ f(sm))`; no elements,
  symmetry, or braiding are used to interpret the formula.
- Bijectivity is the `Equiv` data, including `left_inv` and `right_inv`.
  Naturality in both M and N is supplied in the `homEquiv_naturality_left_symm`
  and `homEquiv_naturality_right` fields used by `restrictCoextendAdjunction`.
  The adjunction is `comap φ ⊣ coextendScalars φ`, constructed with
  `Adjunction.mkOfHomEquiv { homEquiv M N := coextendHomEquiv φ N M, ... }`.
  Hence it is the specified natural bijection, with the specified evaluation counit.

Dependency declarations read with their docstrings and full signatures:

- `def-sfb-modobj-coextension`: the recorded
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `CategoryTheory.Mod.coextendScalars`; also its equalizer, inclusion, evaluation,
  lifting, action, object, and morphism declarations, lines 488–740.
- `def-sfb-modobj-restriction`: its `mathlib_match`
  `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod.comap` (lines 403–411),
  specialized to the monoidal category's self-action. `scalarRestriction` uses
  `φ ▷ M.X ≫ γ[S,M.X]`, and `comap` leaves underlying objects and arrows unchanged.
- Proof dependency `sk-def-sfb-module-objects`: its recorded
  `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`; also `ModObj`,
  `Mod.Hom`, and `Mod.Hom.mk'` for the action laws and linear morphisms.
- Proof dependency `lem-weil-pbc-adjunction-of-natural-bijection`: its Mathlib match
  `Mathlib.CategoryTheory.Adjunction.Basic`, `CategoryTheory.Adjunction.mkOfHomEquiv`
  and `Adjunction.CoreHomEquiv` (lines 351–361 and 436–450), used by the existing
  upstream construction. No proof-only import needs adding because no file is written.

Edge cases checked by reading the actual construction and its hypotheses:
identity φ is admitted (upstream `coextendScalarsId` subsequently uses this adjunction);
noncommutative monoid objects are admitted; zero/trivial module objects, when the
ambient category has them, are not excluded; no nonzero or nonempty hypothesis occurs.
No zero object is required of an arbitrary closed monoidal category. The construction
uses no pointwise detection of morphisms or symmetry of tensor factors. Independent
universes `u` and `v` are preserved. No statement correction or disputed clause is needed.

Searches on 2026-10-21 (all msearch calls used group NG and this item):

- LeanSearch via `msearch.py leansearch`, query: "Restriction of scalars is left adjoint
  to coextension of scalars for modules over monoid objects in a closed monoidal category".
  Eight hits, notably `ModuleCat.restrictCoextendScalarsAdj`, restriction instances,
  and ordinary module/representation constructions. These Mathlib matches are special
  cases, not a replacement for the generic module-object construction.
- LeanFinder via `msearch.py leanfinder`, query: "In a closed monoidal category with
  equalizers restriction of scalars for module objects is left adjoint to coextension
  with evaluation counit and inverse f maps m to s maps f(sm)". Eight hits, all ordinary
  `ModuleCat` restriction/coextension declarations and formulas. No generic Mathlib match.
- Loogle via `msearch.py loogle`, query:
  `CategoryTheory.Mod.restrictCoextendAdjunction, CategoryTheory.Mod.coextendHomEquiv`.
  The service reported unknown identifier `CategoryTheory.Mod.restrictCoextendAdjunction`,
  because it indexes Mathlib. Corrected Mathlib query `ModuleCat.restrictCoextendScalarsAdj`
  returned that one ordinary ring-module adjunction; it is too specialized.
- Mathlib grep via `msearch.py grep`, query
  `restrictCoextend|coextendScalars|coextendHomEquiv`, subdirectory
  `CategoryTheory/Monoidal`: zero hits.
- Direct `rg -n` of `lean/WeilConjectures` for
  `restrictCoextendAdjunction|coextendHomEquiv|coextendCounitHom|def coextendHom `:
  exact definitions in `CategoryTheory/ModuleObjects/ExtendScalars.lean`, with existing
  consumers in `MapMod.lean` and pro-etale lower-shriek files. The full defining section
  was read, not just the matches.
- `grep -rn` of `lean/WeilConjectures` for this node id: zero hits. Direct `rg` of
  `dag/lean_names_upstream.json` for the adjunction/equivalence: zero hits; the current
  source supplies the exact declarations despite that older name inventory.
- Direct `rg -n` of `lean/Sheaf` for
  `restrictCoextendAdjunction|coextendHomEquiv|coextendCounitHom`: uses of the upstream
  adjunction in lower-shriek exchange, gluing, and support localization; no duplicate
  generic definition.

Validation: the prescribed delivery dry run checks this existing-declaration record
against the server's live source. There is no delivered Lean file to compile under
brief-stage2 §1's existing-declaration rule.

## Second reading by NG

A second self-reading of the open node, blueprint source, dependency records, and actual
upstream definition checked the context and each displayed clause above. It confirmed
that the equivalence is oriented opposite to the node's forward map, so the report
explicitly uses its `invFun` for evaluation and its `toFun` for the inverse formula.
It also checked that extension's commutativity/braiding assumptions end before this
coextension section. No mismatch, new node, dependency repair, or source edit is needed.
No independent worker was started, as instructed by the dispatcher; the maintainer's
independent review remains the delivery review.
