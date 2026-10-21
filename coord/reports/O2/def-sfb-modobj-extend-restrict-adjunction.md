## Worker report

This delivery records the existing upstream construction
`CategoryTheory.Mod.extendRestrictAdjunction` in
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars` (lines 422–434).
No Lean module is added: the exact notion already exists. Only the item's `lean` field changes.
The source read is the main-20261015 blueprint node
`sec-proetale-coefficients/sk-def-sfb-change-of-scalars/def-sfb-modobj-extend-restrict-adjunction.md`
and its companion proof. There is no repair note for this item.
The upstream file was read locally and its current server source was independently retrieved
with `scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`.

Hypotheses and objects, matched individually:

- The situation of `def-sfb-modobj-extension` is the enclosing context of the upstream module:
  `{C : Type u} [Category.{v} C] [MonoidalCategory C]`, with independent `u` and `v`;
  `[BraidedCategory C]`; `[HasCoequalizers C]`; and preservation of small colimits by
  `tensorLeft X` and `tensorRight X` for every `X : C`.
  The explicit Lean classes are `PreservesColimitsOfSize.{0, 0}`. These are exactly the
  classes in the dependency's recorded `Mod.extendScalars` declaration in the same file.
  Preservation of all colimits assumed in the prose implies these smaller-shape classes;
  no extra existence of colimits of other shapes is required. The construction applies to
  every situation covered by the node, and no size equality is imposed.
- The monoid objects are `{R S : C} [MonObj R] [MonObj S]`; commutativity only of R is
  `[IsCommMonObj R]`; the monoid morphism is `(φ : R ⟶ S) [IsMonHom φ]`.
  There is no commutativity assumption on S, nor closed, abelian or additive structure on C.
- Every R-module M is `(M : Mod C R)` and every S-module N is `(N : Mod C S)` in the
  signatures of `extendUnit`, `extendHomEquiv` and `extendHom`.
- The extension functor is literally `Mod.extendScalars φ`, as recorded for the dependency;
  the restriction functor is literally Mathlib's `Mod.comap φ`, its dependency's mathlib match.

Each clause of the statement:

1. The displayed composite defining u_M is exactly `Mod.extendUnitHom φ M` (lines 318–320):
   `(λ_ M.X).inv ≫ η[S] ▷ M.X ≫ extendπ φ M`.
   The inverse left unitor inserts the tensor unit; `η[S] ▷ M.X` tensors the monoid unit
   with M; `extendπ φ M` is the coequalizer projection of the recorded extension construction.
   Its source and target use the actual module underlying object, with no arbitrary map.
2. R-linearity into restriction of the extended module is precisely the type
   `extendUnit : M ⟶ (comap φ).obj (extendScalarsObj φ M)` (lines 354–359).
   Its underlying map is the preceding composite by `extendUnit_hom`.
   `smul_extendUnitHom` and `whiskerLeft_extendUnitHom_smul` identify the two sides of its
   linearity equation with `φ ▷ M.X ≫ extendπ φ M`.
3. The claimed bijection is `extendHomEquiv φ M N` (lines 411–420), with type
   `(extendScalarsObj φ M ⟶ N) ≃ (M ⟶ (comap φ).obj N)`.
   Its forward function is definitionally
   `fun g ↦ extendUnit φ M ≫ (comap φ).map g`.
   Lean's diagrammatic composition is exactly the prose composite Res(g) after u_M.
   Its inverse is `extendHom φ`; the `left_inv` and `right_inv` fields prove bijectivity.
4. Naturality in M is the `homEquiv_naturality_left_symm` field of
   `extendRestrictAdjunction`; the equivalence converts its inverse formulation to the
   direct naturality equation in the node. Naturality in N is its
   `homEquiv_naturality_right` field (lines 424–434). Both use these very Hom equivalences.
5. The concluding adjunction is the recorded signature, verbatim:
   `noncomputable def extendRestrictAdjunction : extendScalars φ ⊣ comap φ`.
   Its definition is `Adjunction.mkOfHomEquiv { homEquiv := extendHomEquiv φ, ... }`.
   Mathlib's `mkOfHomEquiv_homEquiv` identifies its Hom equivalence with the supplied one;
   the unit is its value on identity, which reduces to `extendUnit φ M`.
   Thus the construction includes the specified normalization.

Dependency declarations read and used:

- `def-sfb-modobj-extension`: module
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, `CategoryTheory.Mod.extendScalars`.
  Read its enclosing hypotheses and definitions of `extendScalarsObj`, `extendπ`,
  `extendScalarsMap` and their coequalizer/action characterizations (lines 164–309).
- `def-sfb-modobj-restriction`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod.comap` (lines 403–410), with `scalarRestriction` and
  `scalarRestriction_hom` (lines 363–393). The action is φ tensor N followed by N's action,
  and underlying morphisms are retained.
- Proof dependency `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`, `Mod.regular`, `Mod.forget`.
- Proof dependency `def-weil-pbc-category-colimit`:
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`, `IsColimit`,
  and the coequalizer specialization used by the existing construction.
- Proof dependency `lem-weil-pbc-adjunction-of-natural-bijection`:
  `Mathlib.CategoryTheory.Adjunction.Basic`, `CategoryTheory.Adjunction.mkOfHomEquiv`
  and `CoreHomEquiv`, read at lines 350–456. This is exactly the constructor used upstream.
  No new imports are necessary for an existing binding.

Edge cases checked by reading the actual construction and hypotheses: identity φ; a zero
monoid/ring object and zero module when present; terminal/trivial examples; a noncommutative
S with commutative R; independent category object and morphism universes. None requires
nontriviality, nonempty elements of a module, an abelian category, or closedness. There is
no indexed-family hypothesis that could remove an empty case. The coequalizer projection,
module unit laws and equivalence fields remain valid in these cases. Nothing is disputed,
no source correction is necessary, and no dependency interface is repaired.

Searches actually run:

- `msearch.py ... leanfinder`: "Extension of scalars for internal module objects in a braided
  monoidal category is left adjoint to restriction of scalars with unit given by the monoid
  unit and tensor coequalizer projection". Eight ordinary ModuleCat results, including
  `ModuleCat.extendRestrictScalarsAdj` and its unit; these are not the general internal notion.
- `msearch.py ... loogle`: `CategoryTheory.Mod, CategoryTheory.Adjunction` — zero hits.
- `msearch.py ... grep`: `extendRestrictAdjunction|extendHomEquiv|extendUnit`, restricted to
  Mathlib `CategoryTheory` — zero hits.
- `msearch.py ... leansearch`: "Extension of scalars for internal module objects is left
  adjoint to restriction of scalars" — eight results, principally ordinary ModuleCat
  extension/restriction, not the general internal notion.
- `rg` over `lean/WeilConjectures/CategoryTheory/ModuleObjects` for
  `extendRestrictAdjunction|extendUnit|extendHomEquiv` found the exact existing construction
  in `ExtendScalars.lean`, lines 318–434, and consumers in `MapMod`,
  `ChangeOfScalarsSquare` and `DerivedExtendScalars`.
- `rg` over `lean/WeilConjectures` for the item's blueprint id found no hit.
  `rg` over `dag/lean_names_upstream.json` for `extendRestrictAdjunction` found no hit.
- `rg` over `lean/Sheaf/CategoryTheory` and
  `lean/WeilConjectures/Mathlib/CategoryTheory` for extension/adjunction names found consumers,
  notably `FlatScalarTowerCoherence`, which already uses the same upstream normalized unit.
  No alternative definition is introduced.

Validation: the prescribed delivery dry run compiles an automatically generated probe
importing the recorded module and checking the main declaration and every recorded helper
against the published live library. No new theorem or definition, and no new sorry, is added.

## Reading for delivery

The dispatcher brief assigns the independent review to the maintainer and prohibits starting
another agent. This is the worker's own final consistency reading, not an independent review:
I checked the node against the upstream source again. The forward equivalence uses the
specified coequalizer unit, not an arbitrary adjunction; both naturality fields are present;
the extension and restriction endpoints are literally the recorded dependency declarations.
No mismatch or statement change was found. The finite-shape preservation universe is already
part of the extension dependency's interface and requires no stronger hypothesis.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
