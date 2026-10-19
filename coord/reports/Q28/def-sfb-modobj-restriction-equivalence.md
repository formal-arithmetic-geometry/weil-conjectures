## Worker report

Recorded the existing definition `CategoryTheory.Mod.comapEquivalenceOfIsIso` in
`WeilConjectures.CategoryTheory.ModuleObjects.MapMod` (published side-project framework,
source lines 158–171). No Lean module is delivered and no other node is stated or changed.
Only the item's `lean` record changes. The record's signature is verbatim from the source:

```lean
noncomputable def comapEquivalenceOfIsIso : Mod C S ≌ Mod C R
```

Sources read: the entire node and all three statement dependencies; their full Mathlib
matches and the corresponding declarations/docstrings; the current main-20261015
blueprint item statement and proof; `coord/pefw-upstream-framework.md`; and the complete
published `MapMod` source, independently retrieved with
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.MapMod`.
There is no repair note for this item.

### Hypotheses and clauses

- Ambient category: `{C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]`, with object
  and morphism universes independent. The self left action is Mathlib's tensor action,
  so `Mod C S` and `Mod C R` are exactly internal left-module categories in C.
- Braiding: `[BraidedCategory C]` is in the declaration's source section.
- Closedness: `[MonoidalClosed C]` is in that same section.
- Equalizers and coequalizers: `[HasEqualizers C]` and `[HasCoequalizers C]` are there.
- Tensor preserving colimits on both sides: the source section has
  `[∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]` and the corresponding
  `tensorRight` instance. These are implied by the node's stated preservation of colimits.
- Monoid objects: `{R S : C} [MonObj R] [MonObj S]`.
- Commutativity of R: `[IsCommMonObj R]` is in the source section; there is no assumption
  of commutativity on S.
- The morphism and its invertibility: `(φ : R ⟶ S) [IsMonHom φ] [IsIso φ]`. This is an
  isomorphism of monoid objects: the Mathlib inverse-monoid-hom instance gives
  `IsMonHom (asIso φ).inv` from the two inverse identities and the monoid-hom equations.
- Restriction in the stated direction: the result is `Mod C S ≌ Mod C R` and the
  constructor's forward functor is literally `Mod.comap φ`, using the dependency's
  recorded Mathlib definition, not another restriction operation.
- The specified quasi-inverse: its inverse field is literally
  `Mod.comap (asIso φ).inv`, from R-modules to S-modules.
- Equivalence: `Equivalence.mk` bundles the two functors and natural isomorphisms.
  Its unit is `(comapId S).symm ≪≫ comapCongr (by simp) ≪≫
  comapComp (asIso φ).inv φ`. Its counit is
  `(comapComp φ (asIso φ).inv).symm ≪≫ comapCongr (by simp) ≪≫ comapId R`.
  These give the two composites isomorphic to their respective identity functors;
  the standard constructor supplies the adjoint-equivalence coherence.

The compiler's `#check @CategoryTheory.Mod.comapEquivalenceOfIsIso` and `#print` confirm
that Lean drops all the unused section hypotheses from this definition's elaborated
type: it actually needs only the monoidal category, the two monoid structures, the
monoid morphism and its invertibility. This existing, more general construction is used
by direct specialization under every hypothesis of the node; no different construction
or weakened conclusion is substituted. The blueprint's own proof explicitly says that
only invertibility is used. All braiding/closedness/limit/colimit/commutativity assumptions
remain verbatim in the DAG statement, which is unchanged. No statement correction is needed.

### Dependency declarations used

All three direct statement dependencies are Mathlib leaves and therefore correctly have
no `lean` record. Their recorded `mathlib_match` declarations are used unchanged:

- `def-sfb-modobj-restriction`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod.comap` (403–410), `scalarRestriction` (363–377) and
  `scalarRestriction_hom` (387–395). The action is `φ ▷ N.X ≫ γ[S,N.X]`, and underlying
  objects and morphisms are literally retained.
- `det-def-sfb-ring-object-monoid`: `Mathlib.CategoryTheory.Monoidal.Mon`,
  `CategoryTheory.MonObj`, `Mon`, `IsMonHom`, `Mon.Hom`, `Mon.id`, `Mon.comp`,
  `Mon.instCategory`, `Mon.forget`, `Mon.forget_faithful`, and `IsCommMonObj`.
  Their full object, morphism, category and commutativity clauses were read, including
  the existing instance that the inverse of a monoid isomorphism is a monoid homomorphism.
- `det-def-sfb-module-objects-definition`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.ModObj`, `IsModHom`, `ModObj.regular`, `Mod`, `Mod.Hom`, `Mod.id`,
  `Mod.comp`, `Mod.instCategory`, `Mod.regular`, and `Mod.forget`.
  `Mathlib.CategoryTheory.Monoidal.Action.Basic`'s `selfLeftAction` identifies its
  monoidal action with tensoring in C, with the stated associator and unitors.

Supporting existing comparison declarations `Mod.comapId`, `Mod.comapComp` and
`Mod.comapCongr` were read in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`
(lines 356–387). They have identity underlying component isomorphisms and express
precisely the two composite action computations in the DAG proof. The source's
`Equivalence.mk` uses these actual natural isomorphisms, not a mere arbitrary choice of
an equivalence or an unspecified inverse.

### Edge cases

Checked identity φ (both restrictions recover the identity via `comapId`), an arbitrary
invertible monoid morphism (inverse is monoid-linear without a new assumption), and
noncommutative S (the definition does not impose commutativity on S). The construction
uses no abelian/additive structure, no zero object, no nonempty index family, and no
finite/nontrivial coefficient assumption. A degenerate category or unit monoid is not
excluded. Distinct object/hom universes are retained; `Mod C R` naturally lives in
`Type (max u₁ v₁)`, so no smallness or universe equality is imposed.

### Searches

All Mathlib service searches below were run with the prescribed `msearch.py Q28
 def-sfb-modobj-restriction-equivalence` wrapper (the tool logs carry the exact results).

- `leanfinder`: “Restriction of scalars along an isomorphism of monoid objects in a
  monoidal category is an equivalence with inverse restriction along its inverse”.
  Eight hits: `Action.resEquiv_inverse`, `CategoryTheory.MonObj.ofIso`,
  `ModuleCat.restrictScalars_isEquivalence_of_ringEquiv`, `CategoryTheory.Mon.mkIso'`,
  `Action.resEquiv`, `Action.resEquiv_functor`, `CategoryTheory.Mon.mkIso_hom_hom`,
  `CategoryTheory.Mon.mkIso`. None gives the internal-module construction in Mathlib.
- `loogle`: `CategoryTheory.Mod.comapEquivalenceOfIsIso, CategoryTheory.Mod.comap`.
  Zero hits, with unknown identifier `CategoryTheory.Mod.comapEquivalenceOfIsIso`.
- `grep`: `comapEquivalence|comap.*[Ii]so|comap.*[Ee]quivalence`, subdirectory
  `CategoryTheory/Monoidal`. Zero Mathlib hits.
- `leansearch`: “Restriction of scalars along an isomorphism of internal monoid
  objects is an equivalence of module object categories”. Eight hits, led by
  `ModuleCat.restrictScalars_isEquivalence_of_ringEquiv` and
  `CategoryTheory.Mod_.scalarRestriction`; other hits include `Mod_.comap`, ordinary
  ModuleCat restriction/equivalence and `LinearEquiv.restrictScalars`. The ordinary
  ring constructions do not replace arbitrary internal modules.
- Project `rg -n` by name and concept in the read-only slopmaster2 `WeilConjectures`,
  project `lean/Sheaf`, and published `lean/WeilConjectures` found the exact construction
  at `lean/WeilConjectures/CategoryTheory/ModuleObjects/MapMod.lean:168`.
  The old slopmaster2 checkout and `dag/lean_names_upstream.json` do not contain it;
  the published side overlay does. `rg` over the DAG confirms the blueprint already
  names this exact declaration and the adjacent extension/coextension nodes cite it.
  There is no second Sheaf definition to reuse.

### Validation

`scompile.py --source` confirmed the current published source. A scratch probe importing
only `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`, with `autoImplicit false`,
`#check @CategoryTheory.Mod.comapEquivalenceOfIsIso` (universes printed), and `#print`
compiled cleanly through the required `scompile.py Q28 def-sfb-modobj-restriction-equivalence`
wrapper, including server confirmation. The scratch file is outside `lean/` and is not
delivered. The delivery dry run additionally checks the existing declaration and runs
the server preflight. No proof was written or changed.

## Second reading by Q28

I independently matched the node statement clause by clause against the published
declaration `CategoryTheory.Mod.comapEquivalenceOfIsIso` in
`WeilConjectures.CategoryTheory.ModuleObjects.MapMod`.

- The ambient object is a braided monoidal closed category with equalizers and
  coequalizers, and both tensor sides preserve colimits. These are the source section
  hypotheses and are exactly the hypotheses written in the node.
- The monoid objects `R` and `S`, commutativity instance on `R`, morphism
  `φ : R ⟶ S`, `IsMonHom φ`, and `IsIso φ` match the node's two monoids and isomorphism.
  No commutativity of `S` is introduced.
- The conclusion has the exact direction `Mod C S ≌ Mod C R`; its forward functor is
  `Mod.comap φ`, and its inverse is `Mod.comap (asIso φ).inv`, precisely the two
  restriction functors in `[def-sfb-modobj-restriction]`.
- The unit and counit are the canonical `comapId`, `comapCongr`, and `comapComp`
  composites in `Equivalence.mk`, giving the requested categorical equivalence.

The compiler `#check`/`#print` showed the elaborated declaration and all universes;
unused section assumptions are dropped by Lean but remain valid ambient hypotheses of
the node. Identity `φ`, degenerate/unit monoids, noncommutative `S`, empty or zero
objects, and distinct object/morphism universes are all covered. No index, finiteness,
characteristic, or nonzero assumption is present in either statement.

The required searches were checked again: grep over Mathlib and project sources,
Loogle for `CategoryTheory.Mod.comapEquivalenceOfIsIso`, LeanFinder and LeanSearch
for internal-module restriction equivalences. They found only `Mod.comap` and
ordinary `ModuleCat`/action equivalences; the published `MapMod` declaration is the
unique exact match. The three dependency records are Mathlib matches and render the
restriction, monoid-object, and module-object notions used here.

One metadata mismatch was found: the node's `lean.statement` included the keyword
`noncomputable`, while preflight compares it with the source signature beginning
`def`. I changed only that record value to the verbatim source signature
`def comapEquivalenceOfIsIso : Mod C S ≌ Mod C R`; no Lean declaration or node
statement was changed.
