## Worker report

The module `Sheaf.CategoryTheory.ModuleObjectCokernelAction` states
`CategoryTheory.Mod.exists_cokernel_action`, with `sorry` as its sole proof.
It introduces no definitions. The item's natural-language statement, dependencies,
and proof are unchanged; only its `lean` record is added.

Sources read: the complete item and its seven proof steps; the current
main-20261015 blueprint files
`sec-proetale-coefficients/sk-prop-sfb-module-category/lem-sfb-modobj-cokernels.md`
and `lem-sfb-modobj-cokernels.proof.md`; and the complete statement and Lean record
of `sk-def-sfb-module-objects`. No repair note exists for this item. The example
`Sheaf.CategoryTheory.CompactObject` is now withdrawn; its node records the identical
upstream `CategoryTheory.IsCompactObject`, so the new file follows the current
`module` / `public import` / exposed public section conventions.

Hypotheses and clauses, in order:

- An arbitrary preadditive monoidal category is `{C : Type u}`,
  `[Category.{v} C] [MonoidalCategory C] [Preadditive C]`. Object and morphism
  universes are independent and explicitly bound.
- Additivity of tensor product in each variable is `[MonoidalPreadditive C]`.
  Its `whiskerLeft_add`, `add_whiskerRight` and zero equations are precisely the
  additivity assumptions, with no symmetry or abelianness assumption.
- The monoid object is `{R : C} [MonObj R]`.
- Preservation of finite colimits by `R ⊗ -` is
  `[PreservesFiniteColimits (tensorLeft R)]`. This is preservation of existing
  colimits, and adds no `HasFiniteColimits C` or `HasCokernels C` assumption.
- The module objects and their module morphism are `{M N : Mod C R}` and
  `(f : M ⟶ N)`, using the dependency's recorded `CategoryTheory.Mod` verbatim.
- A supplied underlying cokernel consists of `{Q : C}`, `(π : N.X ⟶ Q)`,
  `(w : f.hom ≫ π = 0)` and
  `(hπ : IsColimit (CokernelCofork.ofπ π w))`. The equation and cofork universal
  property unpack the statement that the given `π` is a cokernel; they are not
  additional mathematical hypotheses.
- The conclusion supplies `∃ (a : ModObj R Q)`. Its action map `a.smul` has type
  `R ⊗ Q ⟶ Q`, and its fields `one_smul` and `mul_smul` express the two action
  axioms of the dependency node. Thus this existential includes exactly the
  assertion that the induced map is an action.
- The displayed compatibility equation is
  `R ◁ π ≫ a.smul = ModObj.smul (M := R) (X := N.X) ≫ π`.
  Lean composes from left to right; the node writes ordinary function-style
  composition from right to left.
- Uniqueness is explicitly among **all** underlying maps, not just actions:
  `∀ (γ : R ⊗ Q ⟶ Q), R ◁ π ≫ γ =
  ModObj.smul (M := R) (X := N.X) ≫ π → γ = a.smul`.
  Together with the preceding existence equation this is unique existence of
  the morphism stated in the node.
- The induced module object is `({ X := Q, mod := a } : Mod C R)`; the conclusion
  gives a morphism `p` from `N` to this very object with `p.hom = π`. Its
  `IsModHom` structure is exactly the required linearity of the supplied
  projection. No arbitrary replacement for the underlying projection is used.
- Finally `∃ (wp : f ≫ p = 0),
  Nonempty (IsColimit (CokernelCofork.ofπ p wp))` says this projection is a
  cokernel in the module category. `Nonempty` turns the data-valued
  `IsColimit` structure into a proposition without losing its universal
  property. The equation is the required zero composite of that cofork.

Dependency declarations and source interfaces read:

- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.ModObj`,
  `CategoryTheory.Mod`, `CategoryTheory.Mod.Hom`, `CategoryTheory.Mod.forget`,
  `CategoryTheory.Mod.regular`. Read the full signatures and docstrings:
  the actions and their unit/associativity laws, action-compatible underlying
  morphisms, their category structure, forgetful functor and regular module.
  This is the recorded module for `sk-def-sfb-module-objects`, which is both
  the statement dependency and the sole proof dependency. The pro-etale
  specialization in that node is not needed for this generic lemma.
- `Mathlib.CategoryTheory.Monoidal.Preadditive`:
  `CategoryTheory.MonoidalPreadditive` gives additivity in both variables.
- `Mathlib.CategoryTheory.Limits.Preserves.Finite`:
  `CategoryTheory.Limits.PreservesFiniteColimits` gives the finite-colimit
  preservation hypothesis.
- `Mathlib.CategoryTheory.Limits.Shapes.Kernels`:
  `CategoryTheory.Limits.CokernelCofork`, `CokernelCofork.ofπ`, and `IsColimit`
  encode the supplied and resulting cokernel universal properties.
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` is publicly imported
  for the existing preadditive/zero-morphism structure on `Mod C R`, needed
  to type its cokernel. That section requires only preadditivity and tensor
  additivity; its later abelian-category section imposes no hypotheses here.

Searches run on 2026-10-21:

- `msearch.py` LeanFinder, query: "Cokernel of a morphism of module objects in a
  monoidal category has a unique induced action when tensoring preserves finite
  colimits". Eight hits, all ordinary ring-module results such as
  `ModuleCat.cokernelCocone`, `ModuleCat.cokernelIsColimit` and
  `ModuleCat.hasCokernels_moduleCat`; no exact abstract module-object statement.
- `msearch.py` Loogle, query:
  `CategoryTheory.Mod, CategoryTheory.Limits.CokernelCofork`. Zero hits.
- `msearch.py` grep, query `cokernel|Cokernel|CreatesColimit`, subdirectory
  `CategoryTheory/Monoidal`. Five hits, all in
  `Mathlib/CategoryTheory/Monoidal/Limits/Cokernels.lean`; these concern tensor
  products of existing cokernel coforks, not induced module actions.
- `msearch.py` LeanSearch, query: "An underlying cokernel of a morphism of module
  objects has a unique induced module action and is a cokernel in the category
  of module objects". Eight hits: ordinary `ModuleCat` cokernels, the general
  category-theoretic cokernel definition, `TopModuleCat.isColimitCoker`, and
  `Module.Presentation.nonempty_cokernelData`; no exact match.
- `rg` on the project `WeilConjectures` and `Sheaf` source trees for the item id,
  `isColimitCokernelCofork`, cokernel/module combinations, `cokernelSMul` and the
  proposed declaration name. Read the matching upstream
  `WeilConjectures.CategoryTheory.ModuleObjects.Abelian` cokernel section in full.
  `cokernelSMul`, `π_cokernelSMul`, `cokernelObj`, `cokernelπ`, `cokernelCofork` and
  `isColimitCokernelCofork` construct and use the *chosen* underlying cokernel.
  They do not state the present assertion for a supplied `Q, π`, nor its
  explicit uniqueness among all raw action maps. The new theorem states that
  interface without duplicating any of those definitions. The only occurrence
  of the node id in the project sources is a proof-plan reference in
  `Sheaf.CategoryTheory.ModuleObjects.LiftExact`.
- `rg` in Mathlib's `Monoidal/Mod.lean` for cokernels and the upstream declaration
  index for `exists_cokernel_action`, `isColimitCokernelCofork`, `cokernelSMul`:
  no matches. Checked the complete `ModObj`, `Mod` and morphism signatures
  directly; the Mathlib module was also read using `scompile.py --source`.
- `rg` in `coord/repair-notes` for the item id found no repair note.

Edge cases checked before drafting:

- The zero morphism `f = 0` permits the identity of `N.X` as supplied cokernel;
  the factorization forces exactly the original action. Nothing excludes it.
- For an isomorphism `f` and an existing zero cokernel, the unique zero-object
  action and cokernel are allowed; no nonzero-object requirement appears.
- A general preadditive category need not have any other cokernels, finite
  sums, a zero object, or be abelian. Only the given cofork and preservation
  of existing finite colimits are used; no ambient existence instances occur.
- The argument permits noncommutative monoid objects and a nonsymmetric
  monoidal category. The statement imposes neither commutativity nor symmetry.
- A cokernel object is arbitrary and need not be definitionally Mathlib's
  chosen `cokernel f.hom`; the action and projection refer to that exact `Q, π`.
- Different object and morphism universes are retained. There is no index set,
  characteristic restriction or coefficient-size restriction.

The seven-step proof docstring follows the node's expanded proof, including
preserving this cokernel twice to justify associativity cancellation. It does
not infer preservation of arbitrary epimorphisms from finite-colimit preservation.
The older blueprint proof's wording makes that inference, but the node's
expanded proof already repairs it and the statement itself needs no correction.
There is no statement dispute and no new or repaired dependency node.

Validation: `scompile.py Q153 lem-sfb-modobj-cokernels` compiled this file in
both the isolated sandbox and its library module context, with no errors or
warnings (0.9 s and 1.0 s respectively). Every variable and universe is explicitly
bound. The declaration's proof is exactly `by sorry`.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
