## Worker report

Bind `def-sfb-modobj-extension` to the existing upstream definition
`CategoryTheory.Mod.extendScalars` in
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars` (line 304).
No Lean module is added: the prescribed one-definition rule requires reusing this construction.
Only the item's `lean` field changes. There are no new nodes, dependency repairs, statement
corrections, new proofs, or new sorries.

Source read: the complete item and its ten proof steps; the blueprint file
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/` 
`sk-def-sfb-change-of-scalars/def-sfb-modobj-extension.md`, order 1586.
The blueprint itself names `CategoryTheory.Mod.extendScalars`. Read upstream
`ExtendScalars.lean` (especially lines 81, 133–228, 271–308), including the docstrings and
actual definitions, and confirmed those portions against the live server with
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`.
The upstream file already implements the coequalizer construction, rather than selecting
an unspecified functor from an existence assertion.

Hypotheses, clause by clause:

- An arbitrary category is `{C : Type u} [Category.{v} C]`, with independent object and
  morphism universes (`universe v u`). The monoidal and braided structures are
  `[MonoidalCategory C] [BraidedCategory C]`; no symmetric structure is required.
- Coequalizers are `[HasCoequalizers C]`. Preservation of colimits by both tensor functors
  is `[∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]` and the corresponding
  `tensorRight` binder. These are Mathlib's small-diagram preservation assumptions used by
  `Bimod.tensorBimod`; in particular they cover the finite parallel-pair coequalizer and
  all tensorings used in the node's construction. No colimits in C other than the stated
  coequalizers are required to exist.
- Monoid objects and their morphism are `{R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S)
  [IsMonHom φ]`. Commutativity is `[IsCommMonObj R]`, solely on R. There is no commutativity
  requirement on S and no centrality requirement on the image of φ.

Construction, clause by clause:

- `CategoryTheory.Bimod.ofMonHom φ : Bimod (Mon.mk S) (Mon.mk R)` has `X := S`,
  `actLeft := μ[S]`, and `actRight := S ◁ φ ≫ μ[S]`. Its module laws use the monoid and
  monoid-morphism laws, exactly as the node's first proof step.
- `Mod.toBimodObj R M`, imported from the recorded symmetric-bimodule dependency, keeps
  `M.X`, gives the original left action `γ[R,M.X]`, and takes the right action to be
  `(β_ M.X R).hom ≫ γ[R,M.X]`. Thus the node's R-R bimodule is precisely the dependency's.
- `Mod.extendScalarsBimod φ M` is the actual tensor product
  `(Bimod.ofMonHom φ).tensorBimod (toBimodObj R M)`.
- `Mod.extendScalarsObj_X` identifies its underlying object definitionally with
  `coequalizer ((S ◁ φ ≫ μ[S]) ▷ M.X) ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X])`.
  The source of each arrow is `(S ⊗ R) ⊗ M.X`, the target is `S ⊗ M.X`, and their order
  is the order in the node. Lean composition `≫` writes the node's composition in
  chronological order. The chosen projection is `Mod.extendπ φ M`, and
  `Mod.isColimitExtendπ φ M` supplies exactly the coequalizer universal property.
- `Mod.extendScalarsObj φ M : Mod C S` uses the tensor bimodule's actual left action and
  its unitality/associativity proofs. `Mod.whiskerLeft_extendπ_smul` states
  `S ◁ extendπ φ M ≫ γ[S,(extendScalarsObj φ M).X] =
    (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ extendπ φ M`.
  This is exactly descent of multiplication of the first S factor.
- `Mod.extendScalarsMap φ f` is defined by `extendDesc` applied to
  `S ◁ f.hom ≫ extendπ φ N`. The equation `Mod.extendπ_extendScalarsMap` says
  `extendπ φ M ≫ (extendScalarsMap φ f).hom = S ◁ f.hom ≫ extendπ φ N`.
  It is therefore exactly the unique map induced by S tensor f, with S-linearity included
  in its type, rather than any arbitrary map between the coequalizers.
- Finally `Mod.extendScalars φ : Mod C R ⥤ Mod C S` has `obj := extendScalarsObj φ`,
  `map := extendScalarsMap φ`, and the functor identity/composition laws. Its literal
  declaration signature, omitting the delimiter `where`, is recorded verbatim in `lean`.

Dependency declarations read and used:

- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`, `IsModHom`, their action laws and category.
- `lem-sfb-modobj-symmetric-bimodules`:
  `WeilConjectures.CategoryTheory.ModuleObjects.Bimod`, `CategoryTheory.Mod.toBimodObj`,
  `toBimod`, `fullyFaithfulToBimod`, and `Bimod.IsSymmetric`. Read their full definitions;
  the scalar-extension definition directly uses `toBimodObj`.
- `sk-def-sfb-ring-object`:
  `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`, recorded
  `CategoryTheory.Functor.monObjCompForget₂` and its docstring. Its general notions are
  Mathlib `MonObj`, `IsMonHom`, `IsCommMonObj` in `Monoidal.Mon`, whose full signatures and
  laws were read and are used here. The sheaf/presheaf specialization is not needed for
  this entirely generic node.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, `Cocone`, `IsColimit`, and `colimit.desc`.
  Mathlib's `coequalizer` and `coequalizer.desc` specialize this to the parallel pair;
  `isColimitExtendπ` exposes that universal property in the upstream interface.

Edge cases checked by inspecting the construction and its hypotheses: φ may be an identity;
S need not be commutative; the braiding need not be symmetric; u and v remain independent;
no additive, abelian, zero-object, nonzero-ring, field, characteristic, or closed-category
assumption is imposed. In an additive example, the zero module and the zero algebra object
remain allowed. No empty family is implicitly required to be nonempty: the construction is
always the stated two-arrow coequalizer. No node fault or disputed statement was found.

Searches (2026-10-21):

- `msearch.py ... leanfinder "Extension of scalars for module objects over monoid objects
  by a coequalizer in a braided monoidal category"`: eight results, including internal
  `scalarRestriction`, regular modules, `Bimod.TensorBimod.X`, and `Bimod.tensorBimod`;
  no packaged internal extension functor in Mathlib.
- `msearch.py ... loogle 'CategoryTheory.Mod, "extendScalars"'`: zero hits.
- `msearch.py ... leansearch "Internal extension of scalars for module objects in a monoidal
  category using coequalizers"`: eight results, including concrete `ModuleCat.ExtendScalars.obj'`,
  internal module data and restriction, and concrete coextension; no exact Mathlib match.
- `msearch.py ... grep 'extendScalars|scalarExtension|coequalizer' CategoryTheory/Monoidal`:
  five displayed hits in `Bimod.lean`, concerning preserved coequalizers.
- `rg` of `extendScalars|scalarExtension|def-sfb-modobj-extension` in upstream CategoryTheory
  and Sheaf, then focused reads in upstream `CategoryTheory/ModuleObjects`, found the exact
  upstream `ExtendScalars.lean` definition and many existing consumers. A focused `rg -l`
  of `def extendScalars|def-sfb-modobj-extension` across both library roots confirmed it.
- `grep -rn 'def-sfb-modobj-extension' lean/WeilConjectures` found no blueprint-id comment;
  the exact match is established by the implementation, not by an id tag.

Validation: no delivered Lean files require compilation because this is an existing upstream
binding, as required by brief-stage2 §1. The live-source query succeeded and agrees with the
read clone. The prescribed delivery dry run performs the remaining server-side checks.

## Second reading by NA

I reread the node and the existing upstream definitions together after drafting the record.
This is a separate reading pass by the same worker; the dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent delivery review.

The category, braid, two tensor preservation hypotheses, coequalizers, R and S, φ, and
commutativity only of R agree with the node. In particular the definition does not accidentally
inherit the later `[IsCommMonObj S]` assumption from the scalar-composition section, nor the
later closedness/equalizer hypotheses from coextension. The two parallel arrows, their source
parenthesization, the canonical projection, descended left action, and descended morphism map
are exactly those displayed by the node. The right action on M is the recorded dependency's
braiding followed by its original left action. No new construction, extra hypothesis, missing
clause, statement correction, or declaration duplication was found; no revision was needed.
