## Worker report

This is an exact existing-declaration attachment. No Lean module is added, and no
proof is written. Bind `sk-d-trace` to `CategoryTheory.MonoidalCategory.trace` in
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`, branch `slopmaster2`.
Its source and complete docstring explicitly identify the blueprint `sk-d-trace`.
The current published source was also read with `scompile.py --source`; its defining
signature and body agree with the read-only slopmaster2 source.

Source checked: `literature/blueprint/main-20261015/blueprint/sec-trace-formula/` +
`sk-d-trace/_section.md`, definition at order 2617. The node and this unit agree.
There is no repair note for this item. No statement correction, new definition node,
or dependency repair is needed. The node copy changes only `lean`.

The existing declaration, including its surrounding context, is:

```lean
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
noncomputable def trace {X : C} [HasRightDual X] (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ
```

The record's `statement` is the verbatim signature beginning at `def`, following
the project's signature convention. All parameters are bound by the displayed
context or declaration; the existing general object and morphism universes are
not identified or restricted by this attachment.

Each hypothesis and clause corresponds as follows:

| Node text | Lean rendering |
| --- | --- |
| A braided monoidal category C | `{C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]` |
| Its unit 1 | `𝟙_ C` |
| P has a specified right dual P-dual | `{X : C} [HasRightDual X]`, with right dual `Xᘁ` |
| Coevaluation 1 to P tensor P-dual | `η_ X Xᘁ : 𝟙_ C ⟶ X ⊗ Xᘁ` |
| Evaluation P-dual tensor P to 1 | `ε_ X Xᘁ : Xᘁ ⊗ X ⟶ 𝟙_ C` |
| An endomorphism v of P | `(f : X ⟶ X)` |
| v tensor identity of the dual | Right whiskering `f ▷ Xᘁ` |
| sym is the forward braiding | `(β_ X Xᘁ).hom` |
| The four-arrow composite in that order | `η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ` |
| The result belongs to End(1) | Return type `𝟙_ C ⟶ 𝟙_ C` |

`Mathlib.CategoryTheory.Monoidal.Rigid.Basic` was read at `ExactPairing`,
`ExactPairing.coevaluation`, `ExactPairing.evaluation`, and `HasRightDual`.
`HasRightDual` contains the chosen object and an exact pairing with both triangle
identities. Thus the source's duality datum is supplied, rather than replaced by
unconstrained evaluation and coevaluation maps. An arbitrary given right dual can
be installed in this structure; this does not restrict which duality is permitted.

The final paragraph is the application of this same definition to perfect complexes,
not a second general trace. Its concrete scalar-valued implementation already exists:
`DerivedCategory.perfectCategoricalTrace` in
`Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace`, owned by the landed
node `def-trf-categorical-trace`. Its signature is

```lean
noncomputable def perfectCategoricalTrace (P : DerivedCategory (ModuleCat.{u} R))
    (hP : IsPerfectRingComplex P) (v : P ⟶ P) : R
```

with surrounding `{R : Type u} [CommRing R]` and
`[HasDerivedCategory.{u} (ModuleCat.{u} R)]`. This is general in the commutative ring,
even though that module also provides a further finite-coefficient specialization.
Its body installs `perfectTraceCanonicalBraiding (ModuleCat R)` and
`perfectTraceHasRightDual P hP`, then returns
`perfectTraceScalar (MonoidalCategory.trace v)`. The following existing declarations
in that module realize each remaining clause of the node:

| Perfect-complex clause | Existing Lean implementation |
| --- | --- |
| P lies in Perf(R) | `hP : DerivedCategory.IsPerfectRingComplex P`; the full subcategory is `perfectTraceCategory R` |
| The tensor is the derived tensor, with unit R | The existing monoidal structure on `DerivedCategory (ModuleCat R)` and `singleFunctorObjUnitIso` |
| The dual is RHom(P,R) | `perfectTraceDual P := (ihom P).obj (𝟙_ _)` |
| Evaluation and coevaluation give its duality | `perfectTraceEvaluation`, `perfectTraceCoevaluation`, and `perfectTraceHasRightDual` |
| Symmetry for derived tensor | `perfectTraceCanonicalBraiding`, descended from the signed complex symmetry |
| End of the unit is identified with R | `perfectTraceScalar`, inverse of the fully faithful degree-zero Hom map followed by evaluation at 1; `perfectTraceScalarInverse` sends a scalar to multiplication by it |
| tr_R(v given P) lies in R | `perfectCategoricalTrace P hP v : R`, using the attached general trace |

Computing the trace in the ambient derived category agrees with computing it in
its full perfect subcategory: the object, four structural arrows, their composites,
and the endomorphisms of the unit are the same. The scalar trace is therefore
already available; writing another definition would violate one-definition-per-notion.
No extra hypothesis on R, its characteristic, or finite-dimensionality is introduced.

Dependency read: `sk-d-setup`, recorded declaration
`WeilConjectures.TraceFormulaCoefficientSetup` in
`Sheaf.Paper.TraceFormulaCoefficientSetup`; its full signature and docstring were
read. Its final convention for Perf(R) uses
`DerivedCategory.IsPerfectRingComplex`, module
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`, whose full
predicate was also read: isomorphism to a bounded cochain complex of finitely
generated projective modules. The geometric coefficient setup is not a parameter
of the generic categorical trace; the node itself quantifies over an arbitrary
braided category and an arbitrary commutative ring. No copy of any dependency is
introduced. Since no new module is written, no import additions are necessary.

Edge cases checked from the definition and its interfaces:

- A merely braided category is allowed: the arrow is the forward braiding hom,
  not the inverse opposite braiding, and no symmetry or pivotal structure is assumed.
- Only the chosen object needs a right dual; the category need not be rigid and
  no left dual or closed-category structure is required for the generic definition.
- The unit object and its identity endomorphism are admissible; there are no
  additive, nonzero, positivity, or finite-dimensional hypotheses on C or X.
- The zero perfect complex, any shift, the zero ring, and rings of any characteristic
  are not excluded. The existing scalar implementation uses the signed braiding,
  so it does not discard the signs for shifted complexes.
- Arbitrary endomorphisms are accepted; no identity or invertibility requirement
  is silently imposed on v.

Searches made, with msearch.py group Q49 and item sk-d-trace:

- LeanFinder: “Categorical trace of an endomorphism in a braided monoidal category
  with a dual is coevaluation followed by tensor endomorphism braiding evaluation”.
  Repeated with “Trace of an endomorphism of a right dualizable object in a braided
  monoidal category, defined using coevaluation and evaluation”. The latter returned
  eight hits, including `ExactPairing.evaluation`, `ExactPairing.coevaluation`, and
  tensor-Hom duality identities; these supply components, not the general trace.
- Loogle: `CategoryTheory.MonoidalCategory.trace, CategoryTheory.BraidedCategory,
  CategoryTheory.ExactPairing`; zero hits, unknown trace identifier in Mathlib's
  index. This does not contradict the upstream match outside Mathlib.
- LeanSearch: “Categorical trace of an endomorphism of a dualizable object in a
  braided monoidal category”; eight hits, including `BraidedCategory` and unrelated
  commutative comonoid/Dialectica constructions, no exact trace.
- Mathlib grep through msearch.py: `def trace|categorical trace|HasRightDual` in
  `CategoryTheory/Monoidal`; fifteen hits concerning right duals and their transport,
  no trace definition. Direct rg for `def trace|categorical trace` in that directory
  likewise found no categorical trace.
- Direct rg in `WeilConjectures/` for `def trace|categorical trace|def.*Trace|sk-d-trace`
  found the exact definition in the upstream rigid braided module at line 74.
  The specific `sk-d-trace` search found its declaration docstring at line 73
  (and the separate `sk-d-trace-class` string in trace pairing).
- Direct rg with the same patterns in `lean/Sheaf` found
  `Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace`; the entire file
  and its owning DAG node were read to check the scalar specialization.
- `dag/lean_names_upstream.json` associates `sk-d-trace` exactly with
  `CategoryTheory.MonoidalCategory.trace`. The node's own upstream audit also
  names that definition with no sorry.

Validation: the required `deliver2.py Q49 sk-d-trace --no-push` will run the
existing-declaration `#check` through scompile.py, plus server preflight. There is
no delivered Lean file to compile separately. Independent second reading is left
to the dispatcher-appointed second reader; no second-reading section is authored here.

## Second reading by Q49

I opened the node copy at `dag/nodes/sec-trace-formula/sk-d-trace.json`, the
blueprint source `sec-trace-formula/sk-d-trace/_section.md` (order 2617), and the
published source module `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`.
The node is a definition and its `blueprint_lean` entry names
`CategoryTheory.MonoidalCategory.trace`. The existing declaration is therefore the
right attachment; no new module is warranted.

The node's objects, hypotheses, and conclusion match as follows.

- The braided monoidal category and its unit are rendered by the source context
  `{C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]` and by
  `𝟙_ C`. This permits arbitrary category and object universes represented by the
  upstream `Type*`; it adds no symmetry, rigidity of all objects, additive
  structure, or ring hypothesis. PASS.
- The object `P`, its selected right dual `P^vee`, and the duality maps are rendered
  by `{X : C} [HasRightDual X]`, with `Xᘁ`, `η_ X Xᘁ : 𝟙_ C ⟶ X ⊗ Xᘁ`, and
  `ε_ X Xᘁ : Xᘁ ⊗ X ⟶ 𝟙_ C`. `HasRightDual` was opened in the upstream rigid
  basic module: it supplies a chosen right-dual object and an `ExactPairing`, so
  the coevaluation and evaluation satisfy the required triangle identities.
  PASS; no left dual or closedness is assumed.
- The endomorphism `v : P ⟶ P` is `(f : X ⟶ X)`. The arrow `v ⊗ 1` is exactly
  `f ▷ Xᘁ`, the right whiskering used by the source. PASS.
- The middle symmetry is the forward braiding, exactly `(β_ X Xᘁ).hom`, whose
  type is `X ⊗ Xᘁ ⟶ Xᘁ ⊗ X`. The declaration uses the hom, not the inverse.
  PASS for a merely braided category.
- The conclusion is the ordered composite
  `η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ`, with return type
  `𝟙_ C ⟶ 𝟙_ C`. This is exactly the displayed element of `End(𝟙)`; no
  equality or property is added. PASS.
- The source's `Perf(R)` paragraph is represented by the declaration docstring's
  explicit `(Perf R, ⊗ᴸ_R, R)` specialization and by the existing
  `DerivedCategory.perfectCategoricalTrace` in
  `Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace`. Its
  `perfectTraceDual` is `(ihom P).obj (𝟙_ _)` (derived RHom into `R`),
  `perfectTraceHasRightDual` supplies the canonical duality, and
  `perfectTraceScalar` identifies `End(R[0])` with `R`; the resulting definition
  is `perfectTraceScalar (MonoidalCategory.trace v)`. This has the source's
  symmetric derived-tensor specialization and introduces no finite-dimensional,
  characteristic, or nonzero assumption. PASS.

Edge cases checked: the zero endomorphism and zero perfect complex use the same
composite; the tensor unit and its identity are allowed; an empty or trivial
category is not excluded by the generic declaration; the zero ring and arbitrary
characteristic are allowed by the scalar specialization; shifts retain the signed
derived braiding; and no finite-index, positivity, or invertibility condition on
`f` occurs. `HasRightDual` is required only for the selected object, so categories
without global rigidity remain covered. Universe variables are not identified.

Independent searches were made in addition to the worker's log. `rg` in
`WeilConjectures/` found the exact declaration and its `(blueprint: sk-d-trace)`
docstring at lines 62--75 of the upstream module. `rg` in Mathlib's monoidal rigid
directory found right-dual infrastructure but no categorical trace definition.
`rg` in `lean/Sheaf` found only the already-owned scalar specialization
`perfectCategoricalTrace`. LeanFinder searches for a braided right-dual trace
returned pairing and tensor-Hom lemmas, with no exact declaration; Loogle's exact
identifier search returned no indexed Mathlib declaration. I also ran
`scompile.py --source WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`;
the current published source has the same trace signature, body, and blueprint tag.

No mismatch was found, so no Lean source or statement text was changed. The only
delivery change is retaining the existing-declaration `lean` record for
`CategoryTheory.MonoidalCategory.trace` with branch `slopmaster2`; the dependency
`sk-d-setup` is used only as the paper's ambient coefficient convention and needs
no copied definition or repair.
