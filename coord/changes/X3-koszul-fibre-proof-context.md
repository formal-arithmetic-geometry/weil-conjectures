# Sheaf.CategoryTheory.KoszulFibreLinearDescent proof context

## Reason

The original theorem has one hole. Its full proof constructs the signed product
fibre, tensor and product homotopies, and the additive linear localization. Private
helpers need monoidal notation, generic category variables, and explicit transparency
settings for the selected tensor and cochain structures. The static interface check
records the additional section commands even though the existing public declarations
and public imports are byte-for-byte unchanged. No target meaning changes.

## Old

After the existing proposition, the file goes directly to the docstring and theorem
`CategoryTheory.koszulFibreLinearDescent`. There are no proof-helper sections,
`MonoidalCategory` open command, generic category variables, or helper instances.
The existing commands are preserved verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
```

## New

The existing public definitions, proposition, theorem signature and docstrings are
unchanged. The coefficient-action public import is narrowed from
`Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` to
`Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions`. F2 already relocated
`scalarLocalizationCoefficientLinear` verbatim to that lower module; the old module
only re-exports it. The item uses none of the derived-Hom comparison declarations.
This avoids importing that comparison and its telescope proof solely for a coefficient
action. No downstream Lean module imports this item, so no consumer adaptation is needed.
The node already cites the lower coefficient-action definition node.

Old import:
```lean
public import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
```
New import:
```lean
public import Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions
```

The following proof sections are inserted before
the theorem; their helpers are private and proved, with no holes:

```lean
section FibreConstruction
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MonoidalCategory
end FibreConstruction
section ProductHomotopy
variable {C : Type*} [Category C] [Abelian C] [HasCountableProducts C]
  {M N : ℕ → CochainComplex C ℤ} {f g : ∀ n, M n ⟶ N n}
end ProductHomotopy
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section SignedHomotopy
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
end SignedHomotopy
```

The private instances `CategoryTheory.fibreBiproducts`,
`CategoryTheory.fibreFunctor_linear` and `CategoryTheory.fibreFunctor_additive`
supply the canonical biproduct structure from finite products and the proved
linearity/additivity of the private fibre functor. Their full statements and bodies
are in the delivered module. They add no mathematical assumptions or public API.
The private `homotopy_eqToHom` lemma omits the unused biproduct hypothesis and has
an automatically proved reassociation lemma. The other private reassociation lemmas
only rewrite product projections and equality transports.

The resumed compile profile showed repeated elaboration of the sheaf composition,
abelian category, countable products and derived-category instance in private helpers.
The private instances `fibreHasSheafCompose`, `fibreAbelian`, and
`fibreCountableProducts` cache the already inferred structures. `PublishedData` scopes
the original derived-category section variable to the public specification;
`FibreQuasiIso` introduces that same instance only around the three helpers that use
the fixed-derived-tensor theorem. It is reintroduced before the original final theorem.
The other private helpers are constructions on cochain complexes and need no derived
category. Explicit universe annotations on the private `forget₂` applications remove
universe search. The three cached instances are disabled before elaborating the final public theorem,
so its signature uses the original public structures. These are elaboration changes,
with no extra hypothesis or data choice.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.KoszulFibreLinearDescent --uses
koszulFibreLinearDescent KoszulFibreLinearDescentData` reports zero downstream
modules; the two names occur only in this item. No consumer adaptation is required.
DAG parents with unfinished proofs keep the same published statement and unit route.
Neither adopted source modules nor another group's modules are changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.KoszulFibreLinearDescent | X3 | Private proof context; coefficient import narrowed; one hole closed. |

## Status

landed 20261021T214919-L-1890729 2026-10-21 (merge of deliver/X3/Sheaf.CategoryTheory.KoszulFibreLinearDescent)
