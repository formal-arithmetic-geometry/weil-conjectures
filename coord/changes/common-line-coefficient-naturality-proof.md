# SheafOfModules.CommonLine.exists_coefficientNaturality

## Reason

Complete the coefficient-naturality proof. The static visibility check flags the
new `open scoped`, `set_option`, and `attribute` commands even though the
attributes are explicitly local and all added helpers are private. This record
makes those commands available for independent review. No existing public
signature, definition body, visibility, or public import changes.

## Old

```lean
theorem exists_coefficientNaturality
    {B A D₀ D₁ D₀' D₁' : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c₀ : B ⟶ D₀} {c₁ : B ⟶ D₁}
    {φ : D₀ ⟶ D₁} {hφ : c₀ ≫ φ = c₁}
    {c₀' : B ⟶ D₀'} {c₁' : B ⟶ D₁'}
    {φ' : D₀' ⟶ D₁'} {hφ' : c₀' ≫ φ' = c₁'}
    (p : PositiveScalarPowers.{uC, vC, u, uI} a c₀ c₁ φ hφ)
    (p' : PositiveScalarPowers.{uC, vC, u, uI} a c₀' c₁' φ' hφ')
    (β₀ : D₀ ⟶ D₀') (β₁ : D₁ ⟶ D₁')
    (h₀ : c₀ ≫ β₀ = c₀') (h₁ : c₁ ≫ β₁ = c₁')
    (hβ : φ ≫ β₁ = β₀ ≫ φ') : Nonempty (CoefficientNaturality p p' β₀ β₁)
```

The body was `by sorry`. No proof-specific commands occurred between
`CoefficientNaturality` and this theorem.

## New

```lean
theorem exists_coefficientNaturality
    {B A D₀ D₁ D₀' D₁' : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c₀ : B ⟶ D₀} {c₁ : B ⟶ D₁}
    {φ : D₀ ⟶ D₁} {hφ : c₀ ≫ φ = c₁}
    {c₀' : B ⟶ D₀'} {c₁' : B ⟶ D₁'}
    {φ' : D₀' ⟶ D₁'} {hφ' : c₀' ≫ φ' = c₁'}
    (p : PositiveScalarPowers.{uC, vC, u, uI} a c₀ c₁ φ hφ)
    (p' : PositiveScalarPowers.{uC, vC, u, uI} a c₀' c₁' φ' hφ')
    (β₀ : D₀ ⟶ D₀') (β₁ : D₁ ⟶ D₁')
    (h₀ : c₀ ≫ β₀ = c₀') (h₁ : c₁ ≫ β₁ = c₁')
    (hβ : φ ≫ β₁ = β₀ ≫ φ') : Nonempty (CoefficientNaturality p p' β₀ β₁)
```

The body now constructs the normalized coefficient maps and their semilinear
power maps, proves the coefficient ring square by local tensor extensionality,
and proves the comparison square by induction. The following local elaboration
commands support this proof and its private helpers:

- `open scoped ChangeOfRings` opens existing scalar-extension notation.
- `set_option backward.isDefEq.respectTransparency false` permits the existing
  restriction and carrier wrappers to match during elaboration.
- Local `semireducible` and `irreducible` attributes for `siteSheafTensorRight`
  and `changeOfRingsOfUniverses` control unfolding while constructing maps, then
  keep subsequent equalities from expanding the sheafification implementation.
- Local `instance` registrations for the proved private theorems
  `coefficientUnit_surjective` and `commonUnit_surjective` supply the
  sheafification-unit local-surjectivity facts.
- Local `irreducible` attributes on six private map constructors control
  elaboration of the final naturality proof.

These commands do not install any global instance or reducibility attribute.
Every existing public signature and non-theorem body is preserved verbatim.
The four removed imports were private proof imports. No target statement or
mathematical definition changes, and no consumer adaptation is required.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CommonLinePositiveScalarPowers` | P6 | Coefficient-naturality proof completed; local proof elaboration commands and proved private helpers added. |

`tools/downstream.py Sheaf.Paper.CommonLinePositiveScalarPowers --uses
SheafOfModules.CommonLine.exists_coefficientNaturality` reports zero downstream
modules and only the declaration in the item itself. No consumer is adapted.
The still-unproved parent route and the item node remain present; zero current
importers is not used to withdraw any mathematical declaration or dependency.

## Status

landed 20261021T130107-L-2523886 2026-10-21 (merge of deliver/P6/Sheaf.Paper.CommonLinePositiveScalarPowers)
