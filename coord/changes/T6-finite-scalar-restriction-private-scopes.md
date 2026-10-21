# AlgebraicGeometry.Scheme.proEtaleFiniteScalarRestriction_constructible

## Reason

The stage-3 interface checker conservatively flags the additional universe names and
`section`/`variable`/`include` commands used for a proved private sheafification helper.
This records those commands explicitly. They introduce no public data, declarations,
instances, attributes, notations, or statement changes. The `variable` block ends before
all public theorems; `include comm in` applies only to the following private theorem.
The extra universe names occur only in private helpers. Every existing public theorem
signature and public import is textually identical to the source, despite reordering
the declarations to put the two witness lemmas before the main theorem.

## Old

```lean
universe u
```

There was no private generic-helper section; all three public theorem proofs were
`by sorry`. Their full signatures are unchanged.

## New

```lean
universe u v w t
```

The new private helper uses this lexical scope, which is closed before the
pro-etale specializations and public theorems:

```lean
section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ S₀ : Cᵒᵖ ⥤ RingCat.{w}} {R S : Sheaf J RingCat.{w}}
  (α : R₀ ⟶ R.obj) (β : S₀ ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  (a₀ : R₀ ⟶ S₀) (a : R ⟶ S) (comm : α ≫ a.hom = a₀ ≫ β)
  (P : _root_.PresheafOfModules.{t} S₀)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include comm in
```

`scalarRestrictionSheafification` is a fully proved private theorem in this section.
The two options are declaration-scoped, as are the analogous transparency options on
other private helpers. There is no new file-level option. Neither these scope commands
nor the private helpers change the meaning of any target or consumer statement.

## Users

`python3 tools/downstream.py Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible`
reports zero downstream modules. A direct import search in both library roots agrees.
No consumer file requires an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible | T6 | Three proofs completed; public signatures and imports identical. |

## Status

landed 20261021T130156-L-2592138 2026-10-21 (merge of deliver/T6/Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible)
