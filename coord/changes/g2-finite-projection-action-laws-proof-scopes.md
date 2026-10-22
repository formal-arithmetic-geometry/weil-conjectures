# AlgebraicGeometry.ProEtale.finiteProjectionAction_proper

## Reason

This record covers the proof elaboration scopes added in
`Sheaf.Paper.FiniteProjectionActionLaws`. Preflight classifies the added `variable`, `open`,
`section`, option and local `attribute` commands as a possible interface change and requires
this record under stage 3 §3.3. All eight existing theorem signatures, all public imports,
the coefficient-finiteness instance and the public associator construction are preserved.
Only proofs, private helpers and their elaboration scopes change. No adopted source-library
file is edited.

The private helpers prove pullback tensor associativity, the proper/open/counit calculations,
and the composite-action calculation. The component interfaces retain the original composite
functor objects while rewriting the actual canonical projection maps. This avoids expensive
kernel conversion between composite and nested objects in concrete derived categories.
No data is selected from an unproved existence theorem, and no hole is added or split off.

## Old

The original file's elaboration setup was:

```lean
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
```

The first existing theorem was, verbatim:

```lean
theorem finiteProjectionAction_proper
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsProper f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) Y (R((f)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      R((f)_*[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) X M
            (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} P.Coefficient) f).app M).app N₁)).app N₂ ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  sorry
```

The other seven existing theorem signatures, the two public construction bodies and every
public import are preserved verbatim apart from insignificant whitespace in signatures.

## New

The same first theorem, with its completed proof:

```lean
theorem finiteProjectionAction_proper
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsProper f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) Y (R((f)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      R((f)_*[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) X M
            (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} P.Coefficient) f).app M).app N₁)).app N₂ ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  exact genericProjectionAction_proper (ModuleCat.{u + 1} P.Coefficient) f M N₁ N₂
```

The two added file-local elaboration options are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Inside the new private-helper namespace `CategoryTheory.Functor`, the proof opens
`_root_.DerivedCategory LaxMonoidal OplaxMonoidal` and binds its explicit coefficient-category
variables. Those bindings end with that namespace. The pro-etale proof uses the sections
`ActionTensor`, `ActionComposition`, `ActionOpen`, `ComparisonComponents` and
`ActionCertificates`; each declares explicit category variables and is closed in this file.
The ordinary etale proof uses closed `ComparisonComponents` and `ActionCertificates`
sections. The certificates omit the unused `UpperStarPreservesFlat A` instance explicitly.

The additional namespace-local instance priorities are, exactly:

```lean
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local instance high] SymmetricCategory.toBraidedCategory
```

The last command occurs in each site's namespace. In `ActionTensor`, the proof opens
`DerivedCategory Functor.LaxMonoidal Functor.OplaxMonoidal` and locally registers
`isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar`. `ActionOpen` opens
`Functor.LaxMonoidal`. Four private coherence proofs individually use:

```lean
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
```

These attributes are local to the stated scope or declaration; no persistent public
attribute, notation, instance or declaration is added. Every new helper is private and
completely proved. No private helper appears in a public signature or a public definition.

## Users

The read-only command
`python3 tools/downstream.py Sheaf.Paper.FiniteProjectionActionLaws --uses
finiteProjectionAction_proper finiteProjectionAction_open finiteProjectionAction_compactification
finiteProjectionAction_open_counit projectionAction_coefficientFinite projectionActionAssociator`
reports the three downstream modules below and the item itself as the only textual user of
these public declaration names. Direct importers are `EtaleRhoMonoidalMate` and
`ProjectionPurityAgreement`; `EtaleCoprojectionRhoCompatibility` is a transitive importer.
Current module claim records list none of these three consumer modules as held.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteProjectionActionLaws | G2 | Eight holes closed; existing public interface and constructions preserved. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Existing import and all statements and definitions remain valid; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Existing import and all statements and definitions remain valid; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Transitive dependency only; no adaptation. |

The consumer audit found no reference to these declaration names outside the item. Their
unchanged public imports and unchanged public construction bodies preserve the meanings of
consumer statements and definitions. No consumer is edited and no target definition review
is reopened. The module has compiled without warnings in 46.7 seconds, and the eight-law
axiom probe reports only `propext`, `Classical.choice` and `Quot.sound` for every theorem.
The independent CODEX reader reviews this record, the proof scopes and the node route through
the ordinary delivery process; this worker does not claim a separate second reading.

## Status

landed 20261022T022037-L-432158 2026-10-22 (merge of deliver/G2/Sheaf.Paper.FiniteProjectionActionLaws)
