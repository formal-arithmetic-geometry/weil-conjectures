# CategoryTheory.unit_power_localDerivedComplete

## Reason

The stage-3 preflight classifies added file and section commands as an interface
change. This delivery adds elaboration options, opens `ZeroObject` notation, and
introduces section variables for private restriction helpers. Record those changes
explicitly for independent review. The theorem signature, all public imports, all
existing attributes, and every public definition are unchanged. Options and section
variables control elaboration in this file. No exported notation or instance is added.

## Old

Original file context:

```lean
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
```

The original theorem signature, verbatim:

```lean
theorem unit_power_localDerivedComplete
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (a b unit : (O.obj ⋙ forget CommRingCat).sections) (e : ℕ)
    (hu : ∀ U : Cᵒᵖ, IsUnit (unit.val U)) (he : 1 ≤ e)
    (hab : ∀ U : Cᵒᵖ, a.val U = unit.val U * b.val U ^ e) :
    (∀ N : ringedSiteDerived O,
      IsLocallyDerivedRingedIdealComplete O
        (image (ringedKoszulScalar O a)) (image.ι (ringedKoszulScalar O a)) N ↔
      IsLocallyDerivedRingedIdealComplete O
        (image (ringedKoszulScalar O b)) (image.ι (ringedKoszulScalar O b)) N) ∧
    (∃ alpha : ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O a) ≅
        ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O b),
      ∀ N : ringedSiteDerived O,
        ringedCechCompletionUnit O (ringedLocalizationTwoTerm O a)
          (ringedLocalizationTwoTermAugmentation O a) N ≫ alpha.hom.app N =
        ringedCechCompletionUnit O (ringedLocalizationTwoTerm O b)
          (ringedLocalizationTwoTermAugmentation O b) N) ∧
    ∀ c : (O.obj ⋙ forget CommRingCat).sections, c = a ∨ c = b →
      (∀ N : ringedSiteDerived O,
        IsLocallyDerivedRingedIdealComplete O
          (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c))
          ((ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O c)).obj N)) ∧
      ∀ (N L : ringedSiteDerived O),
        IsLocallyDerivedRingedIdealComplete O
          (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c)) L →
        Function.Bijective
          (fun f : (ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O c)).obj N ⟶ L ↦
            ringedCechCompletionUnit O (ringedLocalizationTwoTerm O c)
              (ringedLocalizationTwoTermAugmentation O c) N ≫ f)
```

## New

Updated file context:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
```

The added `ModuleRestriction` section binds two small sites, their continuous and
cocontinuous functor, and the coefficient ring sheaf for private module comparisons.
The added `ComplexRestriction` section binds the two ring sheaves, an additive
restriction functor, two sections, and their localization-unit arrow isomorphism.
Every declaration in those sections is private and proved or explicitly constructed.
They export no instance or public signature. A proved private theorem
`unitPower_hasSheafCompose` is registered as a local instance to cache the generic
proof that forgetting commutative rings preserves sheaves. This local attribute is
confined to the current file; it exports no instance. Two private equality statements
use explicit morphism types to avoid expensive coercion searches. These elaboration
optimizations leave all public declarations unchanged.

The new theorem signature is identical to the old signature:

```lean
theorem unit_power_localDerivedComplete
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (a b unit : (O.obj ⋙ forget CommRingCat).sections) (e : ℕ)
    (hu : ∀ U : Cᵒᵖ, IsUnit (unit.val U)) (he : 1 ≤ e)
    (hab : ∀ U : Cᵒᵖ, a.val U = unit.val U * b.val U ^ e) :
    (∀ N : ringedSiteDerived O,
      IsLocallyDerivedRingedIdealComplete O
        (image (ringedKoszulScalar O a)) (image.ι (ringedKoszulScalar O a)) N ↔
      IsLocallyDerivedRingedIdealComplete O
        (image (ringedKoszulScalar O b)) (image.ι (ringedKoszulScalar O b)) N) ∧
    (∃ alpha : ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O a) ≅
        ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O b),
      ∀ N : ringedSiteDerived O,
        ringedCechCompletionUnit O (ringedLocalizationTwoTerm O a)
          (ringedLocalizationTwoTermAugmentation O a) N ≫ alpha.hom.app N =
        ringedCechCompletionUnit O (ringedLocalizationTwoTerm O b)
          (ringedLocalizationTwoTermAugmentation O b) N) ∧
    ∀ c : (O.obj ⋙ forget CommRingCat).sections, c = a ∨ c = b →
      (∀ N : ringedSiteDerived O,
        IsLocallyDerivedRingedIdealComplete O
          (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c))
          ((ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O c)).obj N)) ∧
      ∀ (N L : ringedSiteDerived O),
        IsLocallyDerivedRingedIdealComplete O
          (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c)) L →
        Function.Bijective
          (fun f : (ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O c)).obj N ⟶ L ↦
            ringedCechCompletionUnit O (ringedLocalizationTwoTerm O c)
              (ringedLocalizationTwoTermAugmentation O c) N ≫ f)
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.UnitPowerCompleteness --uses
unit_power_localDerivedComplete` reports the item and one downstream module. The
consumer currently imports the item privately but has no occurrence of the declaration
in its Lean code: its proof is still unfinished and its docstring cites this argument.
Its statements were read and are unaffected by private helpers or local scope commands.
No consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.UnitPowerCompleteness` | V8 | One theorem proved; signature unchanged; private proof context added. |
| `Sheaf.CategoryTheory.FiniteFreeCompletionTransport` | unclaimed in current queue | Private importer; statements unchanged; no adaptation. |

No target statement or definition used by a target changes. No source-library module
is edited. The independently checked comparison is between the unchanged original
signature and the new proved declaration, together with the recorded context commands.

## Status

landed 20261021T144020-L-37252 2026-10-21 (merge of deliver/V8/Sheaf.CategoryTheory.UnitPowerCompleteness)
