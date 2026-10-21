# WeilConjectures.SfbHomFilteredColimit.internalHom_finiteFree_stage

## Reason

Fill the finite-free stage theorem's sole proof hole. Server preflight class (d)
requires a change record for the added context commands (`open`, `attribute`,
`variable`, and local notation), even though the public declaration is unchanged.
This record documents those commands and every downstream consumer.

The new context supports private proofs of tensor additivity, tensor-unit
normalization, and finite-product transport on homology. Local instances select
the existing independent-coefficient monoidal structure. The transparency option
lets the proof compare the recorded tensor and Hom representative wrappers.
The tensor category is locally marked irreducible to control elaboration. Local
notation abbreviates the existing module category and underlying ring sheaf.
The `omit` commands only remove unused assumptions from private helper binders.
All these settings are local to this file or the displayed section.

## Old

Original context, verbatim:

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SfbHomFilteredColimit
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
```

Original public theorem signature, verbatim:

```lean
theorem internalHom_finiteFree_stage (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R)
    (hfree : ∃ d : ℕ, Nonempty
      (T ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    QuasiIso ((comparison.{u, v, r} J R P L).app T) ∧
      QuasiIso (roofDenominator.{u, v, r} J R P L T)
```

The original theorem proof is `by sorry`.

## New

File context:

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SfbHomFilteredColimit
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]

attribute [local instance] Abelian.hasFiniteBiproducts

open MonoidalCategory
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)
```

The private tensor-unit proof section uses:

```lean
section RegularTensor
variable (R : Sheaf J CommRingCat.{max u v r})
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
set_option quotPrecheck false
set_option hygiene false in
local notation "A" => Modules.{u, v, r} J R
set_option hygiene false in
local notation "O" => (sheafCompose J
  (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
-- Private, fully proved helpers.
end RegularTensor
```

The private Hom additivity and evaluation helpers also use declaration-local:

```lean
omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
```

The public theorem signature is retained verbatim:

```lean
theorem internalHom_finiteFree_stage (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R)
    (hfree : ∃ d : ℕ, Nonempty
      (T ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    QuasiIso ((comparison.{u, v, r} J R P L).app T) ∧
      QuasiIso (roofDenominator.{u, v, r} J R P L T)
```

Its proof is complete. Every added helper is private and fully proved. All new
imports are proof-only. The original public data import is retained; no existing
public definition, signature, attribute, or target meaning changes. The node's
proof is expanded to describe the actual tensor-unit and finite-product argument.
There are no new nodes, split-off holes, or adaptations of another module.

Validation: `lcompile.py` compiled the final file without warnings in 43.1 seconds.
A textual comparison verifies that the public signature is identical to the source.

## Users

`tools/downstream.py Sheaf.Paper.InternalHomFiniteFreeStage --uses
WeilConjectures.SfbHomFilteredColimit.internalHom_finiteFree_stage` lists the three
transitive importers below. Its declaration-use search lists the assigned module
and the direct parent. Holder values are from the shared claim records when this
record was prepared. All existing public interfaces and representative definitions
are retained, so every consumer uses the same theorem statement and needs no edit.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalHomFiniteFreeStage | M3 | Fill the sole hole; add private proof helpers and local proof context. |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | R3 | Direct caller; statement identical, no adaptation. |
| WeilConjectures | unclaimed | Transitive importer; public environment unchanged, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A3 | Transitive importer; public environment unchanged, no adaptation. |

## Status

landed 20261021T014226-L-2390619 2026-10-21 (merge of deliver/M3/Sheaf.Paper.InternalHomFiniteFreeStage)
