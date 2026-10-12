# DerivedCategory.homology_vanishes_of_localization_span

## Reason

The static preflight treats added `open` and `attribute` commands as a possible
interface change and therefore requires this record. Both commands are scoped to
the existing `DerivedCategory` namespace. The attribute is explicitly local and
restores the prior instance environment on leaving the namespace. It prevents the
concrete localization ring's independent Ring instances from being mixed in the
proof. There is no new exported instance or declaration other than a private,
proved tensor comparison; no existing signature, visibility, or definition changes.

## Old

The existing signature, verbatim:

```lean
theorem homology_vanishes_of_localization_span
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁} (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (n : ℤ)
    (hlocal : ∀ i : Fin r,
      IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} (Localization.Away (f i))) n).obj
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M)))) :
    IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) n).obj (Q.obj M))
```

The namespace had no local Ring-instance priority adjustment and no
`open TensorProduct` command. The theorem's proof was `by sorry`.

## New

The theorem retains the identical signature displayed in Old, with its proof
completed. The following commands are inside `namespace DerivedCategory`:

```lean
attribute [local instance 2000] CommRing.toRing

open TensorProduct
```

The transparency option is scoped to the theorem alone:

```lean
set_option backward.isDefEq.respectTransparency false in
```

A scratch example after `end DerivedCategory`, in the restored instance environment,
applies the theorem to the original signature verbatim; it compiles. This checks
compatibility including the universes and the concrete localization Ring instances.
All new imports are proof-only. The original four public imports are preserved.

## Users

`tools/downstream.py ... --uses DerivedCategory.homology_vanishes_of_localization_span`
finds the item itself and its existing direct caller:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.HomologyVanishingLocalizationSpan | E2 | Proof completed; signature unchanged. |
| Sheaf.RingTheory.RingPseudoCoherentLocalizationGlue | unclaimed | Calls the same theorem with the same arguments; no adaptation required. |

Neither module's statements become weaker, stronger, or different. No target's
statement or underlying definitions change. The caller is checked unchanged in a
scratch overlay against the proved item.

## Status

landed 20261012T230754-L-1907877 2026-10-12 (merge of deliver/E2/Sheaf.RingTheory.HomologyVanishingLocalizationSpan)
