# ellAdic_localizing_canonical_rightAdjoint_obj_isBounded

## Reason

The static preflight requests a change record for the added top-level elaboration
options. The proof introduces proved private coefficient and adjunction comparison
helpers in `AlgebraicGeometry.ProEtale` and
`AlgebraicGeometry.ProEtale.CondensedRing`. It sets `autoImplicit` to false explicitly
and allows larger synthesized instance terms. These are file-local elaboration settings.
All existing public signatures, their section variables, visibility and public imports
are identical. No public definition changes, and no target meaning changes.

The item compiled without diagnostics against the current published library. The delivery
probe also passed before the static preflight requested this record. No module besides
the item is edited. In particular no forced adaptation is claimed.

## Old

The canonical theorem's existing signature, verbatim:

```lean
theorem ellAdic_localizing_canonical_rightAdjoint_obj_isBounded
    (hF : (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsLeftAdjoint)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (((@Functor.rightAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF).obj
          ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj))
```

There were no explicit `autoImplicit` or `synthInstance.maxSize` settings in this file.
The original public section begins in namespace
`AlgebraicGeometry.ProEtale.CondensedRing`, with `open Scheme`.

## New

The canonical theorem's signature is verbatim unchanged:

```lean
theorem ellAdic_localizing_canonical_rightAdjoint_obj_isBounded
    (hF : (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsLeftAdjoint)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (((@Functor.rightAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF).obj
          ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj))
```

Added file-local elaboration settings:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
```

The new private coefficient helpers are enclosed in
`namespace AlgebraicGeometry.ProEtale`, closed before the existing namespace
`AlgebraicGeometry.ProEtale.CondensedRing` begins. Every new helper is private and proved.
The original variable block and `open Scheme` are retained. No global instance, attribute,
notation, or definition is added. The supplied-adjoint theorem's signature and proof are
unchanged. Its canonical-adjoint dependency now has a complete proof from existing results.

## Users

`tools/downstream.py` was run for the item with both public theorem names. It lists the
following 25 transitive importers. Only `EllAdicLocalizingExceptionalConstructible` mentions
the supplied-adjoint theorem; no downstream module mentions the canonical theorem.
Their existing statements and definitions retain their meaning because no public interface
or data changes. Holders were not queried for these unedited modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Proved original hole; public interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| Sheaf.Targets.PoincareUncurry | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| TargetsCheck | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Basic | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Statement | Not queried; not edited | Same public signatures and definitions; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | Not queried; not edited | Same public signatures and definitions; no adaptation. |

## Status

landed 20261019T112613-L-3961067 2026-10-19 (merge of deliver/X2/Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded)
