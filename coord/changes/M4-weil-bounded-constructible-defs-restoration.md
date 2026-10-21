# AlgebraicGeometry.ProEtale.CondensedRing.WeilBoundedConstructible

## Reason

Restore the source module removed by the merge queue after the cluster restore,
according to its assignment in `coord/rework.tsv` (2026-10-20). The assigned
quarantine source has zero holes. The repair restores that complete source at
its original library path; it does not withdraw or replace any declaration.

The restored file is byte-for-byte identical to
`quarantine/WeilConjectures/WeilObject/BoundedConstructible/Defs.lean`.
All signatures, attributes, public imports, definitions and proofs are preserved.
No target statement or mathematical definition is changed relative to the
archived source, so the restoration does not change any target's meaning.

## Old

The file `lean/WeilConjectures/WeilObject/BoundedConstructible/Defs.lean`
is absent from the current library. Its original complete source is preserved
at the quarantine path above. No declaration is being replaced with a weaker one.

## New

The original module header and three public imports are restored verbatim:

```lean
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
```

The declarations below are restored verbatim in namespace
`AlgebraicGeometry.ProEtale.CondensedRing`, with the original section variables:

```lean
/-- A *Weil object* of the bounded constructible derived category `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of
`ℚ̄_ℓ`-sheaves for an endomorphism `Φ : X ⟶ X` over `Spec k` is an object `K` together with an
isomorphism `φ_K : LΦ^* K ≅ K`, where `LΦ^* = boundedConstructibleUpperStar ℚ̲̄_ℓ ℓ Φ` is
the restricted derived pullback along `Φ`. The isomorphism `φ_K` is structure data, and
morphisms are morphisms of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` commuting with the structure isomorphisms. -/
abbrev WeilBoundedConstructible : Type _ :=
  IsoAlgebra (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)

namespace WeilBoundedConstructible

/-- The forgetful functor from Weil objects of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` to `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, discarding the
Frobenius structure isomorphisms. -/
noncomputable def forget :
    WeilBoundedConstructible ℓ Φ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  IsoAlgebra.forget (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)

/-- A Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is a Weil object of the ambient derived category
`D(Mod_{ℚ̲̄_ℓ,X})` for the derived pullback `L((Φ)^*⟦ℚ̲̄_ℓ⟧)`: the transport of algebras along
the inclusion, the structure isomorphism of `K` being
`L((Φ)^*⟦ℚ̲̄_ℓ⟧) K ≅ LΦ^* K ≅ K` through `boundedConstructibleUpperStarCompatibility`. -/
noncomputable def toDerivedCategory :
    WeilBoundedConstructible ℓ Φ ⥤
      IsoAlgebra L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  IsoAlgebra.mapOfNatIso
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ).symm

@[simp]
lemma toDerivedCategory_obj_carrier (K : WeilBoundedConstructible ℓ Φ) :
    ((toDerivedCategory ℓ Φ).obj K).carrier = K.carrier.obj :=
  rfl

```

## Users

`tools/downstream.py WeilConjectures.WeilObject.BoundedConstructible.Defs
--allow-missing --uses WeilBoundedConstructible` reports zero current library
consumers. Searching import lines in both `lean/` and `quarantine/` identifies
these three quarantined direct consumers. All retain their original meaning;
none is edited or delivered. Their original sources were checked against the
restored module as verification copies. `LowerUpperShriek` compiled unchanged
in 7.4 seconds. `TensorHom` timed out at 60 seconds; this optional verification
is inconclusive, and its quarantined source is not included in the packet.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | M4 | Restore the complete archived source. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Original interface restored; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Original interface restored; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Original interface restored; no adaptation. |

Other textual mentions in TraceFormula.Basic and the finite-coefficient
WeilComplex module are documentation references, not imports of this module.

`UpperLowerStar` also compiled unchanged in 4.3 seconds. Verification copies
are excluded from this delivery.

## Status

landed 20261021T014715-L-2446875 2026-10-21 (merge of deliver/M4/WeilConjectures.WeilObject.BoundedConstructible.Defs)

