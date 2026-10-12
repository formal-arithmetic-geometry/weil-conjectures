# AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite

## Reason

Repair E1 from reviewer X-4e23d (head 4e23d6ef3, review point 4).
The normalization cokernel must have finite underlying stalks, not merely finitely
generated coefficient modules. Over an algebraically closed field of characteristic
3, coefficients Λ = F_3[t], ℓ = 3 and the nodal cubic with its smooth point at
infinity removed give an acyclic normalized lower-shriek sheaf, but H¹ downstairs
is Λ and violates C5. The added hypothesis excludes precisely this example and
matches the preceding normalization exact-sequence theorem's hypothesis.

## Old

The ambient variables are `(Λ : Type (u + 1)) [CommRing Λ]`.

```lean
theorem IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite {k : Type u} [Field k]
    [IsAlgClosed k] {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] [Smooth (ν ≫ f)] (V : X.Opens)
    (hV : Dense (V : Set X)) [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j]
    {j' : U' ⟶ X'} [IsOpenImmersion j'] {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ)
    [Fact ℓ.Prime]
    (H : IsCurve.Assertions Λ (ν ≫ f)
      ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ))) :
    IsCurve.Assertions Λ f ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ))
```

## New

The ambient variables remain `(Λ : Type (u + 1)) [CommRing Λ]`.

```lean
theorem IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite {k : Type u} [Field k]
    [IsAlgClosed k] {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] [Smooth (ν ≫ f)] (V : X.Opens)
    (hV : Dense (V : Set X)) [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j]
    {j' : U' ⟶ X'} [IsOpenImmersion j'] {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ)
    [Fact ℓ.Prime] [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})]
    (H : IsCurve.Assertions Λ (ν ≫ f)
      ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ))) :
    IsCurve.Assertions Λ f ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ))
```

## Users

Searched every Lean module by the declaration name and ran
`tools/downstream.py WeilConjectures.AlgebraicGeometry.Curve.Reductions --uses
AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`.
There is exactly one external declaration user. All other downstream modules
only transitively import the declaration; their statements are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | A2 | Adds the finite-quotient instance to the named theorem; its existing sorry remains. No internal caller. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | no local claim recorded; adaptation checked by A2 | `reducedConstantLowerShriekAssertions_of_reduction_data` specializes to `ULift (ZMod r)`. Its quotient is finite by existing instances, so no statement or proof adaptation is required. Compiled against the corrected signature. |

The blueprint node already states finite prime-field coefficients. Its informal
statement, proof route and unit realization are unchanged; its Lean record gains
the corrected verbatim signature. No definition and no Challenge target changes,
so this does not reopen a target's definition review.

## Status

landed 20261012T112828-L-763717 2026-10-12 (merge of deliver/A2/WeilConjectures.AlgebraicGeometry.Curve.Reductions)
its caller together. Global-build verification belongs to the maintainer.
