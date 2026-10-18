# Algebra.normal_domain_case

## Reason

The original `Type*` on the test extension introduced an independent universe. It did not
ensure that the test extensions were large enough to contain the base field, either algebra,
or the fraction fields used in Tag 06DF. In particular, quantification over a smaller universe
can be vacuous for a large base field. The intended geometric-normality hypothesis requires
test extensions in the common universe `max u v w`, as the unchanged main theorem already has.
The private filtered-colimit API works in one common universe; lift both algebras there and
transport normality back through `ULift.algEquiv`.

## Old

```lean
theorem normal_domain_case
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsIntegrallyClosed A]
    [IsDomain B] [IsIntegrallyClosed B]
    (hA : ∀ (E : Type*) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)
```

## New

```lean
theorem normal_domain_case
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsIntegrallyClosed A]
    [IsDomain B] [IsIntegrallyClosed B]
    (hA : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)
```

## Users

`python3 tools/downstream.py Sheaf.RingTheory.GeometricallyNormalTensorNormal
--uses Algebra.normal_domain_case` lists only the item module as a declaration user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.GeometricallyNormalTensorNormal | Z9 | Its main theorem already tests extensions in `max u v w`; its proof applies the repaired intermediate statement. Its main signature is unchanged. |

The module has eleven downstream modules. None mentions `Algebra.normal_domain_case`;
they use the main theorem, whose elaborated statement and visibility stay unchanged.
No downstream adaptation or target-statement change is required. No definition changes.

## Status

landed 20261018T091415-L-3259812 2026-10-18 (merge of deliver/Z9/Sheaf.RingTheory.GeometricallyNormalTensorNormal)
