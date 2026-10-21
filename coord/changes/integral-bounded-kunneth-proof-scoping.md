# Proof checking in IntegralBoundedKunnethExact

## Reason

Restore the assigned quarantined module and complete its original theorem proof. The
public interface, mathematical statements, definitions and public imports are unchanged.
This record documents new proof-checking commands, because the interface scanner treats
module-level options as interface changes. There is no mathematical definition repair.

## Old

The archived public section starts with `universe u w` and the categorical namespace opens
without explicit proof options. The theorem has one `sorry` and this signature:

```lean
theorem integral_bounded_kunneth_exact (r : ℤ) :
    ∃ ι : ∀ C D : Bounded IntegralModuleCat.{u},
        integralKunnethTensorTerm r C D ⟶
          (homologyFunctor IntegralModuleCat.{u} r).obj (C.obj ⊗ D.obj),
    ∃ π : ∀ C D : Bounded IntegralModuleCat.{u},
        (homologyFunctor IntegralModuleCat.{u} r).obj (C.obj ⊗ D.obj) ⟶
          integralKunnethTorTerm r C D,
      (∀ C D : Bounded IntegralModuleCat.{u},
        Function.Injective (ι C D) ∧ Function.Exact (ι C D) (π C D) ∧
          Function.Surjective (π C D)) ∧
      (∀ (C C' D D' : Bounded IntegralModuleCat.{u}) (f : C ⟶ C') (g : D ⟶ D'),
        integralKunnethTensorMap r f g ≫ ι C' D' =
          ι C D ≫ (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom)) ∧
      (∀ (C C' D D' : Bounded IntegralModuleCat.{u}) (f : C ⟶ C') (g : D ⟶ D'),
        (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom) ≫ π C' D' =
          π C D ≫ integralKunnethTorMap r f g)
```

## New

The theorem has exactly the same signature and a complete proof. The module adds the
universe `v` only for private general categorical helpers; no existing declaration acquires
a new universe parameter. `autoImplicit false` records the project convention.
`backward.isDefEq.respectTransparency false` permits dependent categorical comparisons to
elaborate. The private natural-transformation comparison uses scoped
`backward.defeqAttrib.useBackward true`. The final theorem uses scoped
`maxHeartbeats 1000000`; the compiler's 60-second wall limit is unchanged.
`open scoped ZeroObject` supplies the standard notation for private helpers.

The proved private helpers construct a short flat resolution, compare Tor zero with tensor,
identify stationary spectral-sequence pages naturally, and extract the two-step filtration
sequence. New imports are private proof imports. All original public definitions remain
verbatim, including both direct sums and both maps.

## Users

| module | current holder | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.IntegralBoundedKunnethExact | E1 | Restore archive and prove original hole. |
| Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion | quarantined | Direct importer; unchanged public interface requires no adaptation. |

A search of both live roots and both quarantine roots finds no live direct importer and
only the archived `IntegralDerivedTensorBoundedTorsion` direct importer. Its source,
parent dependency on this node and the unit route are preserved. No withdrawal, forced
adaptation, source-library change or target statement change is requested.

## Status

landed 20261021T100924-L-4172136 2026-10-21 (merge of deliver/E1/Sheaf.Algebra.Homology.IntegralBoundedKunnethExact)
