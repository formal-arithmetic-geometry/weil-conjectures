# TestLC.fromIntegers and AlgebraicGeometry.ProEtale.testHomEquiv

## Reason

Repair private helper definitions disabled by upstream sync e47efb5a5. The first now uses
this module's explicit spectrum projection. The second reuses the proved spectrum and relative pullback correspondences from
`Sheaf.Paper.ProEtalePointComponentsMaps`. The returned duplicate
`relativeMapEquiv_target` and its local `relativeMapEquiv` have been removed. The second
reading also removed duplicate local `specMapEquiv`, `specMapEquiv_apply`, and
`profiniteProjection_natural`, and the unused `TestLC.ringMapEquiv`. The proof-only
`import all` is retained and their existing declarations are used directly.
The surrounding private scalar-extension helpers gain independent coefficient universes.
The returned stale-base delivery is reapplied to the current main file, with its holed
construction and all five theorem holes replaced by complete Lean terms.
These are implementation repairs; no public definition or statement changes.

## Old

Current main at the repair retry contains the following definitions. `fromIntegers` is
an active holed definition; `testHomEquiv` is active but uses the broken private component
correspondence. The repair constructs both directly:

```lean
private noncomputable def fromIntegers (φ : LocallyConstant S ℤ →+* B) :
    LocallyConstant S A →ₐ[A] B := by
  sorry

private noncomputable def testHomEquiv (K : Type u) [Field K] (S T : Profinite.{u}) :
    ((profiniteToProEtOf (Spec (.of K))).obj S ⟶
      (profiniteToProEtOf (Spec (.of K))).obj T) ≃ (S ⟶ T) :=
  (pointComponentsEquiv _ _ T).trans
    (((testComponentsHomeo K S).symm.continuousMapCongr (Homeomorph.refl T)).trans
      (profiniteHomContinuousEquiv S T).symm)
```

The old local binders were `universe u` and
`variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (S : Profinite.{u})`.

## New

```lean
private noncomputable def fromIntegers (φ : LocallyConstant S ℤ →+* B) :
    LocallyConstant S A →ₐ[A] B :=
  { LocallyConstant.liftPrimeSpectrum (algebraMap A B) (projection S φ) with
    commutes' := LocallyConstant.liftPrimeSpectrum_algebraMap _ _ }

private noncomputable def testHomEquiv (K : Type u) [Field K] (S T : Profinite.{u}) :
    ((profiniteToProEtOf (Spec (.of K))).obj S ⟶
      (profiniteToProEtOf (Spec (.of K))).obj T) ≃ (S ⟶ T) :=
  (relativeMapEquiv _ _ T).trans
    ((Iso.homCongr (TestLC.lcIso K S).symm (Iso.refl _)).trans
      ((specMapEquiv _ T).trans
        (((specSpaceHomeo K S).symm.continuousMapCongr (Homeomorph.refl T)).trans
          { toFun := fun f ↦ ConcreteCategory.ofHom f
            invFun := fun f ↦ f.hom.hom })))
```

The local binders are `universe u v w` and
`variable {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra A B] (S : Profinite.{u})`.
The spectrum correspondence and its evaluation and naturality laws are the existing
proved private helpers of the retained component-map import. The local scalar-extension
inverse laws are fully proved.
All public statements, visibility and statement dependencies remain identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GeometricFieldProfiniteDenseSubsite | R2 | Private construction repaired; all six current active holes closed. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | Sole external explicit use of the public theorem; its signature and meaning are unchanged, so no adaptation. |

`tools/downstream.py Sheaf.Paper.GeometricFieldProfiniteDenseSubsite --uses geometricFieldProfiniteDenseSubsite`
finds these two explicit users. The repaired definitions are private and have no external users.
No target statement uses a changed public definition. No forced adaptation is made.

## Status

landed 20261017T013736-L-115246 2026-10-17 (merge of deliver/R2/Sheaf.Paper.GeometricFieldProfiniteDenseSubsite)
