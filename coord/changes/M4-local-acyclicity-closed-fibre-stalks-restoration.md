# AlgebraicGeometry.Etale.closedFibre_derivedUnit_target_stalks

## Reason

Restore the quarantined rework item from its archive at
`quarantine/Sheaf/AlgebraicGeometry/LocalAcyclicityClosedFibreStalks.lean`.
The archived proof fails because its private import
`Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk` is now an empty,
withdrawn module. Replace it with the official WeilConjectures implementation.
That theorem uses `strictLocalizationToBase`, while the original statement uses
`strictHenselizationStructuralMap`. These models are canonically isomorphic,
but are not definitionally equal.

Use the existing proved `smallStrictHenselizationColimitIso_toBase` comparison.
Construct the induced isomorphism of pullbacks and use the archived private
cohomology-invariance helper to transport coefficients. Insert `singleFunctorιIso`
explicitly. All proof additions are proved; no new public declaration or definition.
The public import, theorem signature, visibility and docstrings are unchanged.
No target statement or mathematical definition changes.

## Old

The live module is absent; its preserved archive has the signature:

```lean
theorem closedFibre_derivedUnit_target_stalks
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ]
    (z : Spec (.of Ξ) ⟶
      pullback (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
        (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s)))) :
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
    let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationPointEvaluation s)))
    let h := pullback.fst f' t
    let x := (z ≫ i) ≫ p
    ∃ e : Scheme.strictHenselizationScheme s ≅ Scheme.strictHenselizationScheme (x ≫ f),
      ∀ q : ℕ, Nonempty
        ((Scheme.pointSmallEtale z).sheafFiber.obj
            ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
              ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.obj
                (((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus ⋙
                  (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus).obj
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj
                    ((upperStar AddCommGrpCat.{u + 1} p).obj G))))) ≅
          (cohomology AddCommGrpCat.{u + 1}
            (localAcyclicityFiber f x (t ≫ e.hom)) (q : ℤ)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom) ≫
                  Scheme.strictHenselizationStructuralMap x)).obj G)))
```

Its private stalk-formula import is:

```lean
import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
```

## New

Restore exactly the same signature above and its existing proof, adding the
canonical-model transport described above. The replacement/additional private imports are:

```lean
import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
```

Remove the unused private import `Mathlib.AlgebraicGeometry.Morphisms.Separated`.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks
--allow-missing --uses closedFibre_derivedUnit_target_stalks` reports zero live
consumers. Searching both library roots and quarantine finds the single archived
consumer below. Its call takes the same arguments and obtains the same existential
isomorphism, so no adaptation is required. No consumer file is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks | M4 | Restore and repair proof. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit | unclaimed | Same signature and public imports; no adaptation. |

## Status

landed 20261021T225152-L-3785462 2026-10-21 (merge of deliver/M4/Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks)
