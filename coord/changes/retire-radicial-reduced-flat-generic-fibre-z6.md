# AlgebraicGeometry.exists_radicial_reduced_flat_generic_fibre

## Reason

The queue marks `Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre` as `retire`.
Its main theorem is identical to the already proved declaration in
`WeilConjectures.AlgebraicGeometry.RadicialReducedFlatGenericFibre`. Its only direct
importer uses the public geometric reducedness descent helper, rather than the
radicial theorem. Preserve that helper in a focused module and retire the duplicate
module. No source-library file changes.

## Old

`Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre` declares:

```lean
theorem geometricallyReduced_of_schemeTheoreticallyDominant
    {k : Type u} [Field k] {W X : Scheme.{u}}
    (h : W ⟶ X) (p : X ⟶ Spec (.of k))
    [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (hred : GeometricallyReduced (h ≫ p)) : GeometricallyReduced p

theorem exists_radicial_reduced_flat_generic_fibre
    {Z S : Scheme.{u}} [IsAffine Z] [IsReduced Z] [IsAffine S] [IsIntegral S]
    (g : Z ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (g.fiberToSpecResidueField η)) :
    ∃ (S' : Scheme.{u}) (q : S' ⟶ S),
      IsAffine S' ∧ IsIntegral S' ∧ IsUniversalHomeomorphism q ∧
      ∃ η' : S', IsGenericPoint η' Set.univ ∧ q η' = η ∧
        GeometricallyReduced
          (((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiberToSpecResidueField
            η')
```

The module also has the private helper
`geometricallyReduced_spec_of_isSeparablyGenerated`, used only by its duplicate
radicial theorem. `FiniteInseparableGeometricReduction` privately imports this module.

## New

The old module is withdrawn with `deleted.txt`; the landing tool retains an empty
module. The radicial node now records the existing upstream module and the same
declaration, with precisely the same signature displayed above. Its proof route and
dependencies are preserved. A server compile of that theorem reports exactly the
three permitted axioms.

`Sheaf.AlgebraicGeometry.GeometricallyReducedDominantDescent` contains:

```lean
theorem geometricallyReduced_of_schemeTheoreticallyDominant
    {k : Type u} [Field k] {W X : Scheme.{u}}
    (h : W ⟶ X) (p : X ⟶ Spec (.of k))
    [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (hred : GeometricallyReduced (h ≫ p)) : GeometricallyReduced p
```

The name, signature, public visibility, and complete Mathlib-only proof of this
helper are unchanged. The new module publicly imports only
`Mathlib.AlgebraicGeometry.Geometrically.Reduced`. It adds source documentation and
the node `lem-sbc-geometrically-reduced-dominant-descent` for the existing result.

The sole changed line of `FiniteInseparableGeometricReduction` is:

```lean
import Sheaf.AlgebraicGeometry.GeometricallyReducedDominantDescent
```

in place of its private import of the withdrawn module. Its declarations, proofs,
public imports, and target meanings are unchanged. Its node now cites the helper
explicitly at the last step. Both delivered modules compile with the reduced import
context, including the full proof of the finite inseparable extension theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre | Z6 | Withdraw the duplicate module; repoint its main theorem's node to the unchanged upstream proof. |
| Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction | unclaimed | Sole direct importer and sole external user of the public helper; switch one private proof import and compile its unchanged proof. |
| Sheaf.AlgebraicGeometry.GeometricallyReducedDominantDescent | Z6 (new) | Preserve the public helper with identical signature and proof, without importing the radicial construction. |
| WeilConjectures.AlgebraicGeometry.RadicialReducedFlatGenericFibre | unclaimed | Existing canonical theorem; read and axiom-checked, unchanged. |
| WeilConjectures.AlgebraicGeometry.RadicialPreparationConstruction | unclaimed | Already imports and calls the upstream theorem; unchanged. |

`tools/downstream.py --uses` reports 33 indirect downstream modules. None of them
uses either retired declaration except the direct importer listed above, which
uses the preserved helper. Its public imports and signatures are unchanged. The
radicial theorem has no external user through the withdrawn Sheaf module. The
new helper's proof treats empty schemes and arbitrary nonaffine schemes, without
new hypotheses. No definition or target statement changes.

## Status

landed 20261020T150715-L-2576908 2026-10-20 (merge of deliver/Z6/Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre)
