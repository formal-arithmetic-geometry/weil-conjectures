# AlgebraicGeometry.exists_reduced_generic_fibre_map_core

## Reason

Repair reviewer X-07e79, head 07e79bf0a, E1 / H3. The original arbitrary
residue-field algebra structure makes the theorem false: with k = Q(t),
L = E = Q(u), supplied t ↦ u² and aE given by t ↦ u² + 1, the required
map would produce a rational-function square root of u² + 1. The valuation
at the irreducible polynomial u² + 1 is odd, so no such square root exists.
The node already specifies the induced algebra structure. Require exactly
that structure, as requested by the reviewer; no natural-language node
statement, definition, target signature, or caller signature changes.

## Old

```lean
theorem exists_reduced_generic_fibre_map_core
    {Z S S' : Scheme.{u}} [IsAffine Z] [IsAffine S] [IsAffine S'] [IsIntegral S']
    (g : Z ⟶ S) (q : S' ⟶ S) (η : S) (η' : S') (hq : q η' = η)
    (hη' : IsGenericPoint η' Set.univ)
    (L k' E : Type u) [Field L] [Field k'] [Field E]
    [Algebra (S.residueField η) L] [Algebra (S.residueField η) k']
    [Algebra L E] [Algebra k' E]
    [Module.Finite (S.residueField η) k'] [IsPurelyInseparable (S.residueField η) k']
    (j : Spec (.of L) ⟶ g.fiber η) (hj : IsSchemeTheoreticallyDominant j)
    (hjbase : j ≫ g.fiberToSpecResidueField η =
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)))
    (e : S'.residueField η' ≃+* k')
    (he : e.toRingHom.comp
      (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom) =
        algebraMap (S.residueField η) k')
    (hsquare : (algebraMap k' E).comp (algebraMap (S.residueField η) k') =
      (algebraMap L E).comp (algebraMap (S.residueField η) L))
    (aE : Algebra (S'.residueField η') E) :
    letI := aE
    ∃ h : Spec (.of E) ⟶
          ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
        IsSchemeTheoreticallyDominant h ∧
        h ≫ ((pullback g q).nilradical.subschemeι ≫
          pullback.snd g q).fiberToSpecResidueField η' =
            Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E))
```

## New

```lean
theorem exists_reduced_generic_fibre_map_core
    {Z S S' : Scheme.{u}} [IsAffine Z] [IsAffine S] [IsAffine S'] [IsIntegral S']
    (g : Z ⟶ S) (q : S' ⟶ S) (η : S) (η' : S') (hq : q η' = η)
    (hη' : IsGenericPoint η' Set.univ)
    (L k' E : Type u) [Field L] [Field k'] [Field E]
    [Algebra (S.residueField η) L] [Algebra (S.residueField η) k']
    [Algebra L E] [Algebra k' E]
    [Module.Finite (S.residueField η) k'] [IsPurelyInseparable (S.residueField η) k']
    (j : Spec (.of L) ⟶ g.fiber η) (hj : IsSchemeTheoreticallyDominant j)
    (hjbase : j ≫ g.fiberToSpecResidueField η =
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)))
    (e : S'.residueField η' ≃+* k')
    (he : e.toRingHom.comp
      (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom) =
        algebraMap (S.residueField η) k')
    (hsquare : (algebraMap k' E).comp (algebraMap (S.residueField η) k') =
      (algebraMap L E).comp (algebraMap (S.residueField η) L))
    (aE : Algebra (S'.residueField η') E)
    (haE : aE = ((algebraMap k' E).comp e.toRingHom).toAlgebra) :
    letI := aE
    ∃ h : Spec (.of E) ⟶
          ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
        IsSchemeTheoreticallyDominant h ∧
        h ≫ ((pullback g q).nilradical.subschemeι ≫
          pullback.snd g q).fiberToSpecResidueField η' =
            Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ReducedGenericFibreMapCore | S1 | Add the induced-algebra equality hypothesis haE. |
| Sheaf.AlgebraicGeometry.ReducedGenericFibreFieldEmbeddingCore | unclaimed | Forced proof adaptation: append rfl to the existing call; its locally defined aE is exactly the induced algebra. Signature and visibility unchanged. |

Source inspection using tools/downstream.py --uses found only the declaration
module and this caller mentioning the changed name. The 149 transitive importers
use the unchanged caller interface and need no edits. No definition changed;
target statement meanings are unchanged.

## Status

landed 20261013T155940-L-1305063 2026-10-13 (merge of deliver/S1/Sheaf.AlgebraicGeometry.ReducedGenericFibreMapCore)
