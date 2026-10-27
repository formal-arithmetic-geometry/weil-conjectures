# AlgebraicGeometry.ProEtale.ScalarCubeFlatModel.simultaneous_flat_model

## Reason

Withdraw the now-unused simultaneous-flat-model module under brief step 8d.
The scalar cube parent already has its complete direct mate proof. The sole remaining
live proof edge is Step 5 of finite compact-support domains; it needs only the canonical
scalar/site isomorphism already proved as `pbcComparisonReduction` in
`Sheaf.Paper.WitnessCompatibility`. The parent proof dependency and argument are updated
in this delivery. Its quarantined Lean archive is preserved unchanged.

## Old

```lean
theorem simultaneous_flat_model
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      ∃ (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (p : P ⟶ K), Good P ∧ QuasiIso p) ∧
    (∀ P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      Good P →
      Good (((comparison A Y)).ordinary.obj P) ∧
      Good (((etale A f)).ordinary.obj P) ∧
      Good (((etaleScalar a Y)).ordinary.obj P) ∧
      Good (((comparison A Y).comp (proetaleScalar a Y)).ordinary.obj P) ∧
      Good (((comparison A Y).comp (proetale A f)).ordinary.obj P) ∧
      Good (((etale A f).comp (comparison A X)).ordinary.obj P) ∧
      Good (((etale A f).comp (etaleScalar a X)).ordinary.obj P) ∧
      Good (((etaleScalar a Y).comp (comparison B Y)).ordinary.obj P) ∧
      Good (((etaleScalar a Y).comp (etale B f)).ordinary.obj P) ∧
      (∀ i : Fin 6, Good ((vertex a f i).ordinary.obj P)) ∧
      IsIso ((comparison A Y).representative P) ∧
      IsIso ((etale A f).representative P) ∧
      IsIso ((etaleScalar a Y).representative P) ∧
      IsIso ((proetaleScalar a Y).representative (((comparison A Y)).ordinary.obj P)) ∧
      IsIso ((proetale A f).representative (((comparison A Y)).ordinary.obj P)) ∧
      IsIso ((comparison A X).representative (((etale A f)).ordinary.obj P)) ∧
      IsIso ((etaleScalar a X).representative (((etale A f)).ordinary.obj P)) ∧
      IsIso ((comparison B Y).representative (((etaleScalar a Y)).ordinary.obj P)) ∧
      IsIso ((etale B f).representative (((etaleScalar a Y)).ordinary.obj P)) ∧
      IsIso ((proetale B f).representative
        (((comparison A Y).comp (proetaleScalar a Y)).ordinary.obj P)) ∧
      IsIso ((proetaleScalar a X).representative
        (((comparison A Y).comp (proetale A f)).ordinary.obj P)) ∧
      IsIso ((proetaleScalar a X).representative
        (((etale A f).comp (comparison A X)).ordinary.obj P)) ∧
      IsIso ((comparison B X).representative
        (((etale A f).comp (etaleScalar a X)).ordinary.obj P)) ∧
      IsIso ((proetale B f).representative
        (((etaleScalar a Y).comp (comparison B Y)).ordinary.obj P)) ∧
      IsIso ((comparison B X).representative
        (((etaleScalar a Y).comp (etale B f)).ordinary.obj P)) ∧
      (∀ i : Fin 6, IsIso ((vertex a f i).representative P)) ∧
      (∀ e : Fin 6,
        derivedFace a f e (_root_.DerivedCategory.Q.{u + 1}.obj P) ≫
            (vertex a f (faceTarget e)).representative P =
          (vertex a f (faceSource e)).representative P ≫
            _root_.DerivedCategory.Q.{u + 1}.map (ordinaryFace a f e P))) ∧
    (∀ (P P' : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (v : P ⟶ P'), Good P → Good P' →
      (comparison A Y).NaturalAt v ∧
      (etale A f).NaturalAt v ∧
      (etaleScalar a Y).NaturalAt v ∧
      ((comparison A Y).comp (proetaleScalar a Y)).NaturalAt v ∧
      ((comparison A Y).comp (proetale A f)).NaturalAt v ∧
      ((etale A f).comp (comparison A X)).NaturalAt v ∧
      ((etale A f).comp (etaleScalar a X)).NaturalAt v ∧
      ((etaleScalar a Y).comp (comparison B Y)).NaturalAt v ∧
      ((etaleScalar a Y).comp (etale B f)).NaturalAt v ∧
      ∀ i : Fin 6, (vertex a f i).NaturalAt v)  := by
  sorry
```

## New

The module is withdrawn, with `lean: null` on its retained DAG node.
No replacement theorem or axiom is introduced. The parent's exact replacement is
`((pbcComparisonReduction T a).app K).symm`, in the derived category of B-module sheaves.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed, quarantined | Preserve Lean archive; replace the DAG proof edge and Step 5 by the existing canonical scalar/site isomorphism. |
| Sheaf.Paper.EtaleProEtaleScalarPullbackCube | unchanged | Already proved without this module; no live dependency edge or import. |

There are no Lean importers in lean/ or quarantine/, and no unit or chapter realizes the
withdrawn node. No declaration under WeilConjectures/ changes. No target statement changes.

## Status

landed 20261024T021950-L-2884652 2026-10-24 (merge of deliver/W8/Sheaf.Paper.EtaleProEtaleSimultaneousFlatModel)
