# Normalized strict-tower composition maps

## Reason

Checking component formulas of the original maps repeatedly exceeded the single-file
60-second compilation limit. Their associator and left-unitor components are identity
morphisms, but applying derived functors to those identities forces expensive
definitional comparisons. Remove those factors using definitional associativity
of functor composition. The natural transformations and all their signatures retain
the same mathematical meaning. The identity normalization rId, open compositor jComp,
equality transport jCongr, proper compositor rComp, gamma and beta all remain.

## Old

```lean
noncomputable def compositionD {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    compositionF B T.cf ⋙ compositionF B T.cg ⟶ compositionF B T.cfg :=
  (Functor.associator (J B T.cf.i) (R B T.cf.g) (J B T.cg.i ⋙ R B T.cg.g)).hom ≫
  Functor.whiskerLeft (J B T.cf.i)
    ((Functor.associator (R B T.cf.g) (J B T.cg.i) (R B T.cg.g)).inv ≫
      Functor.whiskerRight (gamma B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
        (R B T.cg.g) ≫
      (Functor.associator (J B T.q) (R B T.p) (R B T.cg.g)).hom) ≫
  (Functor.associator (J B T.cf.i) (J B T.q) (R B T.p ⋙ R B T.cg.g)).inv ≫
  Functor.whiskerRight
    ((jComp B T.cf.i T.q).hom ≫ (jCongr B T.i_q).hom)
    (R B T.p ⋙ R B T.cg.g) ≫
  Functor.whiskerLeft (J B T.cfg.i)
    ((rComp B T.p T.cg.g).hom ≫ (eqToIso (congrArg (R B) T.p_g)).hom)
```

```lean
noncomputable def compositionC {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) : compositionF B d ⟶ compositionF B c :=
  Functor.whiskerRight
    ((Functor.leftUnitor (J B d.i)).inv ≫
      Functor.whiskerRight (rId B X).inv (J B d.i) ≫
      gamma B c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp d.i).symm))
    (R B d.g) ≫
  (Functor.associator (J B c.i) (R B r.hom) (R B d.g)).hom ≫
  Functor.whiskerLeft (J B c.i)
    ((rComp B r.hom d.g).hom ≫ (eqToIso (congrArg (R B) r.hom_g)).hom)
```

```lean
noncomputable def compositionE {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s) :
    compositionF B c ⋙ G B y ⟶ G B x ⋙ compositionF B c' :=
  (Functor.associator (J B c.i) (R B c.g) (G B y)).hom ≫
  Functor.whiskerLeft (J B c.i) (exchange B s c'.g c.g y wp) ≫
  (Functor.associator (J B c.i) (G B s) (R B c'.g)).inv ≫
  Functor.whiskerRight (beta B x c'.i c.i s wi si).hom (R B c'.g) ≫
  (Functor.associator (G B x) (J B c'.i) (R B c'.g)).hom
```

```lean
noncomputable def compositionHorizontalE {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :
    (compositionF B T.cf ⋙ compositionF B T.cg) ⋙ G B g ⟶
      G B x ⋙ (compositionF B T'.cf ⋙ compositionF B T'.cg) :=
  (Functor.associator (compositionF B T.cf) (compositionF B T.cg) (G B g)).hom ≫
  Functor.whiskerLeft (compositionF B T.cf) (compositionEh B A) ≫
  (Functor.associator (compositionF B T.cf) (G B y) (compositionF B T'.cg)).inv ≫
  Functor.whiskerRight (compositionEf B A) (compositionF B T'.cg) ≫
  (Functor.associator (G B x) (compositionF B T'.cf) (compositionF B T'.cg)).hom

end AlgebraicGeometry.ProEtale.StrictTower
```

## New

```lean
noncomputable def compositionD {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    compositionF B T.cf ⋙ compositionF B T.cg ⟶ compositionF B T.cfg :=
  Functor.whiskerLeft (J B T.cf.i)
    (Functor.whiskerRight (gamma B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
      (R B T.cg.g)) ≫
  Functor.whiskerRight
    ((jComp B T.cf.i T.q).hom ≫ (jCongr B T.i_q).hom)
    (R B T.p ⋙ R B T.cg.g) ≫
  Functor.whiskerLeft (J B T.cfg.i)
    ((rComp B T.p T.cg.g).hom ≫ (eqToIso (congrArg (R B) T.p_g)).hom)
```

```lean
noncomputable def compositionC {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) : compositionF B d ⟶ compositionF B c :=
  Functor.whiskerRight
    (Functor.whiskerRight (rId B X).inv (J B d.i) ≫
      gamma B c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp d.i).symm))
    (R B d.g) ≫
  Functor.whiskerLeft (J B c.i)
    ((rComp B r.hom d.g).hom ≫ (eqToIso (congrArg (R B) r.hom_g)).hom)
```

```lean
noncomputable def compositionE {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s) :
    compositionF B c ⋙ G B y ⟶ G B x ⋙ compositionF B c' :=
  Functor.whiskerLeft (J B c.i) (exchange B s c'.g c.g y wp) ≫
  Functor.whiskerRight (beta B x c'.i c.i s wi si).hom (R B c'.g)
```

```lean
noncomputable def compositionHorizontalE {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :
    (compositionF B T.cf ⋙ compositionF B T.cg) ⋙ G B g ⟶
      G B x ⋙ (compositionF B T'.cf ⋙ compositionF B T'.cg) :=
  Functor.whiskerLeft (compositionF B T.cf) (compositionEh B A) ≫
  Functor.whiskerRight (compositionEf B A) (compositionF B T'.cg)

end AlgebraicGeometry.ProEtale.StrictTower
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | unclaimed | Remove identity associator/unitor factors in four definitions; unchanged signatures. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | W2 | Prove the two open theorems and adapt the private invertibility factorization to the simplified formula. |
| Sheaf.Paper.RefinementExchangeCoherence | unclaimed (H4 completed it during this session) | Forced adaptations of refinementComparison_factor and compositionE_factor; unchanged signatures and data. |

The current, fully proved H4 module fails against these maps at its original lines
162 and 588. Both failures are `Tactic rfl failed`: the normalized expression is
not definitionally equal to the old `refinementPasting` or `exchangePasting`.
Add the proved private helpers `refinementPasting_normalized` and
`exchangePasting_normalized`, then apply their symmetric equalities in
`refinementComparison_factor` and `compositionE_factor`. The first proof also binds
the two quasi-compactness instances already specified in its let-bound statement.
These are the only existing proof bodies changed. All public signatures, definition
bodies, imports and all other proofs of the latest H4 module are preserved. Its
zero-sorry proof is retained. The source module and its adaptation were compiled
separately against the normalized maps: only the original has the two errors.

All target signatures are unchanged. Targets using the maps retain their meaning:
the omitted factors have identity components. Because their definitions are in the
target closure, the semantic statement check is reopened for this representation change.

## Status

landed 20261021T001149-L-1378991 2026-10-21 (merge of deliver/W2/Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting)
