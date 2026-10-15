# AlgebraicGeometry.ProEtale.CondensedRing derived coefficient comparison signatures

## Reason

Repair H10 of reviewer X-84c36 in place. Single-file checking did not reproduce the
export timeout. Profiling the required exporting compilation identified the `sineQuaNon`
premise-index extension: computing relevant constants of the two public `IsIso derivedPushHom`
instance signatures cost about 12 and 14 seconds. Its repeated `getFunInfo` calls traversed
partially applied derived-functor constructions in the comparison's expanded source and target.
The same issue affects `isIso_derivedLowerShriekHom` in this dependency itself.

Name the source and target composite functors of both comparisons, and use those names in
their signatures. Each name is an ordinary definition of exactly the original composite.
The four helper types are inferred directly from their fully specified composites, avoiding
repeated unification against expanded categorical type annotations.
Both comparison construction bodies are verbatim unchanged. Their new types are definitionally
equal to their original types, including all hypotheses and inferred instances; no mathematical
statement, target, adjunction or comparison map changes. These helpers construct functors
explicitly, with no postponed data. The existing module remains intact, and no proof/module is
split or compile limit increased. The dependency is unclaimed in the local claims snapshot.
Target statements stay unchanged; the definition review for targets using these comparisons
can check semantic identity by unfolding the four aliases, since the comparison bodies are
unchanged. No weaker or stronger comparison is substituted.

## Old

Inside the original respective `Derived` and `LowerShriek` sections, with their original
variable contexts:

```lean
noncomputable def derivedPushHom :
    R((f)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R((f)_*⟦Λ'⟧) :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedComapLowerStarIso a f)

noncomputable def derivedLowerShriekHom :
    R(f)_!⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R(f)_!⟦Λ'⟧ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open⟦Λ⟧)
      (derivedPushHom a (HasCompactification.compactification f).g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionShriekIso a (HasCompactification.compactification f).i).hom
      R(((HasCompactification.compactification f).g)_*⟦Λ'⟧) ≫
    (Functor.associator _ _ _).hom
```

## New

In the same two respective contexts:

```lean
/-- The source composite of the derived coefficient pushforward comparison. Keeping the
composite as a named functor avoids repeated expansion of derived-functor data in signatures. -/
noncomputable def derivedPushSource :=
  R((f)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y))

/-- The target composite of the derived coefficient pushforward comparison. -/
noncomputable def derivedPushTarget :=
  L(Mod.extendScalars (coefficientMap a X)) ⋙ R((f)_*⟦Λ'⟧)

/-- **(Push)**: the canonical comparison `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'`, the mate of
`derivedComapLowerStarIso` along `L(Ext) ⊣ D(Res)`. It is not an isomorphism in general. -/
noncomputable def derivedPushHom :
    derivedPushSource a f ⟶ derivedPushTarget a f :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedComapLowerStarIso a f)

/-- The source composite of the derived lower-shriek coefficient comparison. -/
noncomputable def derivedLowerShriekSource :=
  R(f)_!⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y))

/-- The target composite of the derived lower-shriek coefficient comparison. -/
noncomputable def derivedLowerShriekTarget :=
  L(Mod.extendScalars (coefficientMap a X)) ⋙ R(f)_!⟦Λ'⟧

/-- **(Shriek)**: the canonical comparison `Rf_!^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!^Λ'` for
`Rf_! = Di_! ⋙ Rg_*` attached to the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the
derived (Push) comparison for the proper `g` followed by the derived (Shriek) isomorphism for
the open immersion `i`. -/
noncomputable def derivedLowerShriekHom :
    derivedLowerShriekSource a f ⟶ derivedLowerShriekTarget a f :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open⟦Λ⟧)
      (derivedPushHom a (HasCompactification.compactification f).g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionShriekIso a (HasCompactification.compactification f).i).hom
      R(((HasCompactification.compactification f).g)_*⟦Λ'⟧) ≫
    (Functor.associator _ _ _).hom
```

## Users

All fourteen transitive consumers from `tools/downstream.py` are below. The only textual
external users of `derivedPushHom` are the item, `CondensedQbarComparisons`, and
`CondensedQbarBaseChangeCompatibility`; the two latter sources are checked unchanged against
the sandbox outputs. `derivedLowerShriekHom` is also used by coefficient-comparison statements.
The existing signature representations are definitionally equal, so consumer edits are not
required. The claim holders are the local snapshot at repair time. No held module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` | unclaimed | Name the comparison endpoints; comparison constructions unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | B3 | Same comparison and definitionally equal type; no adaptation. |
| `Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful` | unclaimed | Same comparison and definitionally equal type; no adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Same comparison and definitionally equal type; no adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | B3 | Same comparison and definitionally equal type; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | A4 | Same comparison and definitionally equal type; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Same comparison and definitionally equal type; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Same comparison and definitionally equal type; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Same comparison and definitionally equal type; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | A2 | Same comparison and definitionally equal type; no adaptation. |
| `TargetsCheck` | unclaimed | Same comparison and definitionally equal type; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Same comparison and definitionally equal type; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Same comparison and definitionally equal type; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | E4 | Shared compact signatures avoid expensive premise-index export. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | B2 | Same comparison and definitionally equal type; no adaptation. |

## Status

landed 20261015T184346-L-858739 2026-10-15 (merge of deliver/E4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility)
