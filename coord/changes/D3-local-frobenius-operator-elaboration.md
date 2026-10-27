# TraceFormulaLocalFrobeniusOperator elaboration repair

## Reason

Restore the exact owning module preserved by the rework quarantine. The recorded failure was a 60-second compile timeout. The baseline now sometimes compiles, but profiling still isolates approximately 3 seconds in the dependent let-to-have transformation of the local coefficient type in `finiteGlobalCompactStep`. Inlining that alias removes the expensive transformation (3.57 ms in the repaired profile). Explicit functor and isomorphism result types keep the coefficient-complex interfaces small. Later definitions use those interfaces with local irreducibility and transparency-respecting elaboration.

The old and new constructions are definitionally identical: substituting the old local type alias gives exactly the new body. No comparison, coefficient ring, localization universe, finite-level index, or arrow order changes. Local irreducibility ends with this namespace and does not change the transparency visible to importers. No target needs a mathematical statement re-review.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

```lean
def finiteLocalFibre (T : TraceFormulaCoefficientConventions.{u})
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) :=
  proEtaleConstantRingDerivedPullback T.coefficientRing z ⋙
    T.finiteLocalSections
```

```lean
def finiteLocalRho (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
    (hz : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :=
  T.finiteLocalSections.mapIso
    (eqToIso (congrArg
      (fun f ↦ (proEtaleConstantRingDerivedPullback T.coefficientRing f).obj K.obj.carrier)
      hz.symm) ≪≫
      (proEtaleConstantRingPullbackComposition z
        (T.datum.schemeFrobeniusIterate T.X₀ m) T.coefficientRing).symm.app K.obj.carrier)
```

```lean
def finiteGlobalCompactSections (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) :=
  sfIntrinsicCompactSupport (frobeniusCohomologyCompactification T.datum T.X₀ c₀)
    T.coefficientRing ⋙ T.finiteLocalSections
```

```lean
def finiteGlobalCompactStep (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower 0).obj M) := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    let F := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E
    exact frobeniusCompactTransportFinite D C.l C.different F X c₀ n M ≫
      (finiteGlobalCompactSections ⟨D, C, E, n + 1, hn, X⟩ c₀).map
        ((pointPowerPullbackModel C.l F n (D.geometricGaloisFrobenius X)).hom.app M ≫
          eqToHom (congrArg
            (fun f ↦ (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing C.l F (n + 1)) f).obj M)
            (pow_one (End.of (D.geometricGaloisFrobenius X))).symm))
```

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

```lean
def finiteLocalFibre (T : TraceFormulaCoefficientConventions.{u})
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) :
    proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ⥤
      @DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  proEtaleConstantRingDerivedPullback T.coefficientRing z ⋙
    T.finiteLocalSections
```

```lean
def finiteLocalRho (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
    (hz : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :
    (T.finiteLocalFibre z).obj K.obj.carrier ≅
      (T.finiteLocalFibre z).obj
        ((proEtaleConstantRingDerivedPullback T.coefficientRing
          (T.datum.schemeFrobeniusIterate T.X₀ m)).obj K.obj.carrier) :=
  T.finiteLocalSections.mapIso
    (eqToIso (congrArg
      (fun f ↦ (proEtaleConstantRingDerivedPullback T.coefficientRing f).obj K.obj.carrier)
      hz.symm) ≪≫
      (proEtaleConstantRingPullbackComposition z
        (T.datum.schemeFrobeniusIterate T.X₀ m) T.coefficientRing).symm.app K.obj.carrier)
```

```lean
def finiteGlobalCompactSections (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) :
    proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ⥤
      @DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  sfIntrinsicCompactSupport (frobeniusCohomologyCompactification T.datum T.X₀ c₀)
    T.coefficientRing ⋙ T.finiteLocalSections
```

```lean
def finiteGlobalCompactStep (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower 0).obj M) := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    exact frobeniusCompactTransportFinite D C.l C.different
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E) X c₀ n M ≫
      (finiteGlobalCompactSections ⟨D, C, E, n + 1, hn, X⟩ c₀).map
        ((pointPowerPullbackModel C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E) n
          (D.geometricGaloisFrobenius X)).hom.app M ≫
          eqToHom (congrArg
            (fun f ↦ (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing C.l
                (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E) (n + 1)) f).obj M)
            (pow_one (End.of (D.geometricGaloisFrobenius X))).symm))
```

```lean
attribute [local irreducible] finiteLocalSections finiteLocalFibre finiteLocalRho
  finiteLocalFrobenius finiteGlobalCompactSections finiteGlobalCompactStep
```

## Users

`tools/downstream.py Sheaf.Paper.TraceFormulaLocalFrobeniusOperator --allow-missing --uses ...` reports zero live downstream modules and zero live declaration users. This is a consequence of quarantine, not permission to withdraw the construction. The four direct archived importers are retained and inspected separately:

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed in snapshot | Archived direct importer; definitionally identical API and maps; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed in snapshot | Archived direct importer; definitionally identical API and maps; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed in snapshot | Archived direct importer; definitionally identical API and maps; no adaptation. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed in snapshot | Archived direct importer; definitionally identical API and maps; no adaptation. |

Every original public import and all ten attached declarations are restored. The node attachment, statement dependencies, and unit route are preserved. No upstream source module is changed.

## Status

landed 20261024T204539-L-3792477 2026-10-24 (merge of deliver/D3/Sheaf.Paper.TraceFormulaLocalFrobeniusOperator)
