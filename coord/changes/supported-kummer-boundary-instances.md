# AlgebraicGeometry.Etale.SupportedKummerBoundary

## Reason

The interface's Ext arguments stored global sheafification/Grothendieck instance expressions,
while the recorded unbounded derived category stores opaque instance proofs. Comparing them
unfolds the sheafification construction in the kernel. In isolated original-target clauses,
the boundary specification cost about ten seconds, its uniqueness clause eight seconds,
and the scalar clause exceeded twelve thousand kernel heartbeats. The full target statement
alone required twenty-six seconds, and the final complete proof exceeded the file limit.

Select the existing derived-category instance proofs locally when elaborating this definition.
The written signature and body are identical. Their implicit instance arguments now coincide
with the derived interfaces. All differing instance arguments are proofs of the same properties;
proof irrelevance gives the original construction and predicate. No mathematical statement or
normalization changes. This is a repair of the stored instance expressions, not a new predicate.
The local selections export no instances. The auxiliary names have no stable source API;
source refactors may require updating these selections. The auxLemma linter is disabled only
on the attribute command that deliberately names these existing source declarations.

## Old

```lean
@[irreducible]
def SupportedKummerBoundary (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤)))
    (c : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2) : Prop :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  ∀ (W : T.Opens) (_hW : (W : Set T) = (Set.range i.base)ᶜ),
    ∃ (τ : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj
          (op (Scheme.Etale.mk W.ι)))
      (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (a : T.gmSheaf ⟶ E)
      (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
      (f : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf ⟶
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj E),
      Scheme.Modules.etaleIsoTorsorVal (Scheme.Modules.dual i.ker.toModules) τ =
        supportedDivisorSectionPullback i W ∧
      (∀ (U : T.Etaleᵒᵖ) (g : T.gmSheaf.obj.obj U)
        (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        @id (E.obj.obj U) (f.hom.app U ((Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).vadd U g p)) =
          a.hom.app U g + (@id (E.obj.obj U) (f.hom.app U p))) ∧
      (∀ (U : T.Etaleᵒᵖ) (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        b.hom.app U (f.hom.app U p) =
          ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
            ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from U.unop).op
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) ∧
      @id (E.obj.obj (op (Scheme.Etale.mk W.ι)))
        (f.hom.app (op (Scheme.Etale.mk W.ι)) τ) = 0 ∧
      (Ext.mk₀ (supportedIntegralGenerator A i)).comp
          (c.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2) =
        (hE.extClass.comp (T.kummerSequence_shortExact N hT).extClass (rfl : 1 + 1 = 2)).comp
          (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 2)

/-- The canonical closed-immersion exchange on the constant sheaf.
Source: Stacks 0A45, base change (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedConstantExchange (A : Type (u + 1)) [CommRing A]
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : CommSq w i' i v) :
    (upperStar (ModuleCat.{u + 1} A) v).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D') :=
  (baseChangeMap (ModuleCat.{u + 1} A) sq).app (ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i').map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) w).app
        (ModuleCat.of A A)).hom
```

## New

```lean
section

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

@[irreducible]
def SupportedKummerBoundary (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤)))
    (c : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2) : Prop :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  ∀ (W : T.Opens) (_hW : (W : Set T) = (Set.range i.base)ᶜ),
    ∃ (τ : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj
          (op (Scheme.Etale.mk W.ι)))
      (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (a : T.gmSheaf ⟶ E)
      (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
      (f : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf ⟶
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj E),
      Scheme.Modules.etaleIsoTorsorVal (Scheme.Modules.dual i.ker.toModules) τ =
        supportedDivisorSectionPullback i W ∧
      (∀ (U : T.Etaleᵒᵖ) (g : T.gmSheaf.obj.obj U)
        (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        @id (E.obj.obj U) (f.hom.app U ((Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).vadd U g p)) =
          a.hom.app U g + (@id (E.obj.obj U) (f.hom.app U p))) ∧
      (∀ (U : T.Etaleᵒᵖ) (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        b.hom.app U (f.hom.app U p) =
          ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
            ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from U.unop).op
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) ∧
      @id (E.obj.obj (op (Scheme.Etale.mk W.ι)))
        (f.hom.app (op (Scheme.Etale.mk W.ι)) τ) = 0 ∧
      (Ext.mk₀ (supportedIntegralGenerator A i)).comp
          (c.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2) =
        (hE.extClass.comp (T.kummerSequence_shortExact N hT).extClass (rfl : 1 + 1 = 2)).comp
          (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 2)

/-- The canonical closed-immersion exchange on the constant sheaf.
Source: Stacks 0A45, base change (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedConstantExchange (A : Type (u + 1)) [CommRing A]
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : CommSq w i' i v) :
    (upperStar (ModuleCat.{u + 1} A) v).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D') :=
  (baseChangeMap (ModuleCat.{u + 1} A) sq).app (ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i').map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) w).app
        (ModuleCat.of A A)).hom

end
```

## Users

The definition module is unclaimed. Direct declaration users were enumerated with
`tools/downstream.py --uses SupportedKummerBoundary`. The table includes the new consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | N1 | Original times out against both baseline and repaired libraries; no adaptation delivered. See report.md. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | G5 | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | B3 | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary | unclaimed | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | unclaimed | Check unavailable: original TraceSystem.olean is missing from the shared build; module unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | A7 | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | Same predicate; original consumer checked against the repair. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.SupportedKummerChernRealization | B3, new | Uses the normalized boundary interface. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryPullback | B3, new | Uses the normalized boundary interface. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryScalar | B3, new | Uses the normalized boundary interface. |

The existing definitions and targets using them require independent definition review.
Original consumer checks and any necessary forced adaptations are recorded in report.md.

## Status

landed 20261020T211631-L-3481036 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer)
