# CategoryTheory.internalModules_finiteContAction proof scope

## Reason

The completed proof adds a `FiniteActions` section containing private constructions,
section variables and two elaboration options. The delivery checker conservatively
records new scoped commands as an interface change. All public signatures, exported
mathematical definitions and imports are identical. These commands are closed before
the namespace ends, and affect only the new proof and its private helpers.

The proof constructs both functors explicitly and verifies their strict inverse
identities and forgetful comparison. No target statement or definition used in a target
changes meaning; no target semantic review needs to reopen.

## Old

The public declaration, verbatim before this delivery:

```lean
theorem internalModules_finiteContAction (R : Type r) [Ring R]
    (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ E : InternalModule R (ContAction FintypeCat.{u} G) ≌
        FiniteContinuousModule.{r, g, u} R G,
      E.functor ⋙ E.inverse = 𝟭 _ ∧
      E.inverse ⋙ E.functor = 𝟭 _ ∧
      ∃ i : InternalModule.forget R (ContAction FintypeCat.{u} G) ⋙
          finiteContActionForget G ≅ E.functor ⋙ FiniteContinuousModule.forget R G,
        ∀ (A : InternalModule R (ContAction FintypeCat.{u} G))
          (T : ContAction FintypeCat.{u} G) (a b : T ⟶ A.X) (t : T.obj.V),
          (fun (f : (T ⟶ A.X) → (T.obj.V → A.X.obj.V))
            (k : A.X.obj.V → (E.functor.obj A).obj.obj.V) ↦
            k (f (prod.lift a b ≫ A.add) t) = k (f a t) + k (f b t) ∧
            k (f (terminal.from T ≫ A.zero) t) = (0 : (E.functor.obj A).obj.obj.V) ∧
            k (f (a ≫ A.neg) t) = -k (f a t) ∧
            ∀ c : R, k (f (a ≫ A.smul c) t) = c • k (f a t))
            (fun h ↦ ((finiteContActionForget G).map h).hom) (i.hom.app A).hom := by
  sorry
```

There was no additional finite-action proof section at this position.

## New

The added proof scope begins as follows; all its construction declarations are private:

```lean
section FiniteActions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace InternalModule
variable {R : Type r} [Ring R]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
```

The public declaration, with the identical signature and its complete combining proof:

```lean
theorem internalModules_finiteContAction (R : Type r) [Ring R]
    (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ E : InternalModule R (ContAction FintypeCat.{u} G) ≌
        FiniteContinuousModule.{r, g, u} R G,
      E.functor ⋙ E.inverse = 𝟭 _ ∧
      E.inverse ⋙ E.functor = 𝟭 _ ∧
      ∃ i : InternalModule.forget R (ContAction FintypeCat.{u} G) ⋙
          finiteContActionForget G ≅ E.functor ⋙ FiniteContinuousModule.forget R G,
        ∀ (A : InternalModule R (ContAction FintypeCat.{u} G))
          (T : ContAction FintypeCat.{u} G) (a b : T ⟶ A.X) (t : T.obj.V),
          (fun (f : (T ⟶ A.X) → (T.obj.V → A.X.obj.V))
            (k : A.X.obj.V → (E.functor.obj A).obj.obj.V) ↦
            k (f (prod.lift a b ≫ A.add) t) = k (f a t) + k (f b t) ∧
            k (f (terminal.from T ≫ A.zero) t) = (0 : (E.functor.obj A).obj.obj.V) ∧
            k (f (a ≫ A.neg) t) = -k (f a t) ∧
            ∀ c : R, k (f (a ≫ A.smul c) t) = c • k (f a t))
            (fun h ↦ ((finiteContActionForget G).map h).hom) (i.hom.app A).hom := by
  let F := InternalModule.pointRepFunctor (R := R) (G := G)
  let I := InternalModule.repInternalFunctor (R := R) (G := G)
  have hFI : F ⋙ I = 𝟭 _ := InternalModule.pointRep_internal_comp
  have hIF : I ⋙ F = 𝟭 _ := InternalModule.internal_pointRep_comp
  let E := Equivalence.mk F I (eqToIso hFI.symm) (eqToIso hIF)
  refine ⟨E, hFI, hIF, InternalModule.pointRepForgetIso, ?_⟩
  intro A T a b t
  change InternalModule.ev (prod.lift a b ≫ A.add) t =
      InternalModule.pointAdd A (InternalModule.ev a t) (InternalModule.ev b t) ∧
    InternalModule.ev (terminal.from T ≫ A.zero) t = InternalModule.pointZero A ∧
    InternalModule.ev (a ≫ A.neg) t = InternalModule.pointNeg A (InternalModule.ev a t) ∧
    ∀ c : R, InternalModule.ev (a ≫ A.smul c) t =
      InternalModule.pointSmul A c (InternalModule.ev a t)
  exact ⟨InternalModule.add_ev A a b t, InternalModule.zero_ev A T t, rfl, fun _ ↦ rfl⟩
```

The section closes with `end FiniteActions`. The private helpers are fully proved in
`lean/Sheaf/CategoryTheory/EquivalenceInternalModule.lean`.

## Users

This delivery edits only the item held by H2. The following complete transitive importer
list was obtained with `tools/downstream.py Sheaf.CategoryTheory.EquivalenceInternalModule
--names`. Every importer sees the same public declarations and imports, so its statements
and proofs are unaffected. No consumer module is adapted; the holder column records this
rather than requesting any transfer of an existing claim.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.EquivalenceInternalModule | H2 | Completes the remaining proof; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | not adapted | Public interface and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | not adapted | Public interface and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | not adapted | Public interface and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LisseFiniteEtaleFiltration | not adapted | Public interface and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | not adapted | Public interface and target meanings unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | not adapted | Public interface and target meanings unchanged. |
| TargetsCheck | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.Statement | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.Examples | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted | Public interface and target meanings unchanged. |
| WeilConjectures.ZetaFunction.Weights | not adapted | Public interface and target meanings unchanged. |

## Status

landed 20261018T062804-L-653836 2026-10-18 (merge of deliver/H2/Sheaf.CategoryTheory.EquivalenceInternalModule)
