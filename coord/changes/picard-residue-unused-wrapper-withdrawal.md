# Retire the unused Picard residue wrapper chain

## Reason

The current parent `AlgebraicGeometry.Scheme.picard_h1_fixed_model_comparison`
already uses `picard_residue_homology_chosen_geometric_maps` from
`Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison`.
The BYPASS-picardh1 parent route, dated 2026-10-15 and reviewed in the parent node,
removed the edge to `lem-sc-picard-fixed-model-residue-chain-comparison`.
All seven modules below are outside the `TargetsCheck` import closure. Their only
Lean callers and DAG users are inside this same seven-module, eight-node chain;
the outer chain-comparison module has no caller. None realizes a blueprint unit
statement or proof step. The item brief §8d requires withdrawal of an item made
unnecessary by the root route; §8b requires withdrawing its remaining callers in
the same delivery. All six other modules are unclaimed.

This is pruning, not a proof of the corrected per-index naturality statement.
No false arbitrary-comparison statement is restored. The mathematical DAG nodes,
including their corrected statements and proof plans, remain; only their Lean
attachments are detached. The direct parent route and its existing chosen-map
obligation remain as they stood in the checkout.

## Old

The public signatures withdrawn are reproduced verbatim below.

### Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex

```lean
theorem picard_residue_homology_geometric_naturality_fixed_positive_per_index
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
    (hn : 0 < n) :
    ∃ (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1),
      ∀ i : Fin n,
        ∃ (eCi : affineResidueCycleHomology W U p (C i) ≃+
            Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
          (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i)),
      ∀ (φ : K ⟶ C i), DerivedCategory.Q.map φ = a →
        ∀ z : affineResidueCycleHomology W U p K,
          eCi (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eK z)
```

### Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed

```lean
theorem picard_residue_homology_geometric_naturality_fixed_positive
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
    (hn : 0 < n) :
    ∃ (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i)),
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
        ∀ z : affineResidueCycleHomology W U p K,
          eC i (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eK z)

theorem picard_residue_homology_geometric_naturality_fixed
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    ∃ (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i)),
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
        ∀ z : affineResidueCycleHomology W U p K,
          eC i (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eK z)
```

### Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality

```lean
theorem picard_residue_homology_geometric_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    ∃ (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i)),
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
        ∀ z : affineResidueCycleHomology W U p K,
          eC i (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eK z)
```

### Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality

```lean
theorem picard_residue_cycles_geometric_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCnegative : ∀ i j, j < 0 → IsZero ((C i).X j))
    (hCzero : ∀ i, (C i).d 0 1 = 0)
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    let p := RingHom.ker (W.evaluation U w hwU).hom
    letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    let ZK := LinearMap.ker
      ((show (K.X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
        (K.X 2).val.obj (.op (Over.mk (𝟙 U))) from
          ((K.d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField)
    let Z := fun i ↦ LinearMap.ker
      ((show ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
        ((C i).X 2).val.obj (.op (Over.mk (𝟙 U))) from
          (((C i).d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField)
    ∃ (γ : ZK →+ Sheaf.H
        (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i))
      (β : ∀ i, Z i →+ Sheaf.H (structureSheafAb
        (pullback (fi i) (S.fromSpecResidueField s))) 1),
      Function.Surjective γ ∧
      (∀ x : ZK, γ x = 0 ↔ ∃ y, ((show (K.X 0).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
        (K.X 1).val.obj (.op (Over.mk (𝟙 U))) from
          ((K.d 0 1).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField) y = x.val) ∧
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
        ∀ (x : ZK) (hy :
          ((((φ.f 1).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange
            p.ResidueField) x.val ∈ Z i),
          β i ⟨_, hy⟩ = structureSheafCohomologyPullback
            (((Over.pullback (S.fromSpecResidueField s)).map
              (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                (ui i) (hui i))).left) 1 (γ x)
```

### Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison

```lean
theorem picard_fixed_model_residue_cycle_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCnegative : ∀ i j, j < 0 → IsZero ((C i).X j))
    (hCzero : ∀ i, (C i).d 0 1 = 0)
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
    (hreszero :
      let p := RingHom.ker (W.evaluation U w hwU).hom
      letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
      ∀ j : ℤ,
        (show (K.X j).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
          (K.X (j + 1)).val.obj (.op (Over.mk (𝟙 U))) from
            ((K.d j (j + 1)).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField =
          0) :
    let p := RingHom.ker (W.evaluation U w hwU).hom
    letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    let Z := fun i ↦ LinearMap.ker
      ((show ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
        ((C i).X 2).val.obj (.op (Over.mk (𝟙 U))) from
          (((C i).d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField)
    ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i))
      (β : ∀ i, Z i →+ Sheaf.H (structureSheafAb
        (pullback (fi i) (S.fromSpecResidueField s))) 1),
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
      let b := (((φ.f 1).val.app (.op (Over.mk (𝟙 U)))).hom).comp e1.symm.toLinearMap
      ∀ z, ∃ hz : b.baseChange p.ResidueField z ∈ Z i,
        β i ⟨b.baseChange p.ResidueField z, hz⟩ =
          structureSheafCohomologyPullback
            (((Over.pullback (S.fromSpecResidueField s)).map
              (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                (ui i) (hui i))).left) 1 (α z)
```

### Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison

```lean
theorem picard_fixed_model_residue_derived_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) j w)))))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCnegative : ∀ i j, j < 0 → IsZero ((C i).X j))
    (hCzero : ∀ i, (C i).d 0 1 = 0)
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    let p := RingHom.ker (W.evaluation U w hwU).hom
    letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i))
      (γ : (p.ResidueField ⊗[Γ(W, U)]
          (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))))) →+
        (∀ i, Sheaf.H (structureSheafAb
          (pullback (fi i) (S.fromSpecResidueField s))) 1)),
      ∀ (φ : ∀ i, K ⟶ C i), (∀ i, DerivedCategory.Q.map (φ i) = a i) →
      let t : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)]
          (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U)))) :=
        LinearMap.pi (fun i ↦
          (((φ i).f 1).val.app (.op (Over.mk (𝟙 U)))).hom.comp e1.symm.toLinearMap)
      ∀ z, γ (t.baseChange p.ResidueField z) = fun i ↦
        structureSheafCohomologyPullback
          (((Over.pullback (S.fromSpecResidueField s)).map
            (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
              (ui i) (hui i))).left) 1 (α z)
```

### Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison

```lean
theorem picard_fixed_model_residue_chain_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) j w)))))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCnegative : ∀ i j, j < 0 → IsZero ((C i).X j))
    (hCzero : ∀ i, (C i).d 0 1 = 0)
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    let p := RingHom.ker (W.evaluation U w hwU).hom
    letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (t : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)]
        (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U)))))
      (γ : (p.ResidueField ⊗[Γ(W, U)]
          (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))))) →+
        (∀ i, Sheaf.H (structureSheafAb
          (pullback (fi i) (S.fromSpecResidueField s))) 1)),
      (∀ a, t (e1 ((K.d 0 1).val.app
        (.op (Over.mk (𝟙 U))) (e0.symm a))) = 0) ∧
      ∀ z, γ (t.baseChange p.ResidueField z) = fun i ↦
        structureSheafCohomologyPullback
          (((Over.pullback (S.fromSpecResidueField s)).map
            (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
              (ui i) (hui i))).left) 1 (α z)
```

## New

Each path is listed in `deleted.txt`. The delivery tool lands each withdrawal as:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

No replacement theorem, definition, axiom or admitted lemma is introduced.
The eight existing node copies set `lean` to `null`, which removes the obsolete
attachment. Their statements, proof plans, source references and unit records stay intact.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex | H2 | Withdrawn together with its only callers; no external importer. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed | unclaimed | Withdrawn together with its only callers; no external importer. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality | unclaimed | Withdrawn together with its only callers; no external importer. |
| Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality | unclaimed | Withdrawn together with its only callers; no external importer. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | unclaimed | Withdrawn together with its only callers; no external importer. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | unclaimed | Withdrawn together with its only callers; no external importer. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | Withdrawn together with its only callers; no external importer. |

A whole-library import scan found exactly the six links between these modules,
and no external importer. A declaration-name scan gives no external Lean caller.
The whole DAG scan found no `proof_deps` or `stmt_deps` user outside these eight
nodes, and all unit `realized` records were checked for these IDs.

## Status

landed 20261014T205125-L-2659034 2026-10-14 (merge of deliver/H2/Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex)
