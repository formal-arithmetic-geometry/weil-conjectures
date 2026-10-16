# integralMatrixFunctions, integralFunctionInclusion, integralFiniteFreePullbackIso

## Reason

The analytic proof needs lower modules for coefficient pullback and pointwise rank. Those modules must use the existing matrix-chart data without importing the theorem being proved, so the data moves into `Sheaf.Paper.IntegralMatrixAnalyticData`. The original three definitions and anonymous IsMonHom instance are copied verbatim. The original module publicly imports this lower module, preserving the old declaration names, types, reduction behavior and public visibility.

New abbreviations name normalized pullback and its conjugated finite-free map. New definitions name the regular coefficient, the regular pullback isomorphism, and the continuous functions of the pulled-back matrix. Each is an explicit construction. The new regular comparison, matrix-functions wrapper and continuous-function pushforward are irreducible to stop elaboration repeatedly unfolding the entire inverse-image, scalar-restriction and biproduct comparison term; the defining equations are unfolded explicitly in the corresponding proved APIs. Only newly introduced definitions receive irreducibility attributes; the original relocated definitions retain their reduction behavior and meaning. This addresses the costly definition itself; no wall-clock compilation limit is raised.

No target signature or definition used by a target changes mathematically. No existing consumer needs a source adaptation. This is a module relocation with a public reexport and additional explicit helper definitions.

## Old

The definitions in `Sheaf.Paper.IntegralMatrixAnalyticCover`, verbatim:

```lean
noncomputable def integralMatrixFunctions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (e : condensedRingObj (integralCoeff ℓ E) X ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (continuousIntegers ℓ E))) [IsIso e]
    {n t : ℕ}
    (f : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t) :
    Matrix (Fin t) (Fin n) C(X, continuousIntegers ℓ E) := fun i j ↦
  let p := biproduct.ι _ j ≫ f ≫ biproduct.π _ i
  (((inv e ≫ p.hom ≫ e).hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down

noncomputable def integralFunctionInclusion (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X (continuousIntegers ℓ E).subtype continuous_subtype_val)

instance (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    IsMonHom (integralFunctionInclusion ℓ E X) := by
  dsimp [integralFunctionInclusion]
  infer_instance

noncomputable def integralFiniteFreePullbackIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    let R := condensedRingObj (integralCoeff ℓ E) X
    let T := (ProEtale.upperStar Ab.{u + 1} f).mapMod R ⋙
      Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) f))
    T.obj (Mod.finiteFree R n) ≅
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) Y) n := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P := (ProEtale.upperStar Ab.{u + 1} f).mapMod R
  let α := condensedPullbackHom (integralCoeff ℓ E) f
  let Q := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv α)
  let T := P ⋙ Q
  let e₀ : P.obj (Mod.regular R) ≅
      Mod.regular ((ProEtale.upperStar Ab.{u + 1} f).obj R) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  let e₁ : T.obj (Mod.regular R) ≅
      Mod.regular (condensedRingObj (integralCoeff ℓ E) Y) :=
    Q.mapIso e₀ ≪≫ Mod.regularIsoOfIsIso α
  exact T.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ e₁)
```

Its public imports were `Sheaf.Paper.ContinuousCoefficientRealizations` and `Mathlib.Data.Matrix.Basic`.

## New

The original module now has `public import Sheaf.Paper.IntegralMatrixAnalyticData`. That module publicly imports both former dependencies and contains the original constructions unchanged, followed by the new explicit helpers:

```lean
noncomputable def integralRegularCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X)) :
    C(X, continuousIntegers ℓ E) :=
  let e := chartComparison X (continuousIntegers ℓ E)
  (((inv e ≫ p.hom ≫ e).hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down

noncomputable def integralMatrixFunctions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (e : condensedRingObj (integralCoeff ℓ E) X ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (continuousIntegers ℓ E))) [IsIso e]
    {n t : ℕ}
    (f : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t) :
    Matrix (Fin t) (Fin n) C(X, continuousIntegers ℓ E) := fun i j ↦
  let p := biproduct.ι _ j ≫ f ≫ biproduct.π _ i
  (((inv e ≫ p.hom ≫ e).hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down

noncomputable def integralFunctionInclusion (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X (continuousIntegers ℓ E).subtype continuous_subtype_val)

instance (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    IsMonHom (integralFunctionInclusion ℓ E X) := by
  dsimp [integralFunctionInclusion]
  infer_instance

@[irreducible] noncomputable def integralRegularPullbackIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let R := condensedRingObj (integralCoeff ℓ E) X
    let T := (ProEtale.upperStar Ab.{u + 1} f).mapMod R ⋙
      Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) f))
    T.obj (Mod.regular R) ≅
      Mod.regular (condensedRingObj (integralCoeff ℓ E) Y) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P := (ProEtale.upperStar Ab.{u + 1} f).mapMod R
  let α := condensedPullbackHom (integralCoeff ℓ E) f
  let Q := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv α)
  let e₀ : P.obj (Mod.regular R) ≅
      Mod.regular ((ProEtale.upperStar Ab.{u + 1} f).obj R) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  exact Q.mapIso e₀ ≪≫ Mod.regularIsoOfIsIso α

noncomputable def integralFiniteFreePullbackIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    let R := condensedRingObj (integralCoeff ℓ E) X
    let T := (ProEtale.upperStar Ab.{u + 1} f).mapMod R ⋙
      Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) f))
    T.obj (Mod.finiteFree R n) ≅
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) Y) n := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P := (ProEtale.upperStar Ab.{u + 1} f).mapMod R
  let α := condensedPullbackHom (integralCoeff ℓ E) f
  let Q := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv α)
  let T := P ⋙ Q
  let e₀ : P.obj (Mod.regular R) ≅
      Mod.regular ((ProEtale.upperStar Ab.{u + 1} f).obj R) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  let e₁ : T.obj (Mod.regular R) ≅
      Mod.regular (condensedRingObj (integralCoeff ℓ E) Y) :=
    Q.mapIso e₀ ≪≫ Mod.regularIsoOfIsIso α
  exact T.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ e₁)

noncomputable abbrev integralMatrixPullback (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) :=
  (ProEtale.upperStar Ab.{u + 1} g).mapMod (condensedRingObj (integralCoeff ℓ E) X) ⋙
    Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) g))

noncomputable abbrev integralMatrixPullbackMap (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t) :=
  (integralFiniteFreePullbackIso ℓ E g n).inv ≫
    (integralMatrixPullback ℓ E g).map a ≫ (integralFiniteFreePullbackIso ℓ E g t).hom

@[irreducible] noncomputable def integralMatrixPullbackFunctions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t) :
    Matrix (Fin t) (Fin n) C(Y, continuousIntegers ℓ E) :=
  integralMatrixFunctions ℓ E Y (chartComparison Y (continuousIntegers ℓ E))
    (integralMatrixPullbackMap ℓ E g a)

@[irreducible] noncomputable def continuousFunctionPushforward {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X O) ⟶
    (ProEtale.lowerStar Ab.{u + 1} f).obj
      ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf Y O)) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ULift.up
            (s.down.comp (pullback.fst U.unop.hom f).base.hom)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro U V g
       apply ConcreteCategory.hom_ext
       intro s
       apply ULift.ext
       change (s.down.comp g.unop.left.base.hom).comp
         (pullback.fst V.unop.hom f).base.hom =
           (s.down.comp (pullback.fst U.unop.hom f).base.hom).comp
             ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left.base.hom
       have h : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left ≫
           pullback.fst U.unop.hom f = pullback.fst V.unop.hom f ≫ g.unop.left := by
         exact pullback.lift_fst _ _ _
       ext x
       exact congrArg (fun h : pullback V.unop.hom f ⟶ U.unop.left ↦ s.down (h x)) h.symm }⟩

theorem continuousFunctionPushforward_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O]
    (U : X.ProEt) (s : ULift.{u + 1} C(U.left, O)) :
    ((continuousFunctionPushforward f O).hom.app (op U)) s =
      ULift.up (s.down.comp (pullback.fst U.hom f).base.hom) := by
  unfold continuousFunctionPushforward
  rfl

theorem continuousFunctionPushforward_app_one {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] (U : X.ProEt) :
    ((continuousFunctionPushforward f O).hom.app (op U)) (ULift.up 1) =
      ULift.up 1 := by
  rw [continuousFunctionPushforward_app]
  rfl
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralMatrixAnalyticCover | C1 | Same theorem signature; publicly reexports the unchanged moved data and proves the cover by the new intermediate lemmas. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Unchanged names, signatures, data and visibility through the public reexport. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Unchanged names, signatures, data and visibility through the public reexport. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Unchanged names, signatures, data and visibility through the public reexport. |

## Status

landed 20261016T064221-L-581921 2026-10-16 (merge of deliver/C1/Sheaf.Paper.IntegralMatrixAnalyticCover)
