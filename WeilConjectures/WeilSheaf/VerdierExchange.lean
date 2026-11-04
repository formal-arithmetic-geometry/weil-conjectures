/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CompactProjectionFormula
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# The Verdier exchange for Weil complexes

Let `f : X ⟶ Y` be a separated morphism of finite type of separated `k₀`-schemes of finite type
over a base `S`, with structure morphisms `a_X = f ≫ a_Y`, and let `G_X`, `G_Y` be right adjoints
of the direct images with compact support `Ra_{X,0}!`, `Ra_{Y,0}!` of Weil complexes. For a Weil
complex `Q` on `S` put `ω_X = G_X Q` and `ω_Y = G_Y Q`. Then for every Weil complex `M` on `X`,

`RHom(Rf₀! M, ω_Y) ≅ Rf_* RHom(M, ω_X)`

(blueprint: `fix-cor-verdier-exchange`). The proof is the Yoneda argument of
`fix-lem-tensor-adjunction`: for a test Weil complex `T` on `Y`,

`Hom(T, RHom(Rf₀! M, ω_Y)) = Hom(Rf₀! M ⊗ T, ω_Y) = Hom(Rf₀!(M ⊗ f^* T), ω_Y)`
`= Hom(Ra_{X,0}!(M ⊗ f^* T), Q) = Hom(M ⊗ f^* T, ω_X) = Hom(f^* T, RHom(M, ω_X))`
`= Hom(T, Rf_* RHom(M, ω_X))`,

using the tensor–hom adjunction of the native derived tensor product
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison`), the compact-support
projection formula (`AlgebraicGeometry.WeilComplex.nonempty_nativeCompactProjectionLeft_iso`),
the composition law `Ra_{X,0}! ≅ Ra_{Y,0}! ∘ Rf₀!` and the adjunction `f^* ⊣ Rf_*`. In particular
no exceptional inverse image `Rf^!` along `f` is needed.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerStar_of_adjunction`: the exchange.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The tensor–hom adjunction for the derived internal hom** of pro-étale Weil sheaves
(blueprint: `def-weil-derived-pullback-tensor-hom`): `Hom(P ⊗ T, Q) ≅ Hom(T, RHom(P, Q))`,
naturally in `T`, the tensor product being the native derived tensor product. -/
noncomputable def nativeDerivedTensorOpCompYonedaIso
    (P Q : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (Prod.sectR P _ ⋙ nativeDerivedTensor k₀ l X).op ⋙ yoneda.obj Q ≅
      yoneda.obj ((derivedHom k₀ l X Q).obj (op P)) := by
  letI := (nativeDerivedClosedComparison k₀ l X).weilClosed.monoidal
  letI := (nativeDerivedClosedComparison k₀ l X).weilSymmetry
  let e : tensorRight P ≅ Prod.sectR P _ ⋙ nativeDerivedTensor k₀ l X :=
    (BraidedCategory.tensorLeftIsoTensorRight P).symm ≪≫
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
        dsimp [nativeDerivedTensor, WeilConjectures.CoefficientClosedStructure.tensor]
        change P ◁ g ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 P ⊗ₘ g)
        simp)
  exact Functor.isoWhiskerRight (NatIso.op e) _ ≪≫
    (((nativeDerivedClosedComparison k₀ l X).weilClosed.adjunction P).compYonedaIso.app Q).symm ≪≫
    yoneda.mapIso (((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q).app (op P))

end ProEtaleWeilSheaf

namespace WeilComplex

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The tensor–hom adjunction on Weil complexes**: if a Weil complex `A` represents
`RHom(M, Q)`, then `Hom(M ⊗ T, Q) ≅ Hom(T, A)`, naturally in the Weil complex `T`. -/
noncomputable def nativeConstructibleTensorOpCompYonedaIso (M Q A : WeilComplex k₀ l X)
    (e : A.obj ≅ (ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj).obj (op M.obj)) :
    (Prod.sectR M _ ⋙ nativeConstructibleTensor k₀ l X).op ⋙ yoneda.obj Q ≅ yoneda.obj A :=
  Functor.isoWhiskerLeft _ ((objectProperty k₀ l X).fullyFaithfulι.opCompYonedaObjIso Q).symm ≪≫
    (Functor.isoWhiskerLeft (objectProperty k₀ l X).ι.op
      (ProEtaleWeilSheaf.nativeDerivedTensorOpCompYonedaIso M.obj Q.obj ≪≫
        yoneda.mapIso e.symm)) ≪≫
    (objectProperty k₀ l X).fullyFaithfulι.opCompYonedaObjIso A

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- **Verdier exchange** (blueprint: `fix-cor-verdier-exchange`, with `fix-lem-tensor-adjunction`):
let `a_X = f ≫ a_Y` be morphisms to a base `S`, `G_X`, `G_Y` right adjoints of `Ra_{X,0}!` and
`Ra_{Y,0}!`, and `Q` a Weil complex on `S`. If the Weil complexes `D_Y` and `D_X` represent
`RHom(Rf₀! M, G_Y Q)` and `RHom(M, G_X Q)`, then `D_Y ≅ Rf_* D_X`. -/
theorem nonempty_iso_derivedLowerStar_of_adjunction {S : Scheme.{u}}
    [S.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (S ↘ Spec (CommRingCat.of k₀))]
    (aX : X ⟶ S) (aY : Y ⟶ S) [aX.IsOver (Spec (CommRingCat.of k₀))]
    [aY.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : f ≫ aY = aX) {GX : WeilComplex k₀ l S ⥤ WeilComplex k₀ l X}
    {GY : WeilComplex k₀ l S ⥤ WeilComplex k₀ l Y}
    (adjX : derivedLowerShriek k₀ l aX ⊣ GX) (adjY : derivedLowerShriek k₀ l aY ⊣ GY)
    (Q : WeilComplex k₀ l S) (M : WeilComplex k₀ l X) (DY : WeilComplex k₀ l Y)
    (DX : WeilComplex k₀ l X)
    (eY : DY.obj ≅ (ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj).obj
      (op ((derivedLowerShriek k₀ l f).obj M).obj))
    (eX : DX.obj ≅ (ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj).obj (op M.obj)) :
    Nonempty (DY ≅ (derivedLowerStar f).obj DX) := by
  subst h
  obtain ⟨π⟩ := nonempty_nativeCompactProjectionLeft_iso (k₀ := k₀) (l := l) f
  obtain ⟨c⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f aY
  -- `T ↦ Rf₀! M ⊗ T` is `T ↦ Rf₀!(M ⊗ f^* T)`.
  let p : Prod.sectR ((derivedLowerShriek k₀ l f).obj M) _ ⋙ nativeConstructibleTensor k₀ l Y ≅
      upperStar f ⋙ (Prod.sectR M _ ⋙ nativeConstructibleTensor k₀ l X) ⋙
        derivedLowerShriek k₀ l f :=
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
        simp only [Functor.comp_map, Functor.prod_map, Prod.sectR_map, Functor.id_map,
          Iso.refl_hom, Category.comp_id, Category.id_comp]
        erw [CategoryTheory.Functor.map_id]
        rfl) :
        Prod.sectR ((derivedLowerShriek k₀ l f).obj M) _ ⋙ nativeConstructibleTensor k₀ l Y ≅
          Prod.sectR M _ ⋙ nativeCompactProjectionLeft k₀ l f) ≪≫
      Functor.isoWhiskerLeft (Prod.sectR M _) π ≪≫
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by simp [nativeConstructibleTensor]) :
        Prod.sectR M _ ⋙ nativeCompactProjectionRight k₀ l f ≅
          upperStar f ⋙ (Prod.sectR M _ ⋙ nativeConstructibleTensor k₀ l X) ⋙
            derivedLowerShriek k₀ l f)
  -- `P ↦ Hom(Rf₀! P, G_Y Q)` is `P ↦ Hom(P, G_X Q)`.
  let q : (derivedLowerShriek k₀ l f).op ⋙ yoneda.obj (GY.obj Q) ≅ yoneda.obj (GX.obj Q) :=
    Functor.isoWhiskerLeft (derivedLowerShriek k₀ l f).op (adjY.compYonedaIso.app Q) ≪≫
      Functor.isoWhiskerRight (NatIso.op c) (yoneda.obj Q) ≪≫ (adjX.compYonedaIso.app Q).symm
  let e : yoneda.obj DY ≅ yoneda.obj ((derivedLowerStar f).obj DX) :=
    (nativeConstructibleTensorOpCompYonedaIso _ _ DY eY).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op p.symm) (yoneda.obj (GY.obj Q)) ≪≫
      Functor.isoWhiskerLeft (upperStar f ⋙ Prod.sectR M _ ⋙ nativeConstructibleTensor k₀ l X).op
        q ≪≫
      Functor.isoWhiskerLeft (upperStar f).op
        (nativeConstructibleTensorOpCompYonedaIso M (GX.obj Q) DX eX) ≪≫
      ((upperStarDerivedLowerStarAdjunction f).compYonedaIso.app DX).symm
  exact ⟨Yoneda.fullyFaithful.preimageIso e⟩

end WeilComplex

end AlgebraicGeometry
