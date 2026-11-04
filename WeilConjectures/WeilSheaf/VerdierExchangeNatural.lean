/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CompactProjectionFormula
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.TensorHomNatural

/-!
# The Verdier exchange of Weil complexes, natural form

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
the Verdier exchange `𝔻_Y Rf₀! ≅ Rf_* 𝔻_X` (blueprint `fix-cor-verdier-exchange`) as a natural
isomorphism of functors `(WeilComplex X)ᵒᵖ ⥤ WeilComplex Y`. With Verdier biduality it identifies
`Rf^!` with `𝔻_X f^* 𝔻_Y` (`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`).

The Verdier dual `AlgebraicGeometry.WeilComplex.verdierDual` and the dualizing complex are defined
in `WeilConjectures.WeilSheaf.VerdierDual`, which imports this file; they are spelled out here:
the dualizing complex of `X` is `(Ra_X!)^{ra}(ℚ̄_ℓ)`, the right adjoint of `Ra_X!` applied to the
constant Weil sheaf on `Spec k₀`, and the Verdier dual is the derived internal hom into it, lifted
to Weil complexes along a proof that it lands there (in `VerdierDual`,
`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom_dualizingComplex`).

The proof is a Yoneda argument in two variables. For a test Weil complex `T` on `Y`, each of

`Hom(T, RHom(Rf₀! M, ω_Y)) = Hom(Rf₀! M ⊗ T, ω_Y) = Hom(Rf₀!(M ⊗ f^* T), ω_Y)`
`= Hom(M ⊗ f^* T, ω_X) = Hom(f^* T, RHom(M, ω_X)) = Hom(T, Rf_* RHom(M, ω_X))`

is an isomorphism of functors in the pair `(M, T)`: the tensor–hom adjunction
(`AlgebraicGeometry.WeilComplex.nativeConstructibleTensorYonedaIso`), the compact projection
formula (`AlgebraicGeometry.WeilComplex.nonempty_nativeCompactProjectionLeft_iso`), the
adjunctions `Ra_! ⊣ (Ra_!)^{ra}` with `Ra_{X,0}! ≅ Ra_{Y,0}! ∘ Rf₀!`, and `f^* ⊣ Rf_*`.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_natIso_derivedLowerStar_of_adjunction`: the natural
  exchange for arbitrary right adjoints of `Ra_{X,0}!`, `Ra_{Y,0}!`.
- `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_natIso`: the natural
  Verdier exchange.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable (k₀ l) in
/-- The dualizing complex `ω_X = (Ra_X!)^{ra}(ℚ̄_ℓ)` of a `k₀`-scheme of finite type `X`, given a
right adjoint of `Ra_X!` (`AlgebraicGeometry.WeilComplex.dualizingComplex`, spelled out). -/
noncomputable abbrev dualizingComplexOfIsLeftAdjoint (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [(derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint] :
    WeilComplex k₀ l X :=
  (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).rightAdjoint.obj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Verdier exchange, natural in `M`, for arbitrary adjoints** (blueprint:
`fix-cor-verdier-exchange`, with `fix-lem-tensor-adjunction`): let `a_X = f ≫ a_Y` be morphisms to a
base `S`, `G_X`, `G_Y` right adjoints of `Ra_{X,0}!` and `Ra_{Y,0}!`, and `Q` a Weil complex on `S`.
If `RHom(-, G_X Q)` and `RHom(-, G_Y Q)` land in Weil complexes, then
`RHom(Rf₀! M, G_Y Q) ≅ Rf_* RHom(M, G_X Q)` naturally in `M`.

The proof is the Yoneda argument of
`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerStar_of_adjunction`, run with `M` as a
variable: every step is an isomorphism of functors in the pair `(M, T)`. -/
theorem nonempty_natIso_derivedLowerStar_of_adjunction {S : Scheme.{u}}
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
    (Q : WeilComplex k₀ l S)
    (hX : ∀ K : WeilComplex k₀ l X, WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj).obj (op K.obj)))
    (hY : ∀ K : WeilComplex k₀ l Y, WeilComplex.objectProperty k₀ l Y
      ((ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj).obj (op K.obj))) :
    Nonempty ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop) ≅
      ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop) ⋙
        derivedLowerStar f) := by
  subst h
  obtain ⟨π⟩ := nonempty_nativeCompactProjectionLeft_iso (k₀ := k₀) (l := l) f
  obtain ⟨c⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f aY
  let DX := ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
    ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop)
  let DY := ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
    ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)
  -- `P ↦ Hom(Rf₀! P, G_Y Q)` is `P ↦ Hom(P, G_X Q)`.
  let q : (derivedLowerShriek k₀ l f).op ⋙ yoneda.obj (GY.obj Q) ≅ yoneda.obj (GX.obj Q) :=
    Functor.isoWhiskerLeft (derivedLowerShriek k₀ l f).op (adjY.compYonedaIso.app Q) ≪≫
      Functor.isoWhiskerRight (NatIso.op c) (yoneda.obj Q) ≪≫ (adjX.compYonedaIso.app Q).symm
  let e : Functor.uncurry.obj (((derivedLowerShriek k₀ l f).op ⋙ DY) ⋙ yoneda) ≅
      Functor.uncurry.obj ((DX ⋙ derivedLowerStar f) ⋙ yoneda) :=
    (Iso.refl _ : _ ≅ ((derivedLowerShriek k₀ l f).op.prod (𝟭 (WeilComplex k₀ l Y)ᵒᵖ)) ⋙
        Functor.uncurry.obj (DY ⋙ yoneda)) ≪≫
      Functor.isoWhiskerLeft _ (nativeConstructibleTensorYonedaIso (GY.obj Q) hY).symm ≪≫
      (Iso.refl _ : _ ≅ (prodOpEquiv _).inverse ⋙ (nativeCompactProjectionLeft k₀ l f).op ⋙
        yoneda.obj (GY.obj Q)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (NatIso.op π.symm) _) ≪≫
      (Iso.refl _ : _ ≅ (prodOpEquiv _).inverse ⋙
        ((𝟭 (WeilComplex k₀ l X)).prod (upperStar (k₀ := k₀) (l := l) f) ⋙
          nativeConstructibleTensor k₀ l X).op ⋙
        (derivedLowerShriek k₀ l f).op ⋙ yoneda.obj (GY.obj Q)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ q) ≪≫
      (Iso.refl _ : _ ≅ ((𝟭 (WeilComplex k₀ l X)ᵒᵖ).prod (upperStar (k₀ := k₀) (l := l) f).op) ⋙
        (prodOpEquiv _).inverse ⋙ (nativeConstructibleTensor k₀ l X).op ⋙
          yoneda.obj (GX.obj Q)) ≪≫
      Functor.isoWhiskerLeft _ (nativeConstructibleTensorYonedaIso (GX.obj Q) hX) ≪≫
      (Iso.refl _ : _ ≅ Functor.uncurry.obj (DX ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (upperStar (k₀ := k₀) (l := l) f).op)) ≪≫
      Functor.uncurry.mapIso
        (Functor.isoWhiskerLeft DX (upperStarDerivedLowerStarAdjunction f).compYonedaIso.symm)
  exact ⟨(Yoneda.fullyFaithful.whiskeringRight _).preimageIso
    (Functor.currying.fullyFaithfulFunctor.preimageIso e)⟩

variable [(derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint]
  [(derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint]

/-- **Verdier exchange, natural in `M`** (blueprint `fix-cor-verdier-exchange`): for a separated
morphism of finite type `f : X ⟶ Y`, `𝔻_Y (Rf₀! M) ≅ Rf_* (𝔻_X M)` naturally in the Weil
complex `M`. Here `𝔻 = RHom(-, ω)` is the derived internal hom into the dualizing complex
`ω = (Ra!)^{ra}(ℚ̄_ℓ)`, lifted to Weil complexes along any proofs `hX`, `hY` that it lands there.

It is stated here because the Verdier dual is only defined in
`WeilConjectures.WeilSheaf.VerdierDual`, which imports this file. It is the case
`G = (Ra!)^{ra}`, `Q = ℚ̄_ℓ` of
`AlgebraicGeometry.WeilComplex.nonempty_natIso_derivedLowerStar_of_adjunction`; the objectwise
form is `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso`. -/
theorem nonempty_verdierDual_derivedLowerShriek_natIso
    (hX : ∀ K : WeilComplex k₀ l X, WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplexOfIsLeftAdjoint k₀ l X).obj).obj
        (op K.obj)))
    (hY : ∀ K : WeilComplex k₀ l Y, WeilComplex.objectProperty k₀ l Y
      ((ProEtaleWeilSheaf.derivedHom k₀ l Y (dualizingComplexOfIsLeftAdjoint k₀ l Y).obj).obj
        (op K.obj))) :
    Nonempty ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (dualizingComplexOfIsLeftAdjoint k₀ l Y).obj)
          (fun K ↦ hY K.unop) ≅
      ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplexOfIsLeftAdjoint k₀ l X).obj)
          (fun K ↦ hX K.unop) ⋙ derivedLowerStar f) :=
  nonempty_natIso_derivedLowerStar_of_adjunction f _ _ (comp_over f _)
    (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _) _ hX hY

end WeilComplex

end AlgebraicGeometry
