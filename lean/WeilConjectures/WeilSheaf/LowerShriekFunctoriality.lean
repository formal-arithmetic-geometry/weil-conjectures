/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.WeilSheaf.OpenImmersionRestriction
import WeilConjectures.WeilSheaf.LowerStarId
import WeilConjectures.WeilSheaf.UpperStarComp

/-!
# Functoriality of the direct image with compact support of Weil complexes

The direct image with compact support `Rf₀! = Rḡ_* ∘ ī_!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`) is defined through the compactification
`X ⟶[i] Z ⟶[g] Y` of `f` chosen by Nagata's theorem. This file records the compatibilities of
`Rf₀!` collected in the blueprint theorem `prop-functor-package` of the six-functor chapter that
the Deligne–Laumon reduction (`sec-deligne-laumon-general`) uses:

- *independence of the compactification* (clause 2), in the case of the compactification
  `U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`: `Rj₀!` is the extension by zero;
- *composition* (clause 3): `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`, and the distinguished triangle
  `R(j ≫ f)₀! j^*K ⟶ Rf₀!K ⟶ R(i ≫ f)₀! i^*K ⟶` obtained by applying `Rf₀!` to the
  localization triangle of an open immersion `j` and its closed complement `i`;
- *base change* (clause 4): `h^* Rf₀! ≅ Rf'₀! g^*` for a cartesian square;

as well as the open–closed triangle `j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶` of a Weil complex
(`prop-sf-open-closed-triangle-all-stages`). These belong to the six-functor chapter and are
proved here from compact-support base change, which remains the one package obligation.
The identification of `Rf₀!` with `Rf₀*` for proper `f` is also proved here.

## Main statements

- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar`: `Rf₀! ≅ Rf₀*` for
  `f` proper.
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion`,
  `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_iso`,
  `AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed` and
  `AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso`: clauses 2, 3 and 4 of
  `prop-functor-package`.
- `AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed`: the open–closed triangle
  (`prop-sf-open-closed-triangle-all-stages`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

/-- An open-supported object has no maps to an object supported on the closed complement. -/
private theorem openSupportOrthogonal
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject E] [HasZeroMorphisms E]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    {J : C ⥤ D} {R : D ⥤ C} {I : C ⥤ E} {S : E ⥤ C}
    [J.CommShift ℤ] [J.IsTriangulated]
    (adj : J ⊣ R) (adi : I ⊣ S) [IsIso adj.counit]
    (hs : ∀ W, IsZero (J.obj W) → S.essImage W)
    (K : C) (hK : IsZero (I.obj K)) (W : C) (hW : IsZero (J.obj W)) :
    Subsingleton (K ⟶ W) := by
  obtain ⟨Q, ⟨eW⟩⟩ := hs W hW
  have : Subsingleton (I.obj K ⟶ Q) := ⟨fun _ _ ↦ hK.eq_of_src _ _⟩
  have : Subsingleton (K ⟶ S.obj Q) := (adi.homEquiv K Q).symm.subsingleton
  exact ⟨fun f g ↦ (cancel_mono eW.inv).1 (Subsingleton.elim _ _)⟩

/-- Restriction is fully faithful on maps whose source is open-supported. The fibre and cone
of the restriction unit lie on the closed complement, so orthogonality gives both directions. -/
private theorem openSupportHom_bijective
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject E] [HasZeroMorphisms E]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    {J : C ⥤ D} {R : D ⥤ C} {I : C ⥤ E} {S : E ⥤ C}
    [J.CommShift ℤ] [J.IsTriangulated]
    (adj : J ⊣ R) (adi : I ⊣ S) [IsIso adj.counit]
    (hs : ∀ W, IsZero (J.obj W) → S.essImage W)
    (K L : C) (hK : IsZero (I.obj K)) :
    Function.Bijective (J.map : (K ⟶ L) → (J.obj K ⟶ J.obj L)) := by
  have ho := openSupportOrthogonal adj adi hs K hK
  constructor
  · intro f g hfg
    have hu : (f - g) ≫ adj.unit.app L = 0 := by
      apply (adj.homEquiv K (J.obj L)).symm.injective
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_sub,
        Functor.map_zero, Category.assoc, adj.left_triangle_components]
      rw [hfg, sub_self, zero_comp, zero_comp]
    obtain ⟨W, a, w, hT⟩ := distinguished_cocone_triangle₁ (adj.unit.app L)
    have hW : IsZero (J.obj W) :=
      (Triangle.isZero₁_iff_isIso₂ _ (J.map_distinguished _ hT)).2
        (Recollement.isIso_map_unit_app J adj L)
    have := ho W hW
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ _ hT (f - g) hu
    change K ⟶ W at b
    change f - g = b ≫ a at hb
    have : b = 0 := Subsingleton.elim _ _
    rw [this, zero_comp] at hb
    exact sub_eq_zero.1 hb
  · intro f
    let a := (adj.homEquiv K (J.obj L)) f
    obtain ⟨W, v, w, hT⟩ := distinguished_cocone_triangle (adj.unit.app L)
    have hW : IsZero (J.obj W) :=
      (Triangle.isZero₃_iff_isIso₁ _ (J.map_distinguished _ hT)).2
        (Recollement.isIso_map_unit_app J adj L)
    have := ho W hW
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ _ hT a
      (show a ≫ v = 0 from Subsingleton.elim _ _)
    change K ⟶ L at b
    change a = b ≫ adj.unit.app L at hb
    refine ⟨b, ?_⟩
    apply (adj.homEquiv K (J.obj L)).injective
    change _ = a
    rw [hb, Adjunction.homEquiv_unit]
    exact (adj.unit.naturality b).symm

/-- Lift a natural isomorphism on the open piece. Uniqueness of each lifted map supplies
naturality, and the two restrictions detect invertibility. -/
private theorem openSupportNatIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject E] [HasZeroMorphisms E]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    {J : C ⥤ D} {R : D ⥤ C} {I : C ⥤ E} {S : E ⥤ C}
    [J.CommShift ℤ] [J.IsTriangulated]
    (adj : J ⊣ R) (adi : I ⊣ S) [IsIso adj.counit]
    (hs : ∀ W, IsZero (J.obj W) → S.essImage W)
    (hr : ∀ {K L : C} (f : K ⟶ L), IsIso (I.map f) → IsIso (J.map f) → IsIso f)
    {B : Type*} [Category B] (F G : B ⥤ C)
    (hF : ∀ K, IsZero (I.obj (F.obj K))) (hG : ∀ K, IsZero (I.obj (G.obj K)))
    (e : F ⋙ J ≅ G ⋙ J) : Nonempty (F ≅ G) := by
  classical
  choose b hb using fun K ↦
    (openSupportHom_bijective adj adi hs (F.obj K) (G.obj K) (hF K)).surjective (e.hom.app K)
  have hi (K : B) : IsIso (b K) := by
    have h₁ : IsIso (I.map (b K)) :=
      isIso_of_source_target_iso_zero _ (hF K).isoZero (hG K).isoZero
    have h₂ : IsIso (J.map (b K)) := by rw [hb]; infer_instance
    exact hr _ h₁ h₂
  exact ⟨NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (b K) (hi K)) (by
    intro K L f
    apply (openSupportHom_bijective adj adi hs (F.obj K) (G.obj L) (hF K)).injective
    simpa only [Functor.map_comp, asIso_hom, hb, Functor.comp_map] using e.hom.naturality f)⟩

/-- An exact extension supported on the open and restricting to the identity is left adjoint
to restriction. This follows from the already proved restriction bijection on Hom. -/
private noncomputable def openSupportLeftAdjunction
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject E] [HasZeroMorphisms E]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    {J : C ⥤ D} {R : D ⥤ C} {I : C ⥤ E} {S : E ⥤ C}
    [J.CommShift ℤ] [J.IsTriangulated]
    (adj : J ⊣ R) (adi : I ⊣ S) [IsIso adj.counit]
    (hs : ∀ W, IsZero (J.obj W) → S.essImage W)
    (L : D ⥤ C) (hL : ∀ K, IsZero (I.obj (L.obj K)))
    (e : L ⋙ J ≅ 𝟭 D) : L ⊣ J := by
  classical
  let equiv (K : D) (M : C) : (L.obj K ⟶ M) ≃ (K ⟶ J.obj M) :=
    (Equiv.ofBijective J.map (openSupportHom_bijective adj adi hs _ _ (hL K))).trans
      (Iso.homCongr (e.app K) (Iso.refl _))
  apply Adjunction.mkOfHomEquiv
  refine
    { homEquiv := equiv
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro K K' M f g
    apply (equiv K M).injective
    rw [Equiv.apply_symm_apply]
    simp only [equiv, Equiv.trans_apply, Equiv.ofBijective_apply, Iso.homCongr_apply,
      Iso.refl_hom, Category.comp_id]
    change f ≫ g = e.inv.app K ≫ J.map (L.map f ≫ (equiv K' M).symm g)
    have hn := e.inv.naturality f
    change f ≫ e.inv.app K' = e.inv.app K ≫ J.map (L.map f) at hn
    rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
    have he := (equiv K' M).apply_symm_apply g
    simp only [equiv, Equiv.trans_apply, Equiv.ofBijective_apply, Iso.homCongr_apply,
      Iso.refl_hom, Category.comp_id] at he
    change e.inv.app K' ≫ J.map ((equiv K' M).symm g) = g at he
    exact congrArg (fun v ↦ f ≫ v) he.symm
  · intro K M M' f g
    simp only [equiv, Equiv.trans_apply, Equiv.ofBijective_apply, Iso.homCongr_apply,
      Iso.refl_hom, Category.comp_id]
    change e.inv.app K ≫ J.map (f ≫ g) = (e.inv.app K ≫ J.map f) ≫ J.map g
    rw [Functor.map_comp, Category.assoc]

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] Compactification.over

namespace WeilComplex

section Proper

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsProper f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- **For a proper morphism, the direct image with compact support is the direct image**: for the
chosen compactification `X ⟶[i] Z ⟶[g] Y` of the proper morphism `f`, the open immersion `i` is
proper, hence a closed immersion, so that `Rf₀!K = Rg_*(i_!K) ≅ Rg_*(i_*K) ≅ Rf₀*K`
(blueprint: `prop-functor-package`, clause 3, "for proper `f`, `Rf_! ≃ Rf_*`"). -/
noncomputable def derivedLowerShriekObjIsoDerivedLowerStar (K : WeilComplex k₀ l X) :
    (derivedLowerShriek k₀ l f).obj K ≅ (derivedLowerStar f).obj K := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  refine ObjectProperty.isoMk _ ?_
  change (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj K.obj) ≅ _
  exact (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.app
        K.obj).symm ≪≫
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
        (comp_over c.i _))
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm.app
        K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
      (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g))).app K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g)).app
      K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)).app
      K.obj

end Proper

section Package

variable {X Y Z U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))]

/-- **Base change for the direct image with compact support** (blueprint: `prop-functor-package`,
clause 4, `g^*Rf_! ≃ Rf'_!g'^*` for arbitrary base change, and `thm-cbc-qbar`): for a cartesian
square
```
X' --- g ---> X
|             |
f'            f
v             v
Y' --- h ---> Y
```
of `k₀`-schemes, `h^* Rf₀! ≅ Rf'₀! g^*`.

Source: blueprint `thm-cbc-qbar`, through finite-level proper base change and its coefficient
and Weil-structure comparisons. Proof plan: first establish proper base change for the actual
adic direct-image exchange on bounded constructible complexes. At finite coefficients this is
étale proper base change transported to pro-étale complexes of étale origin. Derived completion
and reduction modulo powers of the uniformizer give the integral exchange; rationalization and
finite coefficient-field descent give the algebraically closed coefficient exchange. The maps
commute with Frobenius by pasting of the same pullback/direct-image exchange transformations,
so the result lifts to Weil complexes and restricts to their constructible full subcategories.

For a compactification `c` of `f`, pull it back along `h`. Apply this proper exchange to `c.g`
after extension by zero along `c.i`, and then apply the exact extension-by-zero base-change
isomorphism. This compares the functor computed with `c` to the one computed with its pulled
back compactification. Compare that compactification to the chosen one for `f'` through their
common refinement. The refinement comparisons must here be established from the proper
exchange just described and exact extension by zero, independently of this theorem. Their
composition yields the displayed natural isomorphism. In particular, the compactification
comparisons proved below using this theorem cannot be used to discharge this obligation. -/
theorem nonempty_upperStar_derivedLowerShriek_iso {X' Y' : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
    {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
    [h.IsOver (Spec (CommRingCat.of k₀))] (hH : IsPullback g f' f h) :
    Nonempty (derivedLowerShriek k₀ l f ⋙ upperStar h ≅ upperStar g ⋙ derivedLowerShriek k₀ l f') :=
  sorry

/-- The functor version of the proper comparison: the compactifying open immersion is also
proper, so its exact extension by zero agrees with direct image. -/
private theorem properShriekIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l f ≅ derivedLowerStar f) := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  exact ⟨((WeilComplex.objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l X).ι
      (Functor.isoWhiskerRight
          (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.symm
          (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor ≪≫
        (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
          (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
            (comp_over c.i _))
          (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g
            (comp_over c.g _))).symm ≪≫
        Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
          (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
          (ProEtaleWeilSheaf.lowerStar k₀ l c.g)) ≪≫
        Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g) ≪≫
        Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)))⟩


private noncomputable def upperStarCompComplexIso (f : U ⟶ X) (g : X ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))] :
    upperStar (k₀ := k₀) (l := l) (f ≫ g) ≅ upperStar g ⋙ upperStar f :=
  ((WeilComplex.objectProperty k₀ l U).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l Z).ι
      (Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarCompIso k₀ l f g) ≪≫
        Functor.mapDerivedCategoryCompIso _ _))

private noncomputable def lowerStarCompComplexIso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (f : U ⟶ X) (g : X ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact g] [QuasiSeparated g] [LocallyOfFiniteType g]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] :
    derivedLowerStar (k₀ := k₀) (l := l) f ⋙ derivedLowerStar g ≅ derivedLowerStar (f ≫ g) :=
  (((upperStarDerivedLowerStarAdjunction g).comp
    (upperStarDerivedLowerStarAdjunction f)).ofNatIsoLeft
    (upperStarCompComplexIso f g).symm).rightAdjointUniq
      (upperStarDerivedLowerStarAdjunction (f ≫ g))

/-- The actual exact extension by zero on bounded constructible Weil complexes. Keep the
subcategory construction folded when using its restriction and support properties. -/
@[irreducible] private noncomputable def extensionComplex (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilComplex k₀ l U ⥤ WeilComplex k₀ l X :=
  (WeilComplex.objectProperty k₀ l U).liftFullSubcategory
    (WeilComplex.objectProperty k₀ l X)
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory fun K hK ↦
      ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l j).bounded_mapDerivedCategory_obj hK.1,
        fun n ↦ (WeilSheaf.objectProperty k₀ l X).prop_of_iso
          (((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategoryHomologyFunctorIso
            n).app K)
          (WeilSheaf.isAdicConstructibleSheaf_extensionByZero j _ (hK.2 n))⟩

/-- Exact sheaf-level vanishing on a disjoint subscheme passes to derived categories. -/
private theorem extensionComplex_isZero_of_disjoint (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (g : Z ⟶ X) [g.IsOver (Spec (CommRingCat.of k₀))]
    (h : Disjoint (Set.range j.base) (Set.range g.base)) (K : WeilComplex k₀ l U) :
    IsZero ((upperStar (k₀ := k₀) (l := l) g).obj
      ((extensionComplex (k₀ := k₀) (l := l) j).obj K)) := by
  apply IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
  change IsZero ((ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory.obj
    (((extensionComplex (k₀ := k₀) (l := l) j).obj K).obj))
  unfold extensionComplex
  have hz (M : ProEtaleWeilSheaf k₀ l U) :
      IsZero ((ProEtaleWeilSheaf.upperStar k₀ l g).obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l j).obj M)) := by
    apply (ProEtaleWeilSheaf.isZero_iff _).2
    exact ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek
      (Scheme.Hom.geometricFiberMap j (comp_over j _))
      (Scheme.Hom.geometricFiberMap g (comp_over g _))
      (by
        rw [Scheme.Hom.range_geometricFiberMap, Scheme.Hom.range_geometricFiberMap]
        exact Set.disjoint_iff_inter_eq_empty.1 (h.preimage _)) M.carrier
  exact DerivedCategory.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj hz K.obj

private noncomputable def extensionRestrictionIso (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    extensionComplex (k₀ := k₀) (l := l) j ⋙ upperStar j ≅ 𝟭 _ := by
  unfold extensionComplex
  exact ((WeilComplex.objectProperty k₀ l U).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l U).ι
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (asIso (Functor.whiskerRight (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l j)
              (ProEtaleWeilSheaf.upperStar k₀ l j)) ≪≫
            asIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).counit) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

private noncomputable def lowerStarIdComplexIso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    derivedLowerStar (k₀ := k₀) (l := l) (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    ((Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarIdIso k₀ l X) ≪≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _) ≪≫
        Functor.mapDerivedCategoryIdIso _)).app K.obj)) (by
    intro K L f
    apply ObjectProperty.hom_ext
    exact (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarIdIso k₀ l X) ≪≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _) ≪≫
        Functor.mapDerivedCategoryIdIso _)).hom.naturality f.hom)

private theorem isZero_of_open_closed_restrictions (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (K : WeilComplex k₀ l X)
    (hi : IsZero ((upperStar i).obj K)) (hj : IsZero ((upperStar j).obj K)) : IsZero K := by
  apply IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) K
  exact DerivedCategory.isZero_of_isZero_mapDerivedCategory_obj
    (ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij.symm)
    ((ObjectProperty.ι _).map_isZero hi) ((ObjectProperty.ι _).map_isZero hj)

private theorem isIso_of_open_closed_restrictions
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) {K L : WeilComplex k₀ l X}
    (f : K ⟶ L) (hi : IsIso ((upperStar i).map f)) (hj : IsIso ((upperStar j).map f)) :
    IsIso f := by
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) :=
    locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) :=
    locallyOfFiniteType_over_of_isOver i (S := Spec (CommRingCat.of k₀))
  obtain ⟨W, v, w, hT⟩ := distinguished_cocone_triangle f
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_open_closed_restrictions j i hij W
      ((Triangle.isZero₃_iff_isIso₁ _ ((upperStar i).map_distinguished _ hT)).2 hi)
      ((Triangle.isZero₃_iff_isIso₁ _ ((upperStar j).map_distinguished _ hT)).2 hj))

/-- Two open-supported complexes with isomorphic open restrictions are isomorphic. -/
private theorem nonempty_iso_of_open_support
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (K L : WeilComplex k₀ l X)
    (hK : IsZero ((upperStar i).obj K)) (hL : IsZero ((upperStar i).obj L))
    (e : (upperStar j).obj K ≅ (upperStar j).obj L) : Nonempty (K ≅ L) := by
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) :=
    locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  obtain ⟨a, ha⟩ := (openSupportHom_bijective
    (upperStarDerivedLowerStarAdjunction j) (upperStarDerivedLowerStarAdjunction i)
    (derivedLowerStar_essImage_of_isZero i j hij.symm) K L hK).surjective e.hom
  have hi : IsIso ((upperStar i).map a) :=
    isIso_of_source_target_iso_zero _ hK.isoZero hL.isoZero
  have hj : IsIso ((upperStar j).map a) := by rw [ha]; infer_instance
  have := isIso_of_open_closed_restrictions j i hij a hi hj
  exact ⟨asIso a⟩


private theorem nonempty_functorIso_of_open_support
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base))
    {B : Type*} [Category B] (F G : B ⥤ WeilComplex k₀ l X)
    (hF : ∀ K, IsZero ((upperStar i).obj (F.obj K)))
    (hG : ∀ K, IsZero ((upperStar i).obj (G.obj K)))
    (e : F ⋙ upperStar j ≅ G ⋙ upperStar j) : Nonempty (F ≅ G) := by
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) :=
    locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  exact openSupportNatIso (upperStarDerivedLowerStarAdjunction j)
    (upperStarDerivedLowerStarAdjunction i)
    (derivedLowerStar_essImage_of_isZero i j hij.symm)
    (fun f hi hj ↦ isIso_of_open_closed_restrictions j i hij f hi hj) F G hF hG e

/-- Compact support computed with a specified compactification, using actual extension by zero. -/
private noncomputable def shriekC
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (f : U ⟶ X)
    [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f] (c : Compactification f) :
    WeilComplex k₀ l U ⥤ WeilComplex k₀ l X :=
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  extensionComplex (k₀ := k₀) (l := l) c.i ⋙ derivedLowerStar c.g

/-- Exchange a proper direct image and exact extension by zero across a cartesian square.
Proper base change identifies their open restrictions; its closed instance makes both sides
vanish on the complement. The support comparison lifts the resulting natural isomorphism. -/
private theorem proper_open_exchange
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (V ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))]
    (a : U ⟶ Z) (q : U ⟶ X) (j : Z ⟶ V) (p : X ⟶ V)
    [a.IsOver (Spec (CommRingCat.of k₀))] [q.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    [IsProper a] [IsProper p] [IsOpenImmersion q] [QuasiCompact q]
    [IsOpenImmersion j] [QuasiCompact j] (sq : IsPullback q a p j) :
    Nonempty (derivedLowerStar (k₀ := k₀) (l := l) a ⋙ extensionComplex j ≅
      extensionComplex q ⋙ derivedLowerStar p) := by
  obtain ⟨ep⟩ := properShriekIso (k₀ := k₀) (l := l) p
  obtain ⟨ea⟩ := properShriekIso (k₀ := k₀) (l := l) a
  obtain ⟨bc⟩ := nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l) sq
  let er : derivedLowerStar (k₀ := k₀) (l := l) p ⋙ upperStar j ≅
      upperStar q ⋙ derivedLowerStar a :=
    Functor.isoWhiskerRight ep.symm _ ≪≫ bc ≪≫ Functor.isoWhiskerLeft _ ea
  let M := (Over.mk j.closedComplement).left
  let m : M ⟶ V := j.closedComplement
  let : M.Over (Spec (CommRingCat.of k₀)) := ⟨m ≫ V ↘ Spec (CommRingCat.of k₀)⟩
  have : m.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hjm : IsCompl (Set.range j.base) (Set.range m.base) := by
    change IsCompl (Set.range j.base) (Set.range j.closedComplement.base)
    rw [j.range_closedComplement]
    exact isCompl_compl
  have hzero (K : WeilComplex k₀ l U) :
      IsZero ((upperStar m).obj ((derivedLowerStar p).obj
        ((extensionComplex q).obj K))) := by
    have : LocallyOfFiniteType (M ↘ Spec (CommRingCat.of k₀)) :=
      locallyOfFiniteType_over_of_isOver m (S := Spec (CommRingCat.of k₀))
    have : QuasiCompact (M ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over m (Spec (CommRingCat.of k₀))]; infer_instance
    have : QuasiSeparated (M ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over m (Spec (CommRingCat.of k₀))]; infer_instance
    let : (pullback p m).Over (Spec (CommRingCat.of k₀)) :=
      ⟨pullback.snd p m ≫ M ↘ Spec (CommRingCat.of k₀)⟩
    have : (pullback.snd p m).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have : (pullback.fst p m).IsOver (Spec (CommRingCat.of k₀)) := by
      constructor
      change pullback.fst p m ≫ (X ↘ Spec (CommRingCat.of k₀)) = _
      rw [← comp_over p (Spec (CommRingCat.of k₀)), ← Category.assoc,
        pullback.condition, Category.assoc, comp_over m]
      rfl
    have hdis : Disjoint (Set.range q.base) (Set.range (pullback.fst p m).base) := by
      apply Set.disjoint_left.2
      rintro x ⟨t, ht⟩ ⟨b, hb⟩
      have h : j.base (a.base t) = m.base ((pullback.snd p m).base b) := by
        calc
          j.base (a.base t) = p.base (q.base t) := by
            simpa only [Scheme.Hom.comp_apply] using
              congrArg (fun v : U ⟶ V ↦ v.base t) sq.w.symm
          _ = p.base ((pullback.fst p m).base b) := by rw [ht, hb]
          _ = _ := by
            simpa only [Scheme.Hom.comp_apply] using
              congrArg (fun v : pullback p m ⟶ V ↦ v.base b)
                (show pullback.fst p m ≫ p = pullback.snd p m ≫ m from pullback.condition)
      exact Set.disjoint_left.1 hjm.disjoint ⟨_, rfl⟩ ⟨_, h.symm⟩
    obtain ⟨b⟩ := nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l)
      (IsPullback.of_hasPullback p m)
    exact ((derivedLowerShriek k₀ l (pullback.snd p m)).map_isZero
      (extensionComplex_isZero_of_disjoint q (pullback.fst p m) hdis K)).of_iso
      ((upperStar m).mapIso (ep.app _).symm ≪≫ b.app _)
  exact nonempty_functorIso_of_open_support j m hjm _ _
    (fun K ↦ extensionComplex_isZero_of_disjoint j m hjm.disjoint
      ((derivedLowerStar a).obj K)) hzero
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (extensionRestrictionIso j) ≪≫ Functor.rightUnitor _ ≪≫
      (Functor.isoWhiskerLeft _ er ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (extensionRestrictionIso q) _ ≪≫ Functor.leftUnitor _).symm)

/-- A cartesian proper refinement transports extension by zero. This is the proper/open
exchange with the identity as the proper map on the common open subscheme. -/
private theorem extension_refinement_iso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (f : U ⟶ X)
    [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f]
    (c d : Compactification f) (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 U) r.hom d.i) :
    have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
    have : QuasiCompact d.i := d.quasiCompact_openImmersion ‹_›
    have : r.hom.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
      change r.hom ≫ (d.g ≫ X ↘ Spec (CommRingCat.of k₀)) = _
      rw [← Category.assoc, r.hom_g]
      rfl⟩
    have : LocallyOfFiniteType (d.Z ↘ Spec (CommRingCat.of k₀)) := by
      change LocallyOfFiniteType (d.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
    have : QuasiCompact (d.Z ↘ Spec (CommRingCat.of k₀)) := by
      change QuasiCompact (d.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
    Nonempty (extensionComplex (k₀ := k₀) (l := l) c.i ⋙ derivedLowerStar r.hom ≅
      extensionComplex d.i) := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  have : QuasiCompact d.i := d.quasiCompact_openImmersion ‹_›
  have : r.hom.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change r.hom ≫ (d.g ≫ X ↘ Spec (CommRingCat.of k₀)) = _
    rw [← Category.assoc, r.hom_g]
    rfl⟩
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    change LocallyOfFiniteType (c.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiCompact (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiCompact (c.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiSeparated (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiSeparated (c.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : LocallyOfFiniteType (d.Z ↘ Spec (CommRingCat.of k₀)) := by
    change LocallyOfFiniteType (d.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiCompact (d.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiCompact (d.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiSeparated (d.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiSeparated (d.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) :=
    locallyOfFiniteType_over_of_isOver c.i (S := Spec (CommRingCat.of k₀))
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c.i (Spec (CommRingCat.of k₀))]; infer_instance
  have : QuasiSeparated (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c.i (Spec (CommRingCat.of k₀))]; infer_instance
  obtain ⟨e⟩ := proper_open_exchange (k₀ := k₀) (l := l) (𝟙 U) c.i d.i r.hom hr
  exact ⟨e.symm ≪≫ Functor.isoWhiskerRight lowerStarIdComplexIso _ ≪≫
    Functor.leftUnitor _⟩

private noncomputable def lowerStarCongrComplexIso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {f g : U ⟶ X}
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact g] [QuasiSeparated g] [LocallyOfFiniteType g] (h : f = g) :
    derivedLowerStar (k₀ := k₀) (l := l) f ≅ derivedLowerStar g := by
  subst h
  exact Iso.refl _

private theorem shriekC_refinement_iso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (f : U ⟶ X)
    [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f]
    (c d : Compactification f) (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 U) r.hom d.i) :
    Nonempty (shriekC (k₀ := k₀) (l := l) f c ≅ shriekC f d) := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  have : QuasiCompact d.i := d.quasiCompact_openImmersion ‹_›
  have : r.hom.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change r.hom ≫ (d.g ≫ X ↘ Spec (CommRingCat.of k₀)) = _
    rw [← Category.assoc, r.hom_g]
    rfl⟩
  have : LocallyOfFiniteType (d.Z ↘ Spec (CommRingCat.of k₀)) := by
    change LocallyOfFiniteType (d.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiCompact (d.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiCompact (d.g ≫ X ↘ Spec (CommRingCat.of k₀)); infer_instance
  obtain ⟨e⟩ := extension_refinement_iso (k₀ := k₀) (l := l) f c d r hr
  let k : derivedLowerStar (k₀ := k₀) (l := l) r.hom ⋙ derivedLowerStar d.g ≅
      derivedLowerStar c.g :=
    lowerStarCompComplexIso r.hom d.g ≪≫ lowerStarCongrComplexIso r.hom_g
  unfold shriekC
  exact ⟨Functor.isoWhiskerLeft _ k.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e _⟩

/-- Compare two compactifications through the cartesian common refinement `c.inf d`. -/
private theorem shriekC_independent
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (f : U ⟶ X)
    [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f] (c d : Compactification f) :
    Nonempty (shriekC (k₀ := k₀) (l := l) f c ≅ shriekC f d) := by
  obtain ⟨ec⟩ := shriekC_refinement_iso (k₀ := k₀) (l := l) f (c.inf d) c
    (c.infFst d) (c.isPullback_infFst d)
  obtain ⟨ed⟩ := shriekC_refinement_iso (k₀ := k₀) (l := l) f (c.inf d) d
    (c.infSnd d) (c.isPullback_infSnd d)
  exact ⟨ec.symm ≪≫ ed⟩

/-- Relate the functor built with Nagata's chosen compactification to any compactification. -/
private theorem shriekIsoArbitraryCompactification
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (f : U ⟶ X)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f) :
    Nonempty (derivedLowerShriek k₀ l f ≅ shriekC f c) := by
  let d := HasCompactification.compactification f
    (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : QuasiCompact d.i := d.quasiCompact_openImmersion ‹_›
  let e : derivedLowerShriek k₀ l f ≅ shriekC f d := by
    unfold shriekC extensionComplex
    exact ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
      (Iso.refl _)
  obtain ⟨ec⟩ := shriekC_independent (k₀ := k₀) (l := l) f d c
  exact ⟨e ≪≫ ec⟩

/-- Compare with the compactification consisting of the open immersion and the identity.
The common-refinement comparison uses only the proper cases of compact-support base change. -/
private theorem shriekOpenIsoExtension
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l j ≅ extensionComplex j) := by
  obtain ⟨e⟩ := shriekIsoArbitraryCompactification (k₀ := k₀) (l := l) j
    (Compactification.ofIsOpenImmersion j)
  change derivedLowerShriek k₀ l j ≅ extensionComplex j ⋙ derivedLowerStar (𝟙 X) at e
  exact ⟨e ≪≫ Functor.isoWhiskerLeft _ lowerStarIdComplexIso ≪≫ Functor.rightUnitor _⟩

private theorem restriction_lowerShriek_open
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l U) :
    Nonempty ((upperStar j).obj ((derivedLowerShriek k₀ l j).obj K) ≅ K) := by
  obtain ⟨e⟩ := shriekOpenIsoExtension (k₀ := k₀) (l := l) j
  exact ⟨((Functor.isoWhiskerRight e _ ≪≫ extensionRestrictionIso j).app K)⟩

private theorem restriction_lowerShriek_closed
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (K : WeilComplex k₀ l U) :
    IsZero ((upperStar i).obj ((derivedLowerShriek k₀ l j).obj K)) := by
  obtain ⟨e⟩ := shriekOpenIsoExtension (k₀ := k₀) (l := l) j
  exact (extensionComplex_isZero_of_disjoint j i hij.disjoint K).of_iso
    ((upperStar i).mapIso (e.app K))

/-- The adjunction of actual extension by zero, obtained independently of compact support. -/
private noncomputable def extensionUpperStarAdjunction
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    extensionComplex (k₀ := k₀) (l := l) j ⊣ upperStar j := by
  let Z := (Over.mk j.closedComplement).left
  let i : Z ⟶ X := j.closedComplement
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hij : IsCompl (Set.range j.base) (Set.range i.base) := by
    change IsCompl (Set.range j.base) (Set.range j.closedComplement.base)
    rw [j.range_closedComplement]
    exact isCompl_compl
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) :=
    locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  exact openSupportLeftAdjunction (upperStarDerivedLowerStarAdjunction j)
    (upperStarDerivedLowerStarAdjunction i)
    (derivedLowerStar_essImage_of_isZero i j hij.symm) _
    (extensionComplex_isZero_of_disjoint j i hij.disjoint) (extensionRestrictionIso j)

/-- Exact extension by zero composes by uniqueness of left adjoints to the composite pullback.
This comparison is independent of compact-support base change. -/
private theorem extension_comp_iso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (i : U ⟶ X) (j : X ⟶ Z)
    [i.IsOver (Spec (CommRingCat.of k₀))] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion i] [QuasiCompact i] [IsOpenImmersion j] [QuasiCompact j]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (extensionComplex (k₀ := k₀) (l := l) i ⋙ extensionComplex j ≅
      extensionComplex (i ≫ j)) := by
  exact ⟨(((extensionUpperStarAdjunction i).comp (extensionUpperStarAdjunction j)).ofNatIsoRight
    (upperStarCompComplexIso i j).symm).leftAdjointUniq
      (extensionUpperStarAdjunction (i ≫ j))⟩

private noncomputable def extensionCongrIso {i j : U ⟶ X}
    [i.IsOver (Spec (CommRingCat.of k₀))] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion i] [IsOpenImmersion j] [QuasiCompact i] [QuasiCompact j] (h : i = j) :
    extensionComplex (k₀ := k₀) (l := l) i ≅ extensionComplex j := by
  subst h
  exact Iso.refl _

/-- **The direct image with compact support along an open immersion is the extension by zero**
(blueprint: `prop-functor-package`, clause 2, compactification comparisons for
`Rf_! = Rf̄_* j_!` are independent of the refinement, applied to the compactification
`U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`; and `def-weil-extension-by-zero`). For a
quasi-compact open immersion `j` and a Weil sheaf `G` on `U`, `Rj₀!G ≅ j₀!G` in degree zero.

Compare the chosen compactification with `U ⟶[j] X ⟶[𝟙] X` through their common refinement.
The proper/open exchange identifies the two extension-by-zero functors on that refinement,
and the proper direct images compose. Thus Rj! is exact extension by zero; its value on a
sheaf in degree zero is the degree-zero extension of that sheaf. -/
theorem nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l U) :
    Nonempty ((derivedLowerShriek k₀ l j).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.extensionByZero j).obj G)) := by
  obtain ⟨e⟩ := shriekOpenIsoExtension (k₀ := k₀) (l := l) j
  refine ⟨e.app (WeilSheaf.toComplex.obj G) ≪≫ ?_⟩
  unfold extensionComplex
  exact ObjectProperty.isoMk _
    (((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategorySingleFunctor 0).app G.obj)

/-- **The open–closed triangle** (blueprint: `prop-sf-open-closed-triangle-all-stages`): for a
quasi-compact open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X` and a Weil complex `K`
on `X`, the open counit and the closed unit extend to a distinguished triangle of Weil complexes
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ j₀!j₀^*K[1]`.

This is a weakening of the blueprint node: the vertices of the triangle are only identified up
to some isomorphism, and the first two arrows are not asserted to be the canonical counit and
unit. The proof takes a fibre triangle of the actual closed unit and identifies its first
vertex by open-support comparison and the compactification description of Rj!. -/
theorem exists_distTriang_openClosed (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ T ∈ distTriang (WeilComplex k₀ l X),
      Nonempty (T.obj₁ ≅ (derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)) ∧
      Nonempty (T.obj₂ ≅ K) ∧
      Nonempty (T.obj₃ ≅ (derivedLowerStar i).obj ((upperStar i).obj K)) := by
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) :=
    locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) :=
    locallyOfFiniteType_over_of_isOver i (S := Spec (CommRingCat.of k₀))
  let adj := upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) i
  obtain ⟨W, a, w, hT⟩ := distinguished_cocone_triangle₁ (adj.unit.app K)
  have hW : IsZero ((upperStar i).obj W) :=
    (Triangle.isZero₁_iff_isIso₂ _ ((upperStar i).map_distinguished _ hT)).2
      (Recollement.isIso_map_unit_app (upperStar i) adj K)
  have ha : IsIso ((upperStar j).map a) :=
    (Triangle.isZero₃_iff_isIso₁ _ ((upperStar j).map_distinguished _ hT)).1
      (isZero_upperStar_obj_derivedLowerStar_obj i j hij.symm ((upperStar i).obj K))
  obtain ⟨e⟩ := restriction_lowerShriek_open j ((upperStar j).obj K)
  obtain ⟨eW⟩ := nonempty_iso_of_open_support j i hij W
    ((derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)) hW
    (restriction_lowerShriek_closed j i hij ((upperStar j).obj K))
    (asIso ((upperStar j).map a) ≪≫ e.symm)
  exact ⟨_, hT, ⟨eW⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩


/-- **Composition of direct images with compact support** (blueprint: `prop-functor-package`,
clause 3: `R(gf)_! ≃ Rg_!Rf_!`; this is `lem-zl-shriek-composition` of
`sec-deligne-laumon-general`). For composable separated morphisms of finite type
`X ⟶[f] Y ⟶[g] Z` of `k₀`-schemes, `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`.

Choose a compatible triangle of compactifications. Proper/open exchange moves the middle
proper direct image past extension by zero; composition of the two extensions and of the two
proper direct images gives the functor for the composite compactification. Independence under
common refinement identifies these three functors with the chosen compact-support functors.
The exchange and independence comparisons here use compact-support base change. -/
theorem nonempty_derivedLowerShriek_comp_iso (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l (f ≫ g) ≅
      derivedLowerShriek k₀ l f ⋙ derivedLowerShriek k₀ l g) := by
  let : HasCompactification g := hasCompactification_of_over (k₀ := k₀) g
  let : HasCompactification (f ≫ g) := hasCompactification_of_over (k₀ := k₀) (f ≫ g)
  let T := Compactification.Triangle.ofHasCompactification f g
  have : QuasiCompact T.cf.i := T.cf.quasiCompact_openImmersion ‹_›
  have : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion ‹_›
  have : QuasiCompact T.cfg.i := T.cfg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.q :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) T.isPullback inferInstance
  have : T.p.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change T.p ≫ (T.cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)) =
      T.cfg.g ≫ Z ↘ Spec (CommRingCat.of k₀)
    rw [← Category.assoc, T.p_g]⟩
  have : T.q.IsOver (Spec (CommRingCat.of k₀)) := by
    constructor
    rw [← comp_over T.p (Spec (CommRingCat.of k₀)), ← Category.assoc,
      ← T.isPullback.w, Category.assoc, comp_over T.cg.i, comp_over T.cf.g]
  have : LocallyOfFiniteType (T.cf.Z ↘ Spec (CommRingCat.of k₀)) := by
    change LocallyOfFiniteType (T.cf.g ≫ Y ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiCompact (T.cf.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiCompact (T.cf.g ≫ Y ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiSeparated (T.cf.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiSeparated (T.cf.g ≫ Y ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : LocallyOfFiniteType (T.cg.Z ↘ Spec (CommRingCat.of k₀)) := by
    change LocallyOfFiniteType (T.cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiCompact (T.cg.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiCompact (T.cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiSeparated (T.cg.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiSeparated (T.cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : LocallyOfFiniteType (T.cfg.Z ↘ Spec (CommRingCat.of k₀)) := by
    change LocallyOfFiniteType (T.cfg.g ≫ Z ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiCompact (T.cfg.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiCompact (T.cfg.g ≫ Z ↘ Spec (CommRingCat.of k₀)); infer_instance
  have : QuasiSeparated (T.cfg.Z ↘ Spec (CommRingCat.of k₀)) := by
    change QuasiSeparated (T.cfg.g ≫ Z ↘ Spec (CommRingCat.of k₀)); infer_instance
  obtain ⟨ex⟩ := proper_open_exchange (k₀ := k₀) (l := l)
    T.cf.g T.q T.cg.i T.p T.isPullback.flip
  obtain ⟨ec⟩ := extension_comp_iso (k₀ := k₀) (l := l) T.cf.i T.q
  let ep : derivedLowerStar (k₀ := k₀) (l := l) T.p ⋙ derivedLowerStar T.cg.g ≅
      derivedLowerStar T.cfg.g :=
    lowerStarCompComplexIso T.p T.cg.g ≪≫ lowerStarCongrComplexIso T.p_g
  let ecomp : shriekC (k₀ := k₀) (l := l) f T.cf ⋙ shriekC g T.cg ≅
      shriekC (f ≫ g) T.cfg := by
    unfold shriekC
    exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ex _ ≪≫ Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ec ≪≫ extensionCongrIso T.i_q) _ ≪≫
      Functor.isoWhiskerLeft _ ep
  obtain ⟨ef⟩ := shriekIsoArbitraryCompactification (k₀ := k₀) (l := l) f T.cf
  obtain ⟨eg⟩ := shriekIsoArbitraryCompactification (k₀ := k₀) (l := l) g T.cg
  obtain ⟨efg⟩ := shriekIsoArbitraryCompactification (k₀ := k₀) (l := l) (f ≫ g) T.cfg
  exact ⟨efg ≪≫ ecomp.symm ≪≫
    (Functor.isoWhiskerRight ef _ ≪≫ Functor.isoWhiskerLeft _ eg).symm⟩

/-- **Direct image with compact support of the localization triangle** (blueprint:
`prop-functor-package`, clause 3: for a closed immersion `i` with open complement `j`, applying
`Rf_!` to the localization triangle gives `R(fj)_!j^*K ⟶ Rf_!K ⟶ R(fi)_!i^*K ⟶`). -/
theorem exists_distTriang_derivedLowerShriek_openClosed (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ T ∈ distTriang (WeilComplex k₀ l Y),
      Nonempty (T.obj₁ ≅ (derivedLowerShriek k₀ l (j ≫ f)).obj ((upperStar j).obj K)) ∧
      Nonempty (T.obj₂ ≅ (derivedLowerShriek k₀ l f).obj K) ∧
      Nonempty (T.obj₃ ≅ (derivedLowerShriek k₀ l (i ≫ f)).obj ((upperStar i).obj K)) := by
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiSeparated (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_distTriang_openClosed j i hij K
  obtain ⟨cj⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j f
  obtain ⟨ci⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) i f
  let F := derivedLowerShriek k₀ l f
  refine ⟨F.mapTriangle.obj T, F.map_distinguished T hT, ?_, ?_, ?_⟩
  · exact ⟨F.mapIso e₁ ≪≫ (cj.app ((upperStar j).obj K)).symm⟩
  · exact ⟨F.mapIso e₂⟩
  · exact ⟨F.mapIso e₃ ≪≫
      F.mapIso (derivedLowerShriekObjIsoDerivedLowerStar i ((upperStar i).obj K)).symm ≪≫
      (ci.app ((upperStar i).obj K)).symm⟩


end Package

end WeilComplex

end AlgebraicGeometry
