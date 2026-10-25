/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.LowerShriekIndependence
public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek

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
(`prop-sf-open-closed-triangle-all-stages`), as well as the identification of `Rf₀!` with `Rf₀*`
for proper `f`. All of them are deduced from the comparison `Rb_* ∘ a_! ≅ i_! ∘ Rq_*` of
`WeilConjectures.WeilSheaf.LowerShriekIndependence` (hence from proper base change,
`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper`), the
adjunction `j_! ⊣ j^*` and the base change of the extension by zero.

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


/-- **For a proper morphism, the direct image with compact support is the direct image**, as an
isomorphism of functors on Weil complexes; its components are
`AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar` (blueprint:
`prop-functor-package`, clause 3, "for proper `f`, `Rf_! ≃ Rf_*`"). -/
noncomputable def derivedLowerShriekIsoDerivedLowerStar :
    derivedLowerShriek k₀ l f ≅ derivedLowerStar f := by
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
  let Φ : (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor :=
    Functor.isoWhiskerRight
        (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.symm
        _ ≪≫
      (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
        (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
          (comp_over c.i _))
        (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm ≪≫
      Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
        (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
        (ProEtaleWeilSheaf.lowerStar k₀ l c.g)) ≪≫
      Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g) ≪≫
      Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)
  exact ((objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _ ≪≫
      Functor.isoWhiskerLeft _ Φ ≪≫ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm)

end Proper

section Package

variable {X Y Z U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))]

/-- **The direct image with compact support along an open immersion is the extension by zero**
(blueprint: `prop-functor-package`, clause 2, compactification comparisons for
`Rf_! = Rf̄_* j_!` are independent of the refinement, applied to the compactification
`U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`; and `def-weil-extension-by-zero`). For a
quasi-compact open immersion `j` and a Weil sheaf `G` on `U`, `Rj₀!G ≅ j₀!G` in degree zero. -/
theorem nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l U) :
    Nonempty ((derivedLowerShriek k₀ l j).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.extensionByZero j).obj G)) := by
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_iso_extensionByZero (k₀ := k₀) (l := l) j
  exact ⟨e.app _ ≪≫ ObjectProperty.isoMk _
    (((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategorySingleFunctor 0).app G.obj)⟩

/-- **The open–closed triangle** (blueprint: `prop-sf-open-closed-triangle-all-stages`): for a
quasi-compact open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X` and a Weil complex `K`
on `X`, the open counit and the closed unit extend to a distinguished triangle of Weil complexes
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ j₀!j₀^*K[1]`.

This is a weakening of the blueprint node: the vertices of the triangle are only identified up
to some isomorphism, and the first two arrows are not asserted to be the canonical counit and
unit. -/
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
  have := locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (CommRingCat.of k₀))
  let adj := WeilComplex.extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j
  obtain ⟨Q, v, w, hT⟩ := distinguished_cocone_triangle (adj.counit.app K)
  -- `j^*` inverts the counit, so `j^* Q = 0` and `Q` comes from the closed part
  have hj : IsIso ((WeilComplex.upperStar j).map (adj.counit.app K)) :=
    adj.isIso_map_counit_app_of_isIso_unit K
  have hQ : IsZero ((WeilComplex.upperStar j).obj Q) := (Triangle.isZero₃_iff_isIso₁ _
    ((WeilComplex.upperStar j).map_distinguished _ hT)).2 hj
  obtain ⟨P, ⟨eP⟩⟩ := WeilComplex.derivedLowerStar_essImage_of_isZero i j hij.symm Q hQ
  -- `i^*` kills `j_! j^* K`, so `i^* K ≅ i^* Q`
  have hi₁ : IsZero ((WeilComplex.upperStar i).obj
      ((WeilComplex.extensionByZero j).obj ((WeilComplex.upperStar j).obj K))) :=
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
      (ProEtaleWeilSheaf.isZero_mapDerivedCategory_upperStar_obj_extensionByZero_obj j i
        hij.disjoint _)
  have hi : IsIso ((WeilComplex.upperStar i).map v) := (Triangle.isZero₁_iff_isIso₂ _
    ((WeilComplex.upperStar i).map_distinguished _ hT)).1 hi₁
  have : IsIso (WeilComplex.upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) i).counit :=
    inferInstance
  obtain ⟨e₁⟩ := WeilComplex.nonempty_derivedLowerShriek_iso_extensionByZero (k₀ := k₀) (l := l) j
  have ea : (WeilComplex.upperStar i).obj Q ≅ (WeilComplex.upperStar i).obj K :=
    (asIso ((WeilComplex.upperStar i).map v)).symm
  have eb : (WeilComplex.upperStar i).obj ((WeilComplex.derivedLowerStar i).obj P) ≅
      (WeilComplex.upperStar i).obj Q := (WeilComplex.upperStar i).mapIso eP
  have ec : (WeilComplex.upperStar i).obj ((WeilComplex.derivedLowerStar i).obj P) ≅ P :=
    asIso ((WeilComplex.upperStarDerivedLowerStarAdjunction i).counit.app P)
  have e₃ : Q ≅ (WeilComplex.derivedLowerStar i).obj ((WeilComplex.upperStar i).obj K) :=
    eP.symm ≪≫ (WeilComplex.derivedLowerStar i).mapIso (ec.symm ≪≫ eb ≪≫ ea)
  exact ⟨Triangle.mk (adj.counit.app K) v w, hT, ⟨(e₁.app _).symm⟩, ⟨Iso.refl _⟩, ⟨e₃⟩⟩


/-- **Composition of direct images with compact support** (blueprint: `prop-functor-package`,
clause 3: `R(gf)_! ≃ Rg_!Rf_!`; this is `lem-zl-shriek-composition` of
`sec-deligne-laumon-general`). For composable separated morphisms of finite type
`X ⟶[f] Y ⟶[g] Z` of `k₀`-schemes, `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`. -/
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
  have := hasCompactification_of_over (k₀ := k₀) f
  have := hasCompactification_of_over (k₀ := k₀) g
  let cf := HasCompactification.compactification f
  let cg := HasCompactification.compactification g
  have : QuasiCompact cf.i := cf.quasiCompact_openImmersion inferInstance
  have : QuasiCompact cg.i := cg.quasiCompact_openImmersion inferInstance
  have : LocallyOfFiniteType (cg.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (cg.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : QuasiSeparated (cg.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have := hasCompactification_of_over (k₀ := k₀) (cf.g ≫ cg.i)
  let ch := HasCompactification.compactification (cf.g ≫ cg.i)
  have : QuasiCompact ch.i := ch.quasiCompact_openImmersion inferInstance
  have hfg : f ≫ g = (cf.i ≫ ch.i) ≫ ch.g ≫ cg.g := by
    conv_lhs => rw [cf.comm, cg.comm]
    simp only [Category.assoc]
    rw [reassoc_of% ch.comm]
  obtain ⟨e₁⟩ := nonempty_derivedLowerShriek_comp_ι_iso (k₀ := k₀) (l := l) (f := f ≫ g)
    (cf.i ≫ ch.i) (ch.g ≫ cg.g) hfg
  obtain ⟨e₂⟩ := nonempty_derivedLowerShriek_comp_ι_iso (k₀ := k₀) (l := l) (f := f)
    cf.i cf.g cf.comm
  obtain ⟨e₃⟩ := nonempty_derivedLowerShriek_comp_ι_iso (k₀ := k₀) (l := l) (f := g)
    cg.i cg.g cg.comm
  let key := ProEtaleWeilSheaf.rightDerivedLowerStarExtensionByZeroIso k₀ l ch.i ch.g cf.g cg.i
    ch.comm.symm
  let E := WeilComplex.extensionByZero (k₀ := k₀) (l := l) cf.i
  let ι := (WeilComplex.objectProperty k₀ l X).ι
  let Φ : derivedLowerShriek k₀ l (f ≫ g) ⋙ (WeilComplex.objectProperty k₀ l Z).ι ≅
      (derivedLowerShriek k₀ l f ⋙ derivedLowerShriek k₀ l g) ⋙
        (WeilComplex.objectProperty k₀ l Z).ι :=
    calc derivedLowerShriek k₀ l (f ≫ g) ⋙ (WeilComplex.objectProperty k₀ l Z).ι
      _ ≅ ι ⋙ (ProEtaleWeilSheaf.extensionByZero k₀ l (cf.i ≫ ch.i)).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l (ch.g ≫ cg.g)).rightDerivedFunctor := e₁
      _ ≅ ι ⋙ ((ProEtaleWeilSheaf.extensionByZero k₀ l cf.i).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.extensionByZero k₀ l ch.i).mapDerivedCategory) ⋙
          ((ProEtaleWeilSheaf.lowerStar k₀ l ch.g).rightDerivedFunctor ⋙
            (ProEtaleWeilSheaf.lowerStar k₀ l cg.g).rightDerivedFunctor) :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
          (ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroCompIso k₀ l cf.i ch.i) _ ≪≫
          Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.rightDerivedLowerStarCompIso k₀ l ch.g cg.g))
      _ ≅ (E ⋙ (WeilComplex.objectProperty k₀ l cf.Z).ι ⋙
            (ProEtaleWeilSheaf.extensionByZero k₀ l ch.i).mapDerivedCategory ⋙
              (ProEtaleWeilSheaf.lowerStar k₀ l ch.g).rightDerivedFunctor) ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l cg.g).rightDerivedFunctor := Iso.refl _
      _ ≅ (E ⋙ (WeilComplex.objectProperty k₀ l cf.Z).ι ⋙
            (ProEtaleWeilSheaf.lowerStar k₀ l cf.g).rightDerivedFunctor ⋙
              (ProEtaleWeilSheaf.extensionByZero k₀ l cg.i).mapDerivedCategory) ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l cg.g).rightDerivedFunctor :=
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ key) _
      _ ≅ (ι ⋙ (ProEtaleWeilSheaf.extensionByZero k₀ l cf.i).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.lowerStar k₀ l cf.g).rightDerivedFunctor) ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l cg.i).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.lowerStar k₀ l cg.g).rightDerivedFunctor := Iso.refl _
      _ ≅ (derivedLowerShriek k₀ l f ⋙ (WeilComplex.objectProperty k₀ l Y).ι) ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l cg.i).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.lowerStar k₀ l cg.g).rightDerivedFunctor :=
        Functor.isoWhiskerRight e₂.symm _
      _ ≅ derivedLowerShriek k₀ l f ⋙ ((WeilComplex.objectProperty k₀ l Y).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l cg.i).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.lowerStar k₀ l cg.g).rightDerivedFunctor) :=
        Functor.associator _ _ _
      _ ≅ derivedLowerShriek k₀ l f ⋙ (derivedLowerShriek k₀ l g ⋙
          (WeilComplex.objectProperty k₀ l Z).ι) := Functor.isoWhiskerLeft _ e₃.symm
      _ ≅ _ := (Functor.associator _ _ _).symm
  exact ⟨((WeilComplex.objectProperty k₀ l Z).fullyFaithfulι.whiskeringRight _).preimageIso Φ⟩

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
  have hX : f ≫ Y ↘ Spec (CommRingCat.of k₀) = X ↘ Spec (CommRingCat.of k₀) :=
    comp_over f _
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by rw [← hX]; infer_instance
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by rw [← hX]; infer_instance
  have : QuasiSeparated (X ↘ Spec (CommRingCat.of k₀)) := by rw [← hX]; infer_instance
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_distTriang_openClosed (k₀ := k₀) j i hij K
  obtain ⟨cj⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j f
  obtain ⟨ci⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) i f
  let F := derivedLowerShriek k₀ l f
  exact ⟨F.mapTriangle.obj T, F.map_distinguished _ hT, ⟨F.mapIso e₁ ≪≫ (cj.app _).symm⟩,
    ⟨F.mapIso e₂⟩, ⟨F.mapIso (e₃ ≪≫ (derivedLowerShriekObjIsoDerivedLowerStar i _).symm) ≪≫
      (ci.app _).symm⟩⟩

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
of `k₀`-schemes, `h^* Rf₀! ≅ Rf'₀! g^*`. -/
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
    Nonempty (derivedLowerShriek k₀ l f ⋙ upperStar h ≅
      upperStar g ⋙ derivedLowerShriek k₀ l f') := by
  have := hasCompactification_of_over (k₀ := k₀) f
  let c := HasCompactification.compactification f
  let c' := c.ofIsPullback hH
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : QuasiCompact c'.i := c'.quasiCompact_openImmersion inferInstance
  let p : c'.Z ⟶ c.Z := pullback.fst c.g h
  have : p.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change pullback.fst c.g h ≫ c.g ≫ Y ↘ Spec (CommRingCat.of k₀) =
      pullback.snd c.g h ≫ Y' ↘ Spec (CommRingCat.of k₀)
    rw [pullback.condition_assoc, comp_over h]⟩
  have hsq : IsPullback g c'.i c.i p := c.isPullback_i_ofIsPullback hH
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper
    (k₀ := k₀) (l := l) (f := c.g) (g := h) (f' := c'.g) (g' := p) inferInstance
    (c.isPullback_g_ofIsPullback hH).flip
  obtain ⟨e₁⟩ := nonempty_derivedLowerShriek_comp_ι_iso (k₀ := k₀) (l := l) (f := f)
    c.i c.g c.comm
  obtain ⟨e₂⟩ := nonempty_derivedLowerShriek_comp_ι_iso (k₀ := k₀) (l := l) (f := f')
    c'.i c'.g c'.comm
  let E := WeilComplex.extensionByZero (k₀ := k₀) (l := l) c.i
  let ι := (WeilComplex.objectProperty k₀ l X).ι
  let Φ : (derivedLowerShriek k₀ l f ⋙ upperStar h) ⋙ (WeilComplex.objectProperty k₀ l Y').ι ≅
      (upperStar g ⋙ derivedLowerShriek k₀ l f') ⋙ (WeilComplex.objectProperty k₀ l Y').ι :=
    calc (derivedLowerShriek k₀ l f ⋙ upperStar h) ⋙ (WeilComplex.objectProperty k₀ l Y').ι
      _ ≅ (derivedLowerShriek k₀ l f ⋙ (WeilComplex.objectProperty k₀ l Y).ι) ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l h).mapDerivedCategory := Iso.refl _
      _ ≅ (ι ⋙ (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor) ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l h).mapDerivedCategory :=
        Functor.isoWhiskerRight e₁ _
      _ ≅ E ⋙ (derivedLowerStar c.g ⋙ upperStar h) ⋙ (WeilComplex.objectProperty k₀ l Y').ι :=
        Iso.refl _
      _ ≅ E ⋙ (upperStar p ⋙ derivedLowerStar c'.g) ⋙ (WeilComplex.objectProperty k₀ l Y').ι :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight e _)
      _ ≅ ι ⋙ ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory) ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l c'.g).rightDerivedFunctor := Iso.refl _
      _ ≅ ι ⋙ ((ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.extensionByZero k₀ l c'.i).mapDerivedCategory) ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l c'.g).rightDerivedFunctor :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
          (ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroUpperStarIso k₀ l g c'.i c.i p hsq) _)
      _ ≅ upperStar g ⋙ ((WeilComplex.objectProperty k₀ l X').ι ⋙
            (ProEtaleWeilSheaf.extensionByZero k₀ l c'.i).mapDerivedCategory ⋙
              (ProEtaleWeilSheaf.lowerStar k₀ l c'.g).rightDerivedFunctor) := Iso.refl _
      _ ≅ upperStar g ⋙ (derivedLowerShriek k₀ l f' ⋙ (WeilComplex.objectProperty k₀ l Y').ι) :=
        Functor.isoWhiskerLeft _ e₂.symm
      _ ≅ _ := (Functor.associator _ _ _).symm
  exact ⟨((WeilComplex.objectProperty k₀ l Y').fullyFaithfulι.whiskeringRight _).preimageIso Φ⟩

end Package

end WeilComplex

end AlgebraicGeometry
