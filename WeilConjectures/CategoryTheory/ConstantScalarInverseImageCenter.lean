/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleScalarCenter

/-! # Constant scalar multiplication under exact algebraic inverse image -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory.ConstantModuleScalar

private def constantScalar
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] [HasSheafify J (Type r)]
    [J.HasSheafCompose (forget CommRingCat.{r})]
    (B : CommRingCat.{r}) (b : B) :
    (constantSheaf J (Type r)).obj PUnit.{r + 1} ⟶
      (sheafCompose J (forget CommRingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj B) :=
  (constantSheaf J (Type r)).map (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b)) ≫
    (constantCommuteCompose J (forget CommRingCat.{r})).inv.app B

private theorem constantScalar_apply
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] [HasSheafify J (Type r)]
    [J.HasSheafCompose (forget CommRingCat.{r})]
    (B : CommRingCat.{r}) (b : B) (U : Cᵒᵖ)
    (t : ((constantSheaf J (Type r)).obj PUnit.{r + 1}).obj.obj U) :
    (constantScalar J B b).hom.app U t =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b := by
  let P := (Functor.const Cᵒᵖ).obj PUnit.{r + 1}
  let : IsIso (toSheafify J P) :=
    isIso_toSheafify J (Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)
  obtain ⟨x, hx⟩ := ((isIso_iff_bijective _).mp
    (inferInstance : IsIso ((toSheafify J P).app U))).2 t
  subst t
  have hn := congrArg (fun f ↦ f.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
      (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b))))
  change _ = ((constantSheaf J (Type r)).map
    (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b))).hom.app U
      ((toSheafify J P).app U x) at hn
  change ((constantCommuteCompose J (forget CommRingCat.{r})).inv.app
    B).hom.app U _ = _
  have hn' : ((constantSheaf J (Type r)).map
      (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b))).hom.app U
        ((toSheafify J P).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (B : Type r))).app U b := hn.symm
  apply Eq.trans (congrArg
    (fun z ↦ ((constantCommuteCompose J (forget CommRingCat.{r})).inv.app
      B).hom.app U z) hn')
  have hf := congrArg (fun f ↦ f.app U b)
    (sheafComposeIso_hom_fac J (forget CommRingCat.{r})
      ((Functor.const Cᵒᵖ).obj B))
  have hconst := toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ (forget CommRingCat.{r})).hom.app B)
  have hp := congrArg (fun f ↦ f.app U b) hconst
  dsimp at hp
  change ((sheafifyComposeIso J (forget CommRingCat.{r})
    ((Functor.const Cᵒᵖ).obj B)).hom.app U)
      ((((presheafToSheaf J (Type r)).map
        ((Functor.compConstIso Cᵒᵖ (forget CommRingCat.{r})).hom.app
          B)).hom.app U)
            ((toSheafify J ((Functor.const Cᵒᵖ).obj (B : Type r))).app U b)) = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget CommRingCat.{r})
    ((Functor.const Cᵒᵖ).obj B)).hom.app U) z) hp.symm).trans hf

private def toConstantUnit
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] [HasSheafify J (Type r)]
    [J.HasSheafCompose (forget CommRingCat.{r})]
    (T : Sheaf J (Type r)) : T ⟶ (constantSheaf J (Type r)).obj PUnit.{r + 1} where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun _ ↦
      (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{r + 1})).app U PUnit.unit)
      naturality := by
        intro U V f
        ext t
        exact congrArg (fun g ↦ g PUnit.unit)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{r + 1})).naturality f) }

/-- Exact algebraic inverse image preserves the localized action of each constant scalar.
Source: Stacks 00YV, 03D7 and 07A6, finite-coefficient transport Step 1
(blueprint: lem-pur-constant-scalar-inverse-image-center).
Proof: regard the constant scalar b as a map from the terminal constant singleton
sheaf to the coefficient sheaf. The normalization h identifies its inverse image
with the same scalar on the target. For a module M, apply moduleSMul to the identity
section of its underlying sheaf and this constant scalar. The moduleUnderlying
isomorphism identifies the resulting endomorphism with multiplication by b on the
inverse-image module. Its naturality then proves equality of module morphisms.
Apply this equality degreewise to every cochain complex. The factorization of the
exact derived functor and localization_app give the displayed equality on QK.
Naturality and essential surjectivity of Q extend it to every derived object.
Zero coefficients and the empty site cause no exception to these equalities. -/
theorem inverseImage_center
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J CommRingCat.{r}] [HasWeakSheafify K CommRingCat.{r}]
    [HasSheafify J (Type r)] [HasSheafify K (Type r)]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.HasSheafCompose (forget CommRingCat.{r})]
    [K.HasSheafCompose (forget CommRingCat.{r})]
    [J.HasSheafCompose (forget AddCommGrpCat.{r})]
    [K.HasSheafCompose (forget AddCommGrpCat.{r})]
    (B : CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (modules (constantRing J B))]
    [HasDerivedCategory.{w} (modules (constantRing K B))]
    (F : Sheaf J (Type r) ⥤ Sheaf K (Type r)) [PreservesFiniteLimits F]
    (L : SheafOfModules.AlgebraicInverseImage F (constantRing J B) (constantRing K B))
    [L.modules.Additive] [PreservesFiniteLimits L.modules]
    [PreservesFiniteColimits L.modules]
    (point : F.obj ((constantSheaf J (Type r)).obj PUnit.{r + 1}) ≅
      (constantSheaf K (Type r)).obj PUnit.{r + 1})
    (h : ∀ b : B,
      F.map ((constantSheaf J (Type r)).map
        (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b)) ≫
          (constantCommuteCompose J (forget CommRingCat.{r})).inv.app B) ≫
          L.ringUnderlying.hom =
        point.hom ≫ (constantSheaf K (Type r)).map
          (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b)) ≫
          (constantCommuteCompose K (forget CommRingCat.{r})).inv.app B)
    (b : B) (M : DerivedCategory (modules (constantRing J B))) :
    L.modules.mapDerivedCategory.map ((derived J B b).app M) =
      (derived K B b).app (L.modules.mapDerivedCategory.obj M) := by
  have ho (N : modules (constantRing J B)) :
      L.modules.map ((ordinary J B b).app N) =
        (ordinary K B b).app (L.modules.obj N) := by
    let T := (underlying (constantRing J B)).obj N
    let q := toConstantUnit J T
    let s := q ≫ constantScalar J B b
    have hs (V : Cᵒᵖ) (x : T.obj.obj V) :
        s.hom.app V x = (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V b :=
      constantScalar_apply J B b V _
    have ht := L.moduleSMul N T s (𝟙 T)
      ((underlying (constantRing J B)).map ((ordinary J B b).app N)) (by
        intro V x
        change @SMul.smul ((constantRing J B).obj.obj V) (N.val.obj V) _
            ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V b) x =
          @SMul.smul ((constantRing J B).obj.obj V) (N.val.obj V) _
            (s.hom.app V x) x
        rw [hs])
    have hh : F.map s ≫ L.ringUnderlying.hom =
        F.map q ≫ point.hom ≫ constantScalar K B b := by
      dsimp only [s, constantScalar]
      rw [Functor.map_comp, Category.assoc, h b]
    have heq : F.map ((underlying (constantRing J B)).map
          ((ordinary J B b).app N)) ≫ L.moduleUnderlying.inv.app N =
        L.moduleUnderlying.inv.app N ≫
          (underlying (constantRing K B)).map
            ((ordinary K B b).app (L.modules.obj N)) := by
      ext V x
      change @id ((L.modules.obj N).val.obj V)
          ((L.moduleUnderlying.inv.app N).hom.app V
            ((F.map ((underlying (constantRing J B)).map
              ((ordinary J B b).app N))).hom.app V x)) =
        ((toSheafify K ((Functor.const Dᵒᵖ).obj B)).app V b) •
          @id ((L.modules.obj N).val.obj V)
            ((L.moduleUnderlying.inv.app N).hom.app V x)
      have hb : L.ringUnderlying.hom.hom.app V ((F.map s).hom.app V x) =
          (toSheafify K ((Functor.const Dᵒᵖ).obj B)).app V b := by
        calc
          _ = (F.map q ≫ point.hom ≫ constantScalar K B b).hom.app V x :=
            congrArg (fun f ↦ f.hom.app V x) hh
          _ = (constantScalar K B b).hom.app V
              ((F.map q ≫ point.hom).hom.app V x) := rfl
          _ = _ := constantScalar_apply K B b V _
      have hi : (F.map (𝟙 T)).hom.app V x = x := by
        rw [Functor.map_id]
        rfl
      have hv := ht V x
      rw [hb, hi] at hv
      exact hv
    apply (underlying (constantRing K B)).map_injective
    apply (cancel_epi (L.moduleUnderlying.inv.app N)).1
    exact (L.moduleUnderlying.inv.naturality ((ordinary J B b).app N)).symm.trans heq
  have hc (N : CochainComplex (modules (constantRing J B)) ℤ) :
      (L.modules.mapHomologicalComplex (.up ℤ)).map ((cochain J B b).app N) =
        (cochain K B b).app ((L.modules.mapHomologicalComplex (.up ℤ)).obj N) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ho (N.X n)
  have he : Functor.whiskerRight (derived J B b) L.modules.mapDerivedCategory =
      Functor.whiskerLeft L.modules.mapDerivedCategory (derived K B b) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro N
    change L.modules.mapDerivedCategory.map ((derived J B b).app
      (DerivedCategory.Q.obj N)) =
        (derived K B b).app (L.modules.mapDerivedCategory.obj (DerivedCategory.Q.obj N))
    apply (cancel_mono (L.modules.mapDerivedCategoryFactors.hom.app N)).1
    rw [← (derived K B b).naturality]
    simp only [derived, Functor.comp_obj, CatCenter.localization_app]
    rw [L.modules.mapDerivedCategoryFactors_hom_naturality, hc]
  exact congrArg (fun t ↦ t.app M) he


end CategoryTheory.ConstantModuleScalar
