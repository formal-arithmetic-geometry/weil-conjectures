/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.SecSmoothPurity.CochainCoefficientArrows
import all Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations

/-! # Scalar comparison and the double transpose

Source: Weil blueprint, sec-smooth-purity/sk-lem-sp-tower,
cor-coef-finite-verdier.proof.md, evaluation and double-dual compatibility
(blueprint: lem-coef-finite-bidual-transpose).

The scalar tensor comparison is normalized by the existing ordinary scalar
comparison on K-flat representatives. All derived categories are ordinary
unbounded module derived categories, with independent localization universes.

## Main definitions and statement

* `scalarCounit`: refer the existing derived counit to ordinary scalar extension.
* `TensorComparisonModel`: normalize the existing comparison on K-flat complexes.
* `finite_bidual_transpose`: the two transpose identities and signed symmetry.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r wA wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  WeilConjectures

namespace CategoryTheory.FiniteBidualTranspose

universe a

set_option linter.defProp false in
@[instance_reducible]
private def cachedCompose {C : Type c} [Category.{v} C]
    [EssentiallySmall.{a} C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{a} RingCat.{a}) :=
  (equivSmallModel.{a} C).hasSheafCompose J
    ((equivSmallModel.{a} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{a} RingCat.{a})

attribute [local instance 1000001] cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 4000] HomologicalComplex.monoidalCategory

attribute [local irreducible] derivedInternalHomOfUniverses
  CoefficientTensorModels.iso CochainComplex.IsKFlatIndependentCoefficients
  DerivedCategory DerivedCategory.Q DerivedCategory.Qh


private theorem tensor_right_map {D : Type*} [Category* D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {X Y : D} (f : X ⟶ Y) (P : D) :
    S.tensor.map (Prod.mkHom f (𝟙 P)) =
      (@MonoidalCategory.tensorRight D _ S.monoidal P).map f := by
  exact @MonoidalCategory.tensorHom_id D _ S.monoidal X Y f P

private theorem tensor_left_map {D : Type*} [Category* D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {X Y : D} (f : X ⟶ Y) (P : D) :
    S.tensor.map (Prod.mkHom (𝟙 P) f) =
      (@MonoidalCategory.tensorLeft D _ S.monoidal P).map f := by
  exact @MonoidalCategory.id_tensorHom D _ S.monoidal P X Y f

private theorem untranspose {D : Type*} [Category* D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (X P Q : D) (f : X ⟶ H.obj (op P, Q)) :
    (S.transpose X P Q).symm f = S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ S.evaluation P Q := by
  rw [tensor_right_map]
  exact (S.adjunction P).homEquiv_counit X Q f

private theorem tensor_comp {D : Type*} [Category* D] (T : D × D ⥤ D)
    {X Y Z X' Y' Z' : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z') :
    T.map (Prod.mkHom (f ≫ g) (f' ≫ g')) =
      T.map (Prod.mkHom f f') ≫ T.map (Prod.mkHom g g') :=
  T.map_comp (Prod.mkHom f f') (Prod.mkHom g g')

private theorem map_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ W)
    (h : X ⟶ Z) (k : Z ⟶ W) (e : f ≫ g = h ≫ k) :
    F.map f ≫ F.map g = F.map h ≫ F.map k := by
  rw [← F.map_comp, ← F.map_comp, e]

private theorem symmetry_diagram {D : Type*} [Category* D]
    {X₀ X₁ A₀ A₁ B₀ B₁ Z₀ Z₁ T₀ T₁ C₀ C₁ : D}
    (p : X₀ ⟶ A₀) (q : X₁ ⟶ A₁) (a : A₀ ⟶ A₁) (s : X₀ ⟶ X₁)
    (t₀ : A₀ ⟶ B₀) (t₁ : A₁ ⟶ B₁) (k₀ : B₀ ⟶ C₀) (k₁ : B₁ ⟶ C₁)
    (d₀ : X₀ ⟶ Z₀) (d₁ : X₁ ⟶ Z₁) (e₀ : Z₀ ⟶ T₀) (e₁ : Z₁ ⟶ T₁)
    (m₀ : T₀ ⟶ C₀) (m₁ : T₁ ⟶ C₁) (g : Z₀ ⟶ Z₁)
    (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁) (v : T₀ ⟶ T₁)
    (hA : p ≫ a = s ≫ q)
    (h₀ : p ≫ t₀ ≫ k₀ = d₀ ≫ e₀ ≫ m₀)
    (h₁ : q ≫ t₁ ≫ k₁ = d₁ ≫ e₁ ≫ m₁)
    (hN : s ≫ d₁ = d₀ ≫ g) (hC : g ≫ e₁ = e₀ ≫ v)
    (hB : m₀ ≫ c = v ≫ m₁) (hb : k₀ ≫ c = b ≫ k₁)
    (hp : Epi p) (hk : Mono k₁) :
    a ≫ t₁ = t₀ ≫ b := by
  apply (cancel_epi p).mp
  apply (cancel_mono k₁).mp
  calc
    _ = (p ≫ a) ≫ t₁ ≫ k₁ := by simp only [Category.assoc]
    _ = s ≫ q ≫ t₁ ≫ k₁ := by rw [hA, Category.assoc]
    _ = s ≫ (d₁ ≫ e₁ ≫ m₁) := by rw [h₁]
    _ = (s ≫ d₁) ≫ e₁ ≫ m₁ := by simp only [Category.assoc]
    _ = d₀ ≫ g ≫ e₁ ≫ m₁ := by rw [hN, Category.assoc]
    _ = d₀ ≫ (g ≫ e₁) ≫ m₁ := by simp only [Category.assoc]
    _ = d₀ ≫ e₀ ≫ v ≫ m₁ := by rw [hC, Category.assoc]
    _ = d₀ ≫ e₀ ≫ m₀ ≫ c := by rw [← hB]
    _ = (p ≫ t₀ ≫ k₀) ≫ c := by rw [h₀]; simp only [Category.assoc]
    _ = _ := by simp only [Category.assoc]; rw [hb]

private theorem transport_square {D : Type*} [Category* D]
    {A B C E A' B' C' E' : D}
    (i : A ⟶ A') (j : B ⟶ B') (k : C ⟶ C') (l : E ⟶ E')
    (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ C) (d : C ⟶ E)
    (a' : A' ⟶ B') (b' : B' ⟶ E') (c' : A' ⟶ C') (d' : C' ⟶ E')
    [Epi i] (ha : i ≫ a' = a ≫ j) (hb : j ≫ b' = b ≫ l)
    (hc : i ≫ c' = c ≫ k) (hd : k ≫ d' = d ≫ l)
    (h : a ≫ b = c ≫ d) : a' ≫ b' = c' ≫ d' := by
  apply (cancel_epi i).mp
  calc
    _ = (i ≫ a') ≫ b' := (Category.assoc _ _ _).symm
    _ = a ≫ b ≫ l := by rw [ha, Category.assoc, hb]
    _ = (c ≫ d) ≫ l := by rw [← Category.assoc, h]
    _ = _ := by rw [Category.assoc, ← hd, ← Category.assoc, ← hc, Category.assoc]

private theorem symmetry_of_representatives {C D : Type*} [Category* C] [Category* D]
    {HA : Cᵒᵖ × C ⥤ C} {HB : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (sA : @SymmetricCategory C _ SA.monoidal)
    (sB : @SymmetricCategory D _ SB.monoidal)
    (F : C ⥤ D) (t : SA.tensor ⋙ F ≅ (F.prod F) ⋙ SB.tensor)
    {I : Type*} (R : I → C) (hR : ∀ U, ∃ i, Nonempty (R i ≅ U))
    (hs : ∀ i j, F.map (sA.braiding (R i) (R j)).hom ≫ t.hom.app (R j, R i) =
      t.hom.app (R i, R j) ≫ (sB.braiding (F.obj (R i)) (F.obj (R j))).hom) :
    ∀ U V, F.map (sA.braiding U V).hom ≫ t.hom.app (V, U) =
      t.hom.app (U, V) ≫ (sB.braiding (F.obj U) (F.obj V)).hom := by
  intro U V
  obtain ⟨p, ⟨i⟩⟩ := hR U
  obtain ⟨q, ⟨j⟩⟩ := hR V
  have hA := @BraidedCategory.braiding_naturality C _ SA.monoidal sA.toBraidedCategory
    _ _ _ _ i.hom j.hom
  change SA.tensor.map (Prod.mkHom i.hom j.hom) ≫ (sA.braiding U V).hom =
    (sA.braiding (R p) (R q)).hom ≫ SA.tensor.map (Prod.mkHom j.hom i.hom) at hA
  have hB := @BraidedCategory.braiding_naturality D _ SB.monoidal sB.toBraidedCategory
    _ _ _ _ (F.map i.hom) (F.map j.hom)
  change SB.tensor.map (Prod.mkHom (F.map i.hom) (F.map j.hom)) ≫
    (sB.braiding (F.obj U) (F.obj V)).hom =
    (sB.braiding (F.obj (R p)) (F.obj (R q))).hom ≫
      SB.tensor.map (Prod.mkHom (F.map j.hom) (F.map i.hom)) at hB
  have hT := t.hom.naturality (Prod.mkHom i.hom j.hom)
  have hT' := t.hom.naturality (Prod.mkHom j.hom i.hom)
  change F.map (SA.tensor.map (Prod.mkHom i.hom j.hom)) ≫ t.hom.app (U, V) =
    t.hom.app (R p, R q) ≫ SB.tensor.map (Prod.mkHom (F.map i.hom) (F.map j.hom)) at hT
  change F.map (SA.tensor.map (Prod.mkHom j.hom i.hom)) ≫ t.hom.app (V, U) =
    t.hom.app (R q, R p) ≫ SB.tensor.map (Prod.mkHom (F.map j.hom) (F.map i.hom)) at hT'
  have : IsIso (F.map (SA.tensor.map (Prod.mkHom i.hom j.hom))) := by
    change IsIso (F.map (SA.tensor.mapIso (Iso.prod i j)).hom)
    infer_instance
  have hAF := F.congr_map hA
  simp only [Functor.map_comp] at hAF
  exact transport_square _ _ _ _ _ _ _ _ _ _ _ _ hAF hT' hT hB (hs p q)

private theorem transpose_core {C D : Type*} [Category* C] [Category* D]
    {HA : Cᵒᵖ × C ⥤ C} {HB : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (sA : @SymmetricCategory C _ SA.monoidal)
    (sB : @SymmetricCategory D _ SB.monoidal)
    (F : C ⥤ D) (t : SA.tensor ⋙ F ≅ (F.prod F) ⋙ SB.tensor)
    (hs : ∀ U V, F.map (sA.braiding U V).hom ≫ t.hom.app (V, U) =
      t.hom.app (U, V) ≫ (sB.braiding (F.obj U) (F.obj V)).hom)
    (OA : C) (OB : D) (u : F.obj OA ⟶ OB) (K : C)
    (hK : F.obj (HA.obj (op K, OA)) ⟶ HB.obj (op (F.obj K), OB))
    (hDK : F.obj (HA.obj (op (HA.obj (op K, OA)), OA)) ⟶
      HB.obj (op (F.obj (HA.obj (op K, OA))), OB))
    (hevK : SB.tensor.map (Prod.mkHom hK (𝟙 (F.obj K))) ≫ SB.evaluation (F.obj K) OB =
      t.inv.app (HA.obj (op K, OA), K) ≫ F.map (SA.evaluation K OA) ≫ u)
    (hevDK : SB.tensor.map (Prod.mkHom hDK (𝟙 (F.obj (HA.obj (op K, OA))))) ≫
      SB.evaluation (F.obj (HA.obj (op K, OA))) OB =
      t.inv.app (HA.obj (op (HA.obj (op K, OA)), OA), HA.obj (op K, OA)) ≫
        F.map (SA.evaluation (HA.obj (op K, OA)) OA) ≫ u) :
    F.map (SA.transpose K (HA.obj (op K, OA)) OA
      ((sA.braiding K (HA.obj (op K, OA))).hom ≫ SA.evaluation K OA)) ≫ hDK =
    SB.transpose (F.obj K) (HB.obj (op (F.obj K), OB)) OB
      ((sB.braiding (F.obj K) (HB.obj (op (F.obj K), OB))).hom ≫
        SB.evaluation (F.obj K) OB) ≫ HB.map (Prod.mkHom hK.op (𝟙 OB)) := by
  dsimp only [CoefficientClosedStructure.tensor] at *
  let V := HA.obj (op K, OA)
  let X := F.obj K
  let Y := F.obj V
  let W := HB.obj (op X, OB)
  let dA := SA.transpose K V OA ((sA.braiding K V).hom ≫ SA.evaluation K OA)
  let dB := SB.transpose X W OB ((sB.braiding X W).hom ≫ SB.evaluation X OB)
  change F.map dA ≫ hDK = dB ≫ HB.map (Prod.mkHom hK.op (𝟙 OB))
  have hdA : (@MonoidalCategory.tensor C _ SA.monoidal).map (Prod.mkHom (dA) (𝟙 V)) ≫
      SA.evaluation V OA =
      (sA.braiding K V).hom ≫ SA.evaluation K OA := by
    erw [← untranspose]
    exact (SA.transpose K V OA).symm_apply_apply _
  have hdB : (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (dB) (𝟙 W)) ≫
      SB.evaluation W OB =
      (sB.braiding X W).hom ≫ SB.evaluation X OB := by
    erw [← untranspose]
    exact (SB.transpose X W OB).symm_apply_apply _
  have hevK' : (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom hK (𝟙 X)) ≫
      SB.evaluation X OB =
      t.inv.app (V, K) ≫ F.map (SA.evaluation K OA) ≫ u := hevK
  have hevDK' : (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom hDK (𝟙 Y)) ≫
      SB.evaluation Y OB =
      t.inv.app (HA.obj (op V, OA), V) ≫ F.map (SA.evaluation V OA) ≫ u := hevDK
  apply (SB.transpose X Y OB).symm.injective
  simp only [untranspose]
  dsimp only [CoefficientClosedStructure.tensor]
  have hn := t.inv.naturality (Prod.mkHom dA (𝟙 V))
  change (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (F.map dA) (F.map (𝟙 V))) ≫
      t.inv.app (HA.obj (op V, OA), V) =
    t.inv.app (K, V) ≫ F.map ((@MonoidalCategory.tensor C _ SA.monoidal).map
        (Prod.mkHom (dA) (𝟙 V))) at hn
  rw [F.map_id] at hn
  have he := SB.evaluation_naturality W Y OB hK
  rw [← tensor_right_map SB, ← tensor_left_map SB] at he
  change (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (HB.map
      (Prod.mkHom hK.op (𝟙 OB))) (𝟙 Y)) ≫
      SB.evaluation Y OB =
    (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (𝟙 (HB.obj (op W, OB))) hK) ≫
        SB.evaluation W OB at he
  have hb : (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (𝟙 X) (hK)) ≫
      (sB.braiding X W).hom =
      (sB.braiding X Y).hom ≫ (@MonoidalCategory.tensor D _ SB.monoidal).map
          (Prod.mkHom (hK) (𝟙 X)) := by
    exact @BraidedCategory.braiding_naturality _ _ SB.monoidal
      sB.toBraidedCategory X Y X W (𝟙 X) hK
  have htau : (sB.braiding X Y).hom ≫ t.inv.app (V, K) =
      t.inv.app (K, V) ≫ F.map (sA.braiding K V).hom := by
    apply (cancel_epi (t.hom.app (K, V))).mp
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [← hs K V]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  calc
    _ = (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (F.map dA) (𝟙 Y)) ≫
        (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (hDK) (𝟙 Y)) ≫
            SB.evaluation Y OB := by
      rw [← Category.assoc, ← tensor_comp, Category.id_comp]
    _ = t.inv.app (K, V) ≫ F.map ((sA.braiding K V).hom ≫
        SA.evaluation K OA) ≫ u := by
      rw [hevDK', ← Category.assoc, hn]
      simp only [Category.assoc]
      rw [← F.map_comp_assoc, hdA]
    _ = (sB.braiding X Y).hom ≫ (@MonoidalCategory.tensor D _ SB.monoidal).map
        (Prod.mkHom (hK) (𝟙 X)) ≫
        SB.evaluation X OB := by
      erw [hevK']
      simpa only [Category.assoc, F.map_comp] using
        congrArg (fun f => f ≫ F.map (SA.evaluation K OA) ≫ u) htau.symm
    _ = (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (𝟙 X) (hK)) ≫
        (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (dB) (𝟙 W)) ≫
        SB.evaluation W OB := by
      erw [hdB]
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ SB.evaluation X OB) hb.symm
    _ = (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (dB) (𝟙 Y)) ≫
        (@MonoidalCategory.tensor D _ SB.monoidal).map (Prod.mkHom (HB.map
            (Prod.mkHom hK.op (𝟙 OB))) (𝟙 Y)) ≫
        SB.evaluation Y OB := by
      rw [he, ← Category.assoc, ← Category.assoc, ← tensor_comp, ← tensor_comp]
      simp only [Category.id_comp]
      congr 2
      apply Prod.ext
      · exact (Category.comp_id _).symm
      · exact Category.comp_id _
    _ = _ := by rw [← Category.assoc, ← tensor_comp, Category.id_comp]

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {A B : Sheaf J CommRingCat.{max c v r}} (φ : A ⟶ B)
  [HasDerivedCategory.{wA} (RingedTensorModules.{c, v, r} J A)]
  [HasDerivedCategory.{wB} (RingedTensorModules.{c, v, r} J B)]

omit [HasDerivedCategory.{wA} (RingedTensorModules.{c, v, r} J A)] in
private theorem pure_ext (P Q N : RingedTensorModules.{c, v, r} J A)
    {f g : P ⊗ Q ⟶ N}
    (h : ∀ U x y,
      f.val.app U ((SheafOfModules.tensorObjIsoSheafification P Q).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 _)).unit.app
          (P.val ⊗ Q.val)).app U (x ⊗ₜ[A.obj.obj U] y))) =
      g.val.app U ((SheafOfModules.tensorObjIsoSheafification P Q).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 _)).unit.app
          (P.val ⊗ Q.val)).app U (x ⊗ₜ[A.obj.obj U] y)))) : f = g := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification P Q).inv).mp
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).obj)
  apply (adj.homEquiv (P.val ⊗ Q.val) N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private def nativeModelIso
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wA} J A))
    (T : CoefficientTensorModels.{r, c, v, wA} J A S)
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients) :
    DerivedCategory.Q.obj (P ⊗ Q) ≅
      S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  T.iso J A S P Q hP hQ

private def nativeSwap
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ) :
    P ⊗ Q ≅ Q ⊗ P :=
  CochainComplex.Monoidal.braiding P Q

private theorem modeled_symmetry
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wA} J A))
    (T : CoefficientTensorModels.{r, c, v, wA} J A S)
    (s : @SymmetricCategory _ _ S.monoidal)
    (coherence : RingedDerivedTensorCoherence.{c, v, r, wA} J A S T s)
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients) :
    (nativeModelIso.{c, v, r, wA} J S T P Q hP hQ).hom ≫
        (s.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (nativeSwap.{c, v, r} J P Q).hom ≫
      (nativeModelIso.{c, v, r, wA} J S T Q P hQ hP).hom := by
  obtain ⟨σ, hσ, he⟩ := coherence.symmetry_model P Q hP hQ
  have hs : σ.hom = (nativeSwap.{c, v, r} J P Q).hom := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := P) (K₂ := Q) (F := curriedTensor (RingedTensorModules.{c, v, r} J A))
      (c := .up ℤ)
    intro p q hpq
    apply pure_ext.{c, v, r} J
    intro U x y
    exact (hσ p q n hpq ((add_comm q p).trans hpq) U x y).trans
      ((RingedDerivedNative.complexConstraints.{c, v, r} J A).symmetry
        P Q p q n hpq ((add_comm q p).trans hpq) U x y).symm
  rw [hs] at he
  exact he

private theorem mapped_symmetry
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wA} J A))
    (T : CoefficientTensorModels.{r, c, v, wA} J A S)
    (s : @SymmetricCategory _ _ S.monoidal)
    (coherence : RingedDerivedTensorCoherence.{c, v, r, wA} J A S T s)
    {D : Type*} [Category* D] (F : DerivedCategory (RingedTensorModules.{c, v, r} J A) ⥤ D)
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients) :
    F.map (nativeModelIso.{c, v, r, wA} J S T P Q hP hQ).hom ≫
      F.map (s.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
    F.map (DerivedCategory.Q.map (nativeSwap.{c, v, r} J P Q).hom) ≫
      F.map (nativeModelIso.{c, v, r, wA} J S T Q P hQ hP).hom := by
  have h := modeled_symmetry.{c, v, r, wA} J S T s coherence P Q hP hQ
  simpa only [Functor.map_comp] using F.congr_map h

private theorem kflat_representative
    (X : DerivedCategory (RingedTensorModules.{c, v, r} J A)) :
    ∃ (P : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ),
      P.IsKFlatIndependentCoefficients ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  let G := DerivedCategory.Q.objPreimage X
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A) G
  have : QuasiIso f := hf
  have : IsIso (DerivedCategory.Q.{wA}.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hf
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

attribute [-instance] cachedCompose

/-- The given scalar model's counit, referred to the prescribed ordinary extension.
The equality only identifies two presentations of the same functor on objects and maps.
Source: Stacks 06YY; blueprint cor-coef-finite-verdier, evaluation paragraph
(blueprint: lem-coef-finite-bidual-transpose). -/
def scalarCounit
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, wA, wB} φ)
    (hE : M.E.mapHomologicalComplex (.up ℤ) = CochainPullback.extend φ)
    (P : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ) :
    M.T.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((CochainPullback.extend φ).obj P) :=
  M.ε.app P ≫ DerivedCategory.Q.map
    (eqToHom (congrArg (fun E ↦ E.obj P) hE))

set_option maxHeartbeats 800000 in
-- Elaborate both K-flat representative identifications.
/-- The canonical scalar tensor comparison, characterized on K-flat representatives.
This is a normalization of the comparison already supplied by derived tensor pullback,
using the actual ordinary comparison `CochainPullback.epsilon`, not an arbitrary map.
Source: Stacks 07A4, 06YY; blueprint cor-coef-finite-verdier, evaluation paragraph
(blueprint: lem-coef-finite-bidual-transpose). -/
def TensorComparisonModel
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, wA, wB} φ)
    (hE : M.E.mapHomologicalComplex (.up ℤ) = CochainPullback.extend φ)
    (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wA} J A))
    (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wB} J B))
    (TA : CoefficientTensorModels.{r, c, v, wA} J A SA)
    (TB : CoefficientTensorModels.{r, c, v, wB} J B SB)
    (t : SA.tensor ⋙ M.T ≅ (M.T.prod M.T) ⋙ SB.tensor) : Prop :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
    ∃ (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := B)
        ((CochainPullback.extend φ).obj P))
      (hQ' : CochainComplex.IsKFlatIndependentCoefficients (R := B)
        ((CochainPullback.extend φ).obj Q)),
      M.T.map (TA.iso J A SA P Q hP hQ).hom ≫
          t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          SB.tensor.map (Prod.mkHom
            (scalarCounit.{c, v, r, wA, wB} J φ M hE P)
            (scalarCounit.{c, v, r, wA, wB} J φ M hE Q)) =
        scalarCounit.{c, v, r, wA, wB} J φ M hE
            ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) ≫
          DerivedCategory.Q.map (CochainPullback.epsilon φ P Q).hom ≫
          (TB.iso J B SB ((CochainPullback.extend φ).obj P)
            ((CochainPullback.extend φ).obj Q) hP' hQ').hom

attribute [local instance 1000001] cachedCompose

private theorem scalarCounit_naturality
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, wA, wB} φ)
    (hE : M.E.mapHomologicalComplex (.up ℤ) = CochainPullback.extend φ)
    {P Q : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ} (f : P ⟶ Q) :
    M.T.map (DerivedCategory.Q.map f) ≫ scalarCounit.{c, v, r, wA, wB} J φ M hE Q =
      scalarCounit.{c, v, r, wA, wB} J φ M hE P ≫
        DerivedCategory.Q.map ((CochainPullback.extend φ).map f) := by
  have h := (eqToHom hE).naturality f
  simp only [eqToHom_app] at h
  unfold scalarCounit
  have hε := M.ε.naturality f
  change M.T.map (DerivedCategory.Q.map f) ≫ M.ε.app Q =
    M.ε.app P ≫ DerivedCategory.Q.map ((M.E.mapHomologicalComplex (.up ℤ)).map f) at hε
  rw [← Category.assoc, hε]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [h]

private theorem nativeNormalization
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, wA, wB} φ)
    (hE : M.E.mapHomologicalComplex (.up ℤ) = CochainPullback.extend φ)
    (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wA} J A))
    (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wB} J B))
    (TA : CoefficientTensorModels.{r, c, v, wA} J A SA)
    (TB : CoefficientTensorModels.{r, c, v, wB} J B SB)
    (t : SA.tensor ⋙ M.T ≅ (M.T.prod M.T) ⋙ SB.tensor)
    (ht : TensorComparisonModel.{c, v, r, wA, wB} J φ M hE SA SB TA TB t)
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients) :
    ∃ (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := B)
        ((CochainPullback.extend φ).obj P))
      (hQ' : CochainComplex.IsKFlatIndependentCoefficients (R := B)
        ((CochainPullback.extend φ).obj Q)),
      M.T.map (nativeModelIso.{c, v, r, wA} J SA TA P Q hP hQ).hom ≫
        t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SB.tensor.map (Prod.mkHom (scalarCounit.{c, v, r, wA, wB} J φ M hE P)
          (scalarCounit.{c, v, r, wA, wB} J φ M hE Q)) =
      scalarCounit.{c, v, r, wA, wB} J φ M hE (P ⊗ Q) ≫
        DerivedCategory.Q.map (CochainPullback.epsilon φ P Q).hom ≫
        (nativeModelIso.{c, v, r, wB} J SB TB ((CochainPullback.extend φ).obj P)
          ((CochainPullback.extend φ).obj Q) hP' hQ').hom := by
  exact ht P Q hP hQ

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric
attribute [local instance 3000] CochainComplex.Monoidal.braidedCategory
attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] CoefficientClosedStructure.transpose
  CoefficientClosedStructure.evaluation
attribute [local irreducible] scalarCounit coefficientTotalTensor nativeModelIso nativeSwap
  CochainPullback.epsilon CochainPullback.extensionPullback
  CochainPullback.extensionComparison CochainPullback.extensionFunctor
  HomologicalComplex₂.total

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_symmetry_models
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, wA, wB} φ)
    (hE : M.E.mapHomologicalComplex (.up ℤ) = CochainPullback.extend φ)
    (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wA} J A))
    (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wB} J B))
    (TA : CoefficientTensorModels.{r, c, v, wA} J A SA)
    (TB : CoefficientTensorModels.{r, c, v, wB} J B SB)
    (sA : @SymmetricCategory _ _ SA.monoidal)
    (sB : @SymmetricCategory _ _ SB.monoidal)
    (coherenceA : RingedDerivedTensorCoherence.{c, v, r, wA} J A SA TA sA)
    (coherenceB : RingedDerivedTensorCoherence.{c, v, r, wB} J B SB TB sB)
    (t : SA.tensor ⋙ M.T ≅ (M.T.prod M.T) ⋙ SB.tensor)
    (ht : TensorComparisonModel.{c, v, r, wA, wB} J φ M hE SA SB TA TB t)
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients) :
    M.T.map (sA.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
      t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (sB.braiding (M.T.obj (DerivedCategory.Q.obj P))
          (M.T.obj (DerivedCategory.Q.obj Q))).hom := by
  dsimp only [CoefficientClosedStructure.tensor] at *
  obtain ⟨hP', hQ', hpq⟩ :=
    nativeNormalization.{c, v, r, wA, wB} J φ M hE SA SB TA TB t ht P Q hP hQ
  obtain ⟨_, _, hqp⟩ :=
    nativeNormalization.{c, v, r, wA, wB} J φ M hE SA SB TA TB t ht Q P hQ hP
  dsimp only [CoefficientClosedStructure.tensor] at hpq hqp
  have : IsIso (M.ε.app P) := M.computes P hP
  have : IsIso (M.ε.app Q) := M.computes Q hQ
  have : IsIso (scalarCounit.{c, v, r, wA, wB} J φ M hE P) := by
    unfold scalarCounit
    infer_instance
  have : IsIso (scalarCounit.{c, v, r, wA, wB} J φ M hE Q) := by
    unfold scalarCounit
    infer_instance
  have hb := @BraidedCategory.braiding_naturality _ _ SB.monoidal sB.toBraidedCategory
    _ _ _ _ (scalarCounit.{c, v, r, wA, wB} J φ M hE P) (scalarCounit.{c, v, r, wA, wB} J φ M hE Q)
  have hA := mapped_symmetry J SA TA sA coherenceA M.T P Q hP hQ
  have hB := modeled_symmetry.{c, v, r, wB} J SB TB sB coherenceB
    ((CochainPullback.extend φ).obj P) ((CochainPullback.extend φ).obj Q) hP' hQ'
  have hN := scalarCounit_naturality.{c, v, r, wA, wB} J φ M hE
    (nativeSwap.{c, v, r} J P Q).hom
  let k₁ := (@MonoidalCategory.tensor
    (DerivedCategory (RingedTensorModules.{c, v, r} J B)) _ SB.monoidal).map
      (Prod.mkHom (scalarCounit.{c, v, r, wA, wB} J φ M hE Q)
        (scalarCounit.{c, v, r, wA, wB} J φ M hE P))
  have hk : IsIso k₁ := by
    change IsIso (SB.tensor.mapIso (Iso.prod
      (asIso (scalarCounit.{c, v, r, wA, wB} J φ M hE Q))
      (asIso (scalarCounit.{c, v, r, wA, wB} J φ M hE P)))).hom
    infer_instance
  have hsource : IsIso (nativeModelIso.{c, v, r, wA}
      J SA TA P Q hP hQ).hom := (nativeModelIso.{c, v, r, wA}
      J SA TA P Q hP hQ).isIso_hom
  have hi : IsIso (M.T.map (nativeModelIso.{c, v, r, wA}
      J SA TA P Q hP hQ).hom) := Functor.map_isIso M.T _
  have hepi : Epi (M.T.map (nativeModelIso.{c, v, r, wA}
      J SA TA P Q hP hQ).hom) := @IsIso.epi_of_iso _ _ _ _ _ hi
  have hmono : Mono k₁ := @IsIso.mono_of_iso _ _ _ _ k₁ hk
  have hd := symmetry_diagram _ _ _ _ _ _ _ k₁ _ _ _ _ _ _ _ _ _ _
    hA hpq hqp hN (by
      have hc := CochainPullback.comparison_braiding.{max c v r, c, v, c, v}
        (CochainPullback.extensionPullback.{max c v r, c, v} φ)
        (CochainPullback.extensionComparison.{max c v r, c, v} φ) P Q
      simpa only [nativeSwap, CochainPullback.epsilon, CochainPullback.extend,
        CochainComplex.Monoidal.braidedCategory, Functor.map_comp] using
        DerivedCategory.Q.{wB}.congr_map hc) hB hb hepi hmono
  exact hd

attribute [-instance] cachedCompose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 800000 in
-- Elaborate the two transposes in independently sized derived categories.
/-- Evaluation-preserving scalar comparison respects the double transpose, and,
when both comparison maps are invertible, identifies the two specified bidual maps.
The last clause is preservation of the signed symmetry; `coherence.symmetry_model`
identifies each braiding with the factor `(-1)^(i*j)` on homogeneous tensors.
Source: Weil blueprint, sec-smooth-purity/sk-lem-sp-tower,
cor-coef-finite-verdier.proof.md, transposing evaluation
(blueprint: lem-coef-finite-bidual-transpose).

Proof plan:
1. Use lem-sf-ringed-derived-closed-symmetric-monoidal for the two natural
   tensor-Hom bijections and their inverse formula, evaluation after tensoring.
   lem-pur-derived-change-of-rings identifies M.T with scalar extension.
   K-flat representatives, the native Koszul symmetry and the scalar cochain
   comparison equation give symmetry compatibility of the normalized tensor
   comparison, without assuming flatness of the ring map.
2. Put V = H_A(K, OmegaA), X = M.T(K), Y = M.T(V). Untranspose the two
   candidate maps X -> H_B(Y, OmegaB). The bijection is injective.
3. For M.T(deltaA) followed by hDK, naturality of t, the evaluation hypothesis
   at V, and the definition of deltaA give u after M.T(evA_K after symmetry),
   preceded by the inverse tensor comparison at (K,V).
4. For deltaB followed by H_B(hK,1), naturality of evaluation in its first
   argument and the definition of deltaB give evaluation at X after symmetry
   and hK tensor 1. Naturality of symmetry and the evaluation hypothesis at K
   turn this into u after M.T(evA_K), with inverse comparison and symmetry.
5. Symmetry compatibility from step 1 identifies steps 3 and 4. Injectivity
   proves the double-transpose equality. The representative symmetries are
   multiplication by (-1)^(i*j), preserved by additive scalar extension,
   including characteristic two and odd shifts.
6. If hK and hDK are isomorphisms, the contravariant Hom functor takes the
   inverse of hK to the inverse of H_B(hK,1). Postcompose the equality by
   that inverse and cancel. No bidual map is assumed invertible.
-/
theorem finite_bidual_transpose
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, wA, wB} φ)
    (hE : M.E.mapHomologicalComplex (.up ℤ) = CochainPullback.extend φ)
    (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wA} J A))
    (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wB} J B))
    (TA : CoefficientTensorModels.{r, c, v, wA} J A SA)
    (TB : CoefficientTensorModels.{r, c, v, wB} J B SB)
    (sA : @SymmetricCategory _ _ SA.monoidal)
    (sB : @SymmetricCategory _ _ SB.monoidal)
    (coherenceA : RingedDerivedTensorCoherence.{c, v, r, wA} J A SA TA sA)
    (coherenceB : RingedDerivedTensorCoherence.{c, v, r, wB} J B SB TB sB)
    (t : SA.tensor ⋙ M.T ≅ (M.T.prod M.T) ⋙ SB.tensor)
    (ht : TensorComparisonModel.{c, v, r, wA, wB} J φ M hE SA SB TA TB t)
    (ΩA : DerivedCategory (RingedTensorModules.{c, v, r} J A))
    (ΩB : DerivedCategory (RingedTensorModules.{c, v, r} J B))
    (u : M.T.obj ΩA ⟶ ΩB)
    (K : DerivedCategory (RingedTensorModules.{c, v, r} J A))
    (hK : M.T.obj ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, wB} J B).obj (op (M.T.obj K), ΩB))
    (hDK : M.T.obj ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj
        (op ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)), ΩA)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, wB} J B).obj
        (op (M.T.obj ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA))), ΩB))
    (hevK : SB.tensor.map (Prod.mkHom hK (𝟙 (M.T.obj K))) ≫
        SB.evaluation (M.T.obj K) ΩB =
      t.inv.app ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA), K) ≫
        M.T.map (SA.evaluation K ΩA) ≫ u)
    (hevDK : SB.tensor.map (Prod.mkHom hDK
          (𝟙 (M.T.obj ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA))))) ≫
        SB.evaluation
          (M.T.obj ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA))) ΩB =
      t.inv.app ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj
          (op ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)), ΩA),
        (derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)) ≫
        M.T.map (SA.evaluation
          ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)) ΩA) ≫ u) :
    (M.T.map ((SA.transpose K
        ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)) ΩA
        ((sA.braiding K
          ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA))).hom ≫
          SA.evaluation K ΩA))) ≫ hDK =
      (SB.transpose (M.T.obj K)
        ((derivedInternalHomOfUniverses.{c, v, r, wB} J B).obj (op (M.T.obj K), ΩB)) ΩB
        ((sB.braiding (M.T.obj K)
          ((derivedInternalHomOfUniverses.{c, v, r, wB} J B).obj (op (M.T.obj K), ΩB))).hom ≫
          SB.evaluation (M.T.obj K) ΩB)) ≫
        (derivedInternalHomOfUniverses.{c, v, r, wB} J B).map (Prod.mkHom hK.op (𝟙 ΩB))) ∧
    (∀ (eK : M.T.obj ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)) ≅
        (derivedInternalHomOfUniverses.{c, v, r, wB} J B).obj (op (M.T.obj K), ΩB))
      (eDK : M.T.obj ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj
          (op ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)), ΩA)) ≅
        (derivedInternalHomOfUniverses.{c, v, r, wB} J B).obj
          (op (M.T.obj ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA))), ΩB)),
      eK.hom = hK → eDK.hom = hDK →
        M.T.map ((SA.transpose K
        ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA)) ΩA
        ((sA.braiding K
          ((derivedInternalHomOfUniverses.{c, v, r, wA} J A).obj (op K, ΩA))).hom ≫
          SA.evaluation K ΩA))) ≫ eDK.hom ≫
          (derivedInternalHomOfUniverses.{c, v, r, wB} J B).map
            (Prod.mkHom eK.inv.op (𝟙 ΩB)) = (SB.transpose (M.T.obj K)
        ((derivedInternalHomOfUniverses.{c, v, r, wB} J B).obj (op (M.T.obj K), ΩB)) ΩB
        ((sB.braiding (M.T.obj K)
          ((derivedInternalHomOfUniverses.{c, v, r, wB} J B).obj (op (M.T.obj K), ΩB))).hom ≫
          SB.evaluation (M.T.obj K) ΩB))) ∧
    (∀ X Y : DerivedCategory (RingedTensorModules.{c, v, r} J A),
      M.T.map (sA.braiding X Y).hom ≫ t.hom.app (Y, X) =
        t.hom.app (X, Y) ≫ (sB.braiding (M.T.obj X) (M.T.obj Y)).hom) := by
  dsimp only [CoefficientClosedStructure.tensor] at *
  let HA := derivedInternalHomOfUniverses.{c, v, r, wA} J A
  let HB := derivedInternalHomOfUniverses.{c, v, r, wB} J B
  let V := HA.obj (op K, ΩA)
  let X := M.T.obj K
  let Y := M.T.obj V
  let W := HB.obj (op X, ΩB)
  let dA := SA.transpose K V ΩA ((sA.braiding K V).hom ≫ SA.evaluation K ΩA)
  let dB := SB.transpose X W ΩB ((sB.braiding X W).hom ≫ SB.evaluation X ΩB)
  let I := {P : CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ //
    P.IsKFlatIndependentCoefficients}
  have hr : ∀ U, ∃ p : I, Nonempty (DerivedCategory.Q.obj p.val ≅ U) := by
    intro U
    obtain ⟨P, hP, e⟩ := kflat_representative.{c, v, r, wA} J U
    exact ⟨⟨P, hP⟩, e⟩
  have hs := symmetry_of_representatives SA SB sA sB M.T t
    (fun p : I => DerivedCategory.Q.obj p.val) hr (fun p q =>
      scalar_symmetry_models.{c, v, r, wA, wB} J φ M hE SA SB TA TB sA sB
        coherenceA coherenceB t ht p.val q.val p.property q.property)
  have hmain : M.T.map dA ≫ hDK = dB ≫ HB.map (Prod.mkHom hK.op (𝟙 ΩB)) :=
    transpose_core SA SB sA sB M.T t hs ΩA ΩB u K hK hDK hevK hevDK
  refine ⟨hmain, ?_, hs⟩
  intro eK eDK heK heDK
  change M.T.map dA ≫ eDK.hom ≫ HB.map (Prod.mkHom (eK.inv.op) (𝟙 ΩB)) = dB
  erw [heDK, ← Category.assoc, hmain, Category.assoc, ← HB.map_comp]
  have hi : Prod.mkHom hK.op (𝟙 ΩB) ≫ Prod.mkHom eK.inv.op (𝟙 ΩB) = 𝟙 (op W, ΩB) := by
    erw [← heK]
    apply Prod.ext
    · exact congrArg Quiver.Hom.op eK.inv_hom_id
    · exact Category.id_comp _
  erw [hi, HB.map_id, Category.comp_id]

end CategoryTheory.FiniteBidualTranspose
