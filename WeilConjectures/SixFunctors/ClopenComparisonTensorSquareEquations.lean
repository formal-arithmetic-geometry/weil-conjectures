/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareData
import WeilConjectures.SixFunctors.ClopenCartesianTensorSquare

/-!
# Clopen comparison tensor square equations

Source: Stacks Project, `sites-cohomology.tex`, Tags 07A4 and 0GL1; clopen tensor
refinement of Stacks 0F7B, original steps 1--7
(blueprint: lem-sf-clopen-comparison-tensor-square-equations).

The normalized tensor comparison data satisfies all four Cartesian, clopen,
composite-open, and pasted tensor identities on the whole unbounded derived
categories, in both ordinary and sequence-site modes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v h w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.ClopenComparisonTensorSquare

-- The next three formal calculations follow the proved private calculations in
-- WeilConjectures.SixFunctors.ProperOpenProjectionMate, without importing its geometric construction.
private theorem open_tensor_composite_transpose
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (S : D ⥤ C) (B : D ⥤ E) (R : E ⥤ D)
    (a : L ⊣ S) (b : B ⊣ R)
    (U : C × C ⥤ C) (T : D × D ⥤ D) (V : E × E ⥤ E)
    (muS : T ⋙ S ≅ (S.prod S) ⋙ U) (muR : V ⋙ R ≅ (R.prod R) ⋙ T)
    (deltaS : (L.prod (𝟭 D)) ⋙ T ≅ (𝟭 C).prod S ⋙ U ⋙ L)
    (deltaR : (B.prod (𝟭 E)) ⋙ V ≅ (𝟭 D).prod R ⋙ T ⋙ B)
    (hS : ∀ (M : C) (N : D), a.homEquiv _ _ (deltaS.inv.app (M, N)) =
      U.map (Prod.mkHom (a.unit.app M) (𝟙 _)) ≫ muS.inv.app (L.obj M, N))
    (hR : ∀ (M : D) (N : E), b.homEquiv _ _ (deltaR.inv.app (M, N)) =
      T.map (Prod.mkHom (b.unit.app M) (𝟙 _)) ≫ muR.inv.app (B.obj M, N))
    (M : C) (N : E) :
    (a.comp b).homEquiv _ _
        (B.map (deltaS.inv.app (M, R.obj N)) ≫ deltaR.inv.app (L.obj M, N)) =
      U.map (Prod.mkHom ((a.comp b).unit.app M) (𝟙 (S.obj (R.obj N)))) ≫
        muS.inv.app (R.obj (B.obj (L.obj M)), R.obj N) ≫
          S.map (muR.inv.app (B.obj (L.obj M), N)) := by
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ _) = _
  rw [b.homEquiv_naturality_left]
  erw [hR]
  rw [a.homEquiv_naturality_right]
  erw [hS]
  rw [Functor.map_comp]
  have hn := muS.inv.naturality (Prod.mkHom (b.unit.app (L.obj M)) (𝟙 (R.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [← hn]
  simp only [Category.assoc]
  rw [← U.map_comp_assoc]
  congr 2
  ext
  · exact (Adjunction.comp_unit_app a b M).symm
  · simp

private theorem tensor_square_clopen_factors
    {A B C D E : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E]
    (Pi : D ⥤ C) (Pp : D ⥤ B) (Pq : C ⥤ E) (Pb : B ⥤ E)
    (S : E ⥤ A) (L : A ⥤ E) (K : E ⥤ B) (J : C ⥤ D)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (muP : TD ⋙ Pp ⟶ (Pp.prod Pp) ⋙ TB)
    (muQ : TC ⋙ Pq ⟶ (Pq.prod Pq) ⋙ TE)
    (muS : TE ⋙ S ⟶ (S.prod S) ⋙ TA)
    (deltaJ : (J.prod (𝟭 D)) ⋙ TD ⟶ (𝟭 C).prod Pi ⋙ TC ⋙ J)
    (deltaK : (K.prod (𝟭 B)) ⋙ TB ⟶ (𝟭 E).prod Pb ⋙ TE ⋙ K)
    (deltaS : (L.prod (𝟭 E)) ⋙ TE ⟶ (𝟭 A).prod S ⋙ TA ⋙ L)
    (beta : J ⋙ Pp ⟶ Pq ⋙ K) (theta : Pp ⋙ Pb ≅ Pi ⋙ Pq)
    (rho : 𝟭 E ⟶ S ⋙ L)
    (hcart : ∀ (H : C) (N : D),
      Pp.map (deltaJ.app (H, N)) ≫ beta.app (TC.obj (H, Pi.obj N)) ≫
        K.map (muQ.app (H, Pi.obj N)) ≫
        K.map (TE.map (Prod.mkHom (𝟙 _) (theta.inv.app N))) =
      muP.app (J.obj H, N) ≫ TB.map (Prod.mkHom (beta.app H) (𝟙 _)) ≫
        deltaK.app (Pq.obj H, Pp.obj N))
    (hclopen : ∀ (F V : E), rho.app (TE.obj (F, V)) ≫ L.map (muS.app (F, V)) =
      TE.map (Prod.mkHom (rho.app F) (𝟙 V)) ≫ deltaS.app (S.obj F, V))
    (H : C) (N : D) :
    Pp.map (deltaJ.app (H, N)) ≫ beta.app (TC.obj (H, Pi.obj N)) ≫
      K.map (rho.app (Pq.obj (TC.obj (H, Pi.obj N)))) ≫
      K.map (L.map (S.map (muQ.app (H, Pi.obj N)))) ≫
      K.map (L.map (muS.app (Pq.obj H, Pq.obj (Pi.obj N)))) ≫
      K.map (L.map (TA.map (Prod.mkHom (𝟙 _) (S.map (theta.inv.app N))))) =
    muP.app (J.obj H, N) ≫
      TB.map (Prod.mkHom (beta.app H ≫ K.map (rho.app (Pq.obj H))) (𝟙 _)) ≫
      deltaK.app (L.obj (S.obj (Pq.obj H)), Pp.obj N) ≫
      K.map (deltaS.app (S.obj (Pq.obj H), Pb.obj (Pp.obj N))) := by
  have hr := rho.naturality (muQ.app (H, Pi.obj N))
  have hs := deltaS.naturality
    (Prod.mkHom (𝟙 (S.obj (Pq.obj H))) (theta.inv.app N))
  have hk := deltaK.naturality (Prod.mkHom (rho.app (Pq.obj H)) (𝟙 (Pp.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.comp_obj,
    Functor.prod_obj, Functor.id_obj] at hr hs hk
  slice_lhs 3 4 => rw [← K.map_comp, ← hr, K.map_comp]
  slice_lhs 4 5 => rw [← K.map_comp, hclopen, K.map_comp]
  have ht : Prod.mkHom (beta.app H ≫ K.map (rho.app (Pq.obj H))) (𝟙 (Pp.obj N)) =
      Prod.mkHom (beta.app H) (𝟙 (Pp.obj N)) ≫
        Prod.mkHom (K.map (rho.app (Pq.obj H))) (𝟙 (Pp.obj N)) := by
    ext <;> simp
  rw [ht, TB.map_comp]
  simp only [Category.assoc]
  slice_rhs 3 4 => exact hk
  slice_lhs 5 6 => rw [← K.map_comp, ← hs, K.map_comp]
  have hp :
      Prod.mkHom (rho.app (Pq.obj H)) (𝟙 (Pq.obj (Pi.obj N))) ≫
        Prod.mkHom (L.map (𝟙 (S.obj (Pq.obj H)))) (theta.inv.app N) =
      Prod.mkHom (𝟙 (Pq.obj H)) (theta.inv.app N) ≫
        Prod.mkHom (rho.app (Pq.obj H)) (Pb.map (𝟙 (Pp.obj N))) := by
    ext <;> simp
  slice_lhs 4 5 => rw [← K.map_comp, ← TE.map_comp, hp, TE.map_comp, K.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hcart H N]

private theorem clopen_tensor_of_normalization
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (S : D ⥤ C) (a : L ⊣ S) (b : S ⊣ L)
    (T : D × D ⥤ D) (U : C × C ⥤ C)
    (mu : T ⋙ S ≅ (S.prod S) ⋙ U)
    (delta : (L.prod (𝟭 D)) ⋙ T ≅ (𝟭 C).prod S ⋙ U ⋙ L)
    (hn : ∀ M : C, a.unit.app M ≫ b.counit.app M = 𝟙 M)
    (hu : ∀ M : C, IsIso (a.unit.app M))
    (hd : ∀ (M : C) (V : D), a.homEquiv _ _ (delta.inv.app (M, V)) =
      U.map (Prod.mkHom (a.unit.app M) (𝟙 (S.obj V))) ≫ mu.inv.app (L.obj M, V))
    (F V : D) :
    b.unit.app (T.obj (F, V)) ≫ L.map (mu.hom.app (F, V)) =
      T.map (Prod.mkHom (b.unit.app F) (𝟙 V)) ≫ delta.hom.app (S.obj F, V) := by
  have ht (M : C) :
      S.map (delta.hom.app (M, V)) ≫ b.counit.app (U.obj (M, S.obj V)) =
        mu.hom.app (L.obj M, V) ≫
          U.map (Prod.mkHom (b.counit.app M) (𝟙 (S.obj V))) := by
    have := hu (U.obj (M, S.obj V))
    apply (cancel_epi (S.map (delta.inv.app (M, V)))).1
    slice_lhs 1 2 =>
      rw [← S.map_comp, Iso.inv_hom_id_app]
      exact S.map_id _
    rw [Category.id_comp]
    apply (cancel_epi (a.unit.app (U.obj (M, S.obj V)))).1
    have he := hd M V
    change a.unit.app (U.obj (M, S.obj V)) ≫ S.map (delta.inv.app (M, V)) = _ at he
    slice_rhs 1 2 => rw [he]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← U.map_comp]
    have hp : Prod.mkHom (a.unit.app M) (𝟙 (S.obj V)) ≫
        Prod.mkHom (b.counit.app M) (𝟙 (S.obj V)) = 𝟙 _ := by
      ext
      · exact hn M
      · simp
    rw [hp, U.map_id]
    exact hn _
  apply ((b.homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change S.map (b.unit.app (T.obj (F, V))) ≫ S.map (L.map (mu.hom.app (F, V))) ≫
      b.counit.app (U.obj (S.obj F, S.obj V)) =
    S.map (T.map (Prod.mkHom (b.unit.app F) (𝟙 V))) ≫
      S.map (delta.hom.app (S.obj F, V)) ≫ b.counit.app (U.obj (S.obj F, S.obj V))
  slice_lhs 2 3 => exact b.counit.naturality (mu.hom.app (F, V))
  slice_lhs 1 2 => exact b.left_triangle_components (T.obj (F, V))
  simp only [CategoryTheory.Functor.id_map]
  rw [ht]
  have hm := mu.hom.naturality (Prod.mkHom (b.unit.app F) (𝟙 V))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hm
  slice_rhs 1 2 => exact hm
  rw [Category.assoc, ← U.map_comp]
  have hp : Prod.mkHom (S.map (b.unit.app F)) (S.map (𝟙 V)) ≫
      Prod.mkHom (b.counit.app (S.obj F)) (𝟙 (S.obj V)) = 𝟙 _ := by
    ext
    · exact b.left_triangle_components F
    · simp
  rw [hp]
  erw [U.map_id, Category.id_comp, Category.comp_id]
  rfl

private theorem ordinaryUnit_isIso {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (M : Mod (restrictRing m j R)) :
    IsIso (o.adjunction.unit.app M) := by
  have h : o.adjunction.unit.app M = (o.sectionIso M).inv := by
    apply (cancel_mono (o.sectionIso M).hom).1
    rw [o.sectionUnit, Iso.inv_hom_id]
    rfl
  rw [h]
  infer_instance

private theorem derivedUnit_isIso {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (M : Der (restrictRing m j R)) :
    IsIso ((exactDerivedAdjunction o.adjunction).unit.app M) := by
  let a := exactDerivedAdjunction o.adjunction
  have hQ (P : CochainComplex (Mod (restrictRing m j R)) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ,
          IsIso (((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
        fun n ↦ ordinaryUnit_isIso o (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          (restrict m j R).mapDerivedCategoryFactors.inv.app _ ≫
            (restrict m j R).mapDerivedCategory.map
              (o.ordinary.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, exactDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

private theorem localized_normalization
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (b : G ⊣ F)
    (h : ∀ M, a.unit.app M ≫ b.counit.app M = 𝟙 M) :
    ∀ M, (exactDerivedAdjunction a).unit.app M ≫
      (exactDerivedAdjunction b).counit.app M = 𝟙 M := by
  have hQ (P : CochainComplex C ℤ) :
      (exactDerivedAdjunction a).unit.app (DerivedCategory.Q.obj P) ≫
        (exactDerivedAdjunction b).counit.app (DerivedCategory.Q.obj P) = 𝟙 _ := by
    simp only [exactDerivedAdjunction, Adjunction.mapExactDerivedCategory,
      Adjunction.localization_unit_app, Adjunction.localization_counit_app, Category.assoc]
    change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).counit.app P) = _
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [G.mapDerivedCategory.map_id]
    rw [Category.id_comp, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
    have hh : (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫
        (b.mapHomologicalComplex (.up ℤ)).counit.app P = 𝟙 P := by
      ext n
      exact h (P.X n)
    erw [hh, CategoryTheory.Functor.map_id]
    rfl
  have hn : (exactDerivedAdjunction a).unit ≫
      (exactDerivedAdjunction b).counit = 𝟙 _ := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    exact hQ
  exact fun M ↦ congr_app hn M

private theorem clopen_projection {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    (v : Data o s) (F V : Der (restrictRing m d.j' d.S)) :
    v.rho.app (o.tensorU'.functor.obj (F, V)) ≫
        v.extensionS.ordinary.mapDerivedCategory.map
          (v.tensorS.tensorComparison.comparison.hom.app (F, V)) =
      o.tensorU'.functor.map (Prod.mkHom (v.rho.app F) (𝟙 V)) ≫
        v.tensorS.delta.hom.app
          ((restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.obj F, V) := by
  exact clopen_tensor_of_normalization _ _
    (exactDerivedAdjunction v.extensionS.adjunction)
    (exactDerivedAdjunction v.rightAdjunction) _ _
    v.tensorS.tensorComparison.comparison v.tensorS.delta
    (localized_normalization _ _ v.counit_normalization)
    (derivedUnit_isIso v.extensionS) v.tensorS.inverse_transpose F V

private theorem composite_open {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    (v : Data o s) (M : Der (restrictRing m s (restrictRing m d.j' d.S)))
    (N : Der d.S) :
    v.tensorB.delta.hom.app (v.extensionS.ordinary.mapDerivedCategory.obj M, N) ≫
      o.opens.jShriek'.map (v.tensorS.delta.hom.app (M, o.opens.jStar'.obj N)) =
        v.deltaK.hom.app (M, N) := by
  let x := v.tensorB.delta.app (v.extensionS.ordinary.mapDerivedCategory.obj M, N) ≪≫
    o.opens.jShriek'.mapIso (v.tensorS.delta.app (M, o.opens.jStar'.obj N))
  have hi : x.inv = (v.deltaK.app (M, N)).inv := by
    apply (((exactDerivedAdjunction v.extensionS.adjunction).comp
      o.opens.adj').homEquiv _ _).injective
    exact (open_tensor_composite_transpose _ _ _ _
      (exactDerivedAdjunction v.extensionS.adjunction) o.opens.adj' _ _ _
      v.tensorS.tensorComparison.comparison v.tensorB.tensorComparison.comparison
      v.tensorS.delta v.tensorB.delta v.tensorS.inverse_transpose
      v.tensorB.inverse_transpose M N).trans (v.inverse_transposeK M N).symm
  exact congrArg Iso.inv (Iso.ext hi : x.symm = (v.deltaK.app (M, N)).symm)

/-- The four normalized clopen tensor identities hold for every supplied datum.

Source: Stacks Project, `sites-cohomology.tex`, Tags 07A4 (`lemma-pullback-tensor-product`)
and 0GL1 (`lemma-j-shriek-and-tensor`), with the clopen tensor refinement of Stacks
0F7B, original steps 1--7 (blueprint: lem-sf-clopen-comparison-tensor-square-equations).

Proof plan: localize the ordinary unit--counit normalization. Under the resulting
reverse adjunction, both sides of the clopen tensor square transpose to the restriction
tensor comparison, using its naturality and the triangle identity. Transpose the
inverses of the composite-open comparisons under the composite adjunction; tensor
naturality and the formula for its unit identify them. Finally expand `alpha` and
paste the Cartesian, clopen, and composite-open identities, moving `rho` through the
tensor comparison by naturality. The argument uses
`lem-sf-clopen-cartesian-tensor-square`, `def-weil-exact-derived-adjunction`, and
`def-sf-open-normalization-data`.
-/
theorem equations_for_data {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s) : Equations a v := by
  rw [Equations]
  refine ⟨cartesian_tensor a v, clopen_projection v, composite_open v, ?_⟩
  intro H N
  have hp := tensor_square_clopen_factors o.opens.jStar o.gPull.derived
    o.gUPull.derived o.opens.jStar'
    (restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory
    v.extensionS.ordinary.mapDerivedCategory o.opens.jShriek' o.opens.jShriek
    v.tensorA.functor o.tensorX'.functor o.tensorU.functor o.tensorX.functor
    o.tensorU'.functor v.tensorP.comparison.hom v.tensorQ.comparison.hom
    v.tensorS.tensorComparison.comparison.hom a.gamma.hom v.tensorB.delta.hom
    v.tensorS.delta.hom a.beta.hom o.theta v.rho
    (cartesian_tensor a v) (clopen_projection v) H N
  rw [composite_open v] at hp
  let e := o.opens.jShriek'.mapIso (v.extensionS.ordinary.mapDerivedCategory.mapIso
    (v.tensorA.functor.mapIso
      ((Iso.refl ((restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.obj
        (o.gUPull.derived.obj H))).prod
        ((restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.mapIso
          (o.theta.app N)))))
  simp only [← Category.assoc] at hp
  change _ ≫ e.inv = _ at hp
  have he := congrArg (fun f ↦ f ≫ e.hom) hp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he
  simpa only [alpha, Functor.map_comp, Category.assoc, e, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Iso.app_hom, restrictionModel,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj] using he

end SheafOfModules.ClopenComparisonTensorSquare
