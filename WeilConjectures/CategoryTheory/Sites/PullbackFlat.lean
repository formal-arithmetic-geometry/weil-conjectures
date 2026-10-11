/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Vanishing

/-!
# Pullback of sheaves along a flat functor preserves flatness

Let `G : C ⥤ D` be a representably flat, cover-preserving functor between sites and let `R` be
a Noetherian commutative ring. The pullback `G^* F = (Lan_{G} F)^#` of a flat sheaf `F` of
`R`-modules is flat (`CategoryTheory.flat_sheafPullback_obj`).

Tensoring with a sheafification is the sheafification of the presheaf tensor product, so it
suffices that `Lan_G F ⊗ M ⟶ Lan_G F ⊗ N` is locally injective for every injection `M ⟶ N`
of presheaves. The left Kan extension is a filtered colimit
`(Lan_G F)(U) = colim_{U ⟶ G V} F(V)`. A section of `Lan_G F ⊗ M` over `U` killed in
`Lan_G F ⊗ N` vanishes there through finitely many `R`-linear relations between finitely many
elements of `(Lan_G F)(U)` (`TensorProduct.exists_relations_of_sum_tmul_eq_zero`); these come
from one stage `F(V)` where the relations already hold (`ModuleCat.exists_lift_of_isColimit`).
Since `F` is flat, the relations are trivial locally on `V`
(`CategoryTheory.Sheaf.exists_factorization_of_flat`), and pulling the covering back to `U`
along `G` makes the section vanish locally.

This is the argument of blueprint `lem-exc-constant-inverse-image-flat` (the relation criterion
for flatness transported by an exact inverse image), at the level of an arbitrary flat
cover-preserving functor.

## Main results

- `CategoryTheory.Sheaf.equalizerSieve_lan_whiskerLeft_mem`: the local injectivity of
  `Lan_G F ⊗ M ⟶ Lan_G F ⊗ N`.
- `CategoryTheory.flat_sheafPullback_obj`: the pullback of a flat sheaf of modules along a
  representably flat cover-preserving functor is flat.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

namespace CategoryTheory

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [EssentiallySmall.{u + 1} C]
  [EssentiallySmall.{u + 1} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Type (u + 1)} [CommRing R] [IsNoetherianRing R]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
  {G : C ⥤ D} [RepresentablyFlat G]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R, G.op.HasPointwiseLeftKanExtension P]

omit [EssentiallySmall.{u + 1} D] in
/-- **Local injectivity of `Lan_G F ⊗ M ⟶ Lan_G F ⊗ N`.** Let `F` be a flat sheaf of modules
over a Noetherian ring and `M ⟶ N` an injection of presheaves of modules on `D`. A section of
`Lan_G F ⊗ M` killed in `Lan_G F ⊗ N` vanishes locally. -/
theorem Sheaf.equalizerSieve_lan_whiskerLeft_mem (hG : CoverPreserving J K G)
    {F : Sheaf J (ModuleCat.{u + 1} R)} (hF : ObjectProperty.flat F)
    {M N : Dᵒᵖ ⥤ ModuleCat.{u + 1} R} (g : M ⟶ N) (hg : ∀ U, Function.Injective (g.app U))
    {U : D} (t : ((G.op.lan.obj F.obj) ⊗ M).obj (op U))
    (ht : ((G.op.lan.obj F.obj) ◁ g).app (op U) t = 0) :
    Presheaf.equalizerSieve t 0 ∈ K U := by
  classical
  let P := G.op.lan.obj F.obj
  -- `t = ∑ₖ mₖ ⊗ g'ₖ`, and its image `∑ₖ mₖ ⊗ g(g'ₖ)` vanishes through finitely many relations
  obtain ⟨n, m, g', htm⟩ :=
    TensorProduct.exists_sum_tmul_eq (t : P.obj (op U) ⊗[R] M.obj (op U))
  have ht₀ : ∑ k, m k ⊗ₜ[R] g.app (op U) (g' k) = 0 := by
    have : (LinearMap.lTensor _ (g.app (op U)).hom) (t : P.obj (op U) ⊗[R] M.obj (op U)) = 0 :=
      ht
    rw [htm] at this
    simpa [map_sum] using this
  obtain ⟨s, q, y, a, e, hma, hey, hab⟩ :=
    TensorProduct.exists_relations_of_sum_tmul_eq_zero m (fun k ↦ g.app (op U) (g' k)) ht₀
  -- rewrite `t = ∑ⱼ yⱼ ⊗ g''ⱼ`; every solution of the relations `e` kills `g''`
  let g'' : Fin s → M.obj (op U) := fun j ↦ ∑ k, a k j • g' k
  have ht' : (t : P.obj (op U) ⊗[R] M.obj (op U)) = ∑ j, y j ⊗ₜ[R] g'' j := by
    rw [htm]
    simp only [g'', hma, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
    exact Finset.sum_comm
  have hg'' (c : Fin s → R) (hc : ∀ l, ∑ j, e l j * c j = 0) : ∑ j, c j • g'' j = 0 := by
    refine hg (op U) ?_
    rw [map_zero, ← hab c hc]
    simp only [g'', map_sum, map_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  -- the elements `yⱼ` and their relations come from one stage `F(V)` of the colimit
  have : IsFiltered (CostructuredArrow G.op (op U)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence G U)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let hcol := G.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj (op U)
  obtain ⟨T₀, y', hy', hey'⟩ := ModuleCat.exists_lift_of_isColimit hcol y e hey
  -- the relations are trivial locally on `V`, as `F` is flat
  obtain ⟨S, hS, hfac⟩ :=
    Sheaf.exists_factorization_of_flat hF (V := T₀.left.unop) y' e hey'
  refine K.superset_covering ?_ (K.pullback_stable T₀.hom.unop (hG.cover_preserve hS))
  rintro U' h ⟨W, f, h', hf, hcomp⟩
  obtain ⟨t', b, z, heb, hyz⟩ := hfac f hf
  change (P ⊗ M).map h.op t = (P ⊗ M).map h.op 0
  rw [map_zero]
  change (TensorProduct.map (P.map h.op).hom (M.map h.op).hom)
    (t : P.obj (op U) ⊗[R] M.obj (op U)) = 0
  -- restricted to `U'`, each `yⱼ` is `∑ₘ bⱼₘ wₘ`
  let w : Fin t' → P.obj (op U') := fun m ↦
    P.map h'.op ((G.op.leftKanExtensionUnit F.obj).app (op W) (z m))
  have hPy (j : Fin s) : P.map h.op (y j) = ∑ m, b j m • w m := by
    rw [← hy' j]
    change P.map h.op (P.map T₀.hom ((G.op.leftKanExtensionUnit F.obj).app T₀.left (y' j))) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have hτ : T₀.hom ≫ h.op = G.op.map f.op ≫ h'.op := by
      exact Quiver.Hom.unop_inj (by simpa using hcomp)
    rw [hτ, Functor.map_comp, ConcreteCategory.comp_apply]
    have hnat := NatTrans.naturality_apply (G.op.leftKanExtensionUnit F.obj) f.op (y' j)
    change _ = P.map (G.op.map f.op) _ at hnat
    rw [← hnat, hyz j]
    simp [w, map_sum, map_smul]
  rw [ht']
  simp only [map_sum, TensorProduct.map_tmul]
  simp_rw [hPy, TensorProduct.sum_tmul, TensorProduct.smul_tmul]
  rw [Finset.sum_comm]
  simp_rw [← TensorProduct.tmul_sum, ← map_smul, ← map_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [hg'' (fun j ↦ b j m) (fun l ↦ by simpa [Matrix.mul_apply] using congrFun (congrFun heb l) m),
    map_zero, TensorProduct.tmul_zero]

omit [EssentiallySmall.{u + 1} D] in
/-- **Local injectivity of `Lan_G F ⊗ M ⟶ Lan_G F ⊗ N`.** Tensoring the left Kan extension of a
flat sheaf of modules with an injection of presheaves of modules is locally injective. -/
theorem Sheaf.isLocallyInjective_lan_whiskerLeft (hG : CoverPreserving J K G)
    {F : Sheaf J (ModuleCat.{u + 1} R)} (hF : ObjectProperty.flat F)
    {M N : Dᵒᵖ ⥤ ModuleCat.{u + 1} R} (g : M ⟶ N) (hg : ∀ U, Function.Injective (g.app U)) :
    Presheaf.IsLocallyInjective K ((G.op.lan.obj F.obj) ◁ g) where
  equalizerSieve_mem {U} x y hxy := by
    have h := Sheaf.equalizerSieve_lan_whiskerLeft_mem hG hF g hg (U := U.unop) (x - y)
      (by rw [map_sub, hxy, sub_self])
    refine K.superset_covering ?_ h
    intro U' f hf
    change _ = _ at hf
    rw [map_sub, map_zero, sub_eq_zero] at hf
    exact hf

variable [K.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [K.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]

/-- Blueprint `lem-exc-constant-inverse-image-flat`, for an arbitrary site morphism:
**pullback along a flat functor preserves flat sheaves of modules.** Let `G : C ⥤ D` be a
representably flat, cover-preserving functor and `R` a Noetherian commutative ring. The pullback
`G^* F = (Lan_G F)^#` of a flat sheaf `F` of `R`-modules on `C` is flat.

Tensoring with `G^* F` is the sheafification of tensoring with the presheaf `Lan_G F`, which
preserves injections up to local vanishing
(`CategoryTheory.Sheaf.isLocallyInjective_lan_whiskerLeft`); sheafification turns locally
injective maps into monomorphisms. -/
theorem flat_sheafPullback_obj (hG : CoverPreserving J K G) {F : Sheaf J (ModuleCat.{u + 1} R)}
    (hF : ObjectProperty.flat F) :
    ObjectProperty.flat
      ((Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} R) J K).obj F) := by
  let P := G.op.lan.obj F.obj
  change ObjectProperty.flat ((presheafToSheaf K _).obj P)
  rw [ObjectProperty.flat_iff_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  have := hS.mono_f
  let g := S.f
  -- `g` is injective on sections
  have hg : ∀ U, Function.Injective (g.hom.app U) := fun U ↦ by
    have : Mono g.hom := (sheafToPresheaf K _).map_mono g
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  -- `(Lan_G F)^# ◁ g` is, up to isomorphism, the sheafification of `Lan_G F ◁ g`
  have : Presheaf.IsLocallyInjective K (P ◁ g.hom) :=
    Sheaf.isLocallyInjective_lan_whiskerLeft hG hF g.hom hg
  have : Sheaf.IsLocallyInjective ((presheafToSheaf K _).map (P ◁ g.hom)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff K (P ◁ g.hom)).2 this
  have : Mono ((presheafToSheaf K _).map (P ◁ g.hom)) := Sheaf.mono_of_isLocallyInjective _
  let μ := Sheaf.presheafToSheafCompTensorLeftIso (J := K) (A := ModuleCat.{u + 1} R) P
  have h₁ : (presheafToSheaf K _).obj P ◁ (presheafToSheaf K _).map g.hom =
      μ.hom.app _ ≫ (presheafToSheaf K _).map (P ◁ g.hom) ≫ μ.inv.app _ := by
    have hn := μ.hom.naturality g.hom
    change _ ◁ _ ≫ _ = _ ≫ (presheafToSheaf K _).map (P ◁ g.hom) at hn
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  let ε := (sheafificationAdjunction K (ModuleCat.{u + 1} R)).counit
  have h₂ : g = inv (ε.app S.X₁) ≫ (presheafToSheaf K _).map g.hom ≫ ε.app S.X₂ := by
    rw [IsIso.eq_inv_comp]
    exact (ε.naturality g).symm
  change Mono ((presheafToSheaf K _).obj P ◁ g)
  rw [h₂, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp, h₁]
  infer_instance

end CategoryTheory
