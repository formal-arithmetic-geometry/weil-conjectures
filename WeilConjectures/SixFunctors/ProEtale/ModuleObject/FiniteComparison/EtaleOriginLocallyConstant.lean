/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCokernel
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank

/-!
# Finitely presented module objects are locally constant with finite stalks

Let `T` be a finite discrete commutative ring and `Φ_W : Mod_{T_W} ≌ Sh(W_proét, T)` the
comparison of the two models of pro-étale sheaves with coefficients in `T`
(`ProEtale.finiteCoefficientModEquivalence`). This file proves that for a finitely presented
module object `P` over `T_W = p_W^* T̲`, the sheaf of `T`-modules `Φ_W(P)` is locally constant
with finite stalks (`ProEtale.isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj`).

Write `P ≅ coker(φ)` for a matrix `φ : T_W^m ⟶ T_W^n`. Its entries are continuous functions
`W → T` (`ProEtale.CondensedRing.continuousMapEndRegularRingEquiv`), so they are constant on the
members `W_c` of a finite open cover of `W`. On `W_c` the matrix is a matrix of scalars, which `Φ`
sends to the multiplication by the scalars
(`ProEtale.finiteCoefficientModEquivalence_map_regularLift`), and `Φ(T_W)` is the constant sheaf
`T` (`ProEtale.finiteCoefficientModEquivalenceRegularIso`); so `Φ_{W_c}(P|_{W_c})` is the constant
sheaf of a finite `T`-module
(`CategoryTheory.Sheaf.exists_iso_constantSheaf_cokernel_matrix_scalarEnd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] {A : C} [MonObj A]
  [IsCommMonObj A]

/-- On the regular module of a commutative monoid object, the linear map sending `1` to a global
section `s` is the action of `s`. -/
lemma regularLift_regular_hom (s : 𝟙_ C ⟶ A) :
    (regularLift (regular A) s).hom = globalSmul s (regular A) := by
  have key : (ρ_ A).inv ≫ A ◁ s ≫ μ = (λ_ A).inv ≫ s ▷ A ≫ μ := by
    conv_lhs => rw [← IsCommMonObj.mul_comm A, BraidedCategory.braiding_naturality_right_assoc,
      rightUnitor_inv_braiding_assoc]
  exact key


section Abelian

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R]

/-- The entries of a matrix of endomorphisms of the regular module. -/
@[simp]
lemma finFreeEntry_matrix {m n : ℕ} (M : Fin m → Fin n → End (regular R)) (a : Fin n)
    (b : Fin m) : finFreeEntry (biproduct.matrix M) a b = M b a := by
  simp [finFreeEntry]

end Abelian
end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (W : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- **`Φ` sends the multiplication by a constant scalar to the multiplication by the scalar**:
the endomorphism of the regular module `T_W` given by the constant global section `t` of `T̲`
becomes the multiplication by `t` on the sheaf of `T`-modules `Φ_W(T_W)`. -/
lemma finiteCoefficientModEquivalence_map_regularLift (t : T) :
    (finiteCoefficientModEquivalence W T).functor.map
        (Mod.regularLift (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) W))
          (ε (upperStarFromPoint W) ≫
            (upperStarFromPoint W).map (Profinite.continuousMapConstRingHom.{u} T t).hom)) =
      Sheaf.scalarEnd (ULift.up t : ULift.{u + 1} T) _ := by
  ext U y
  rw [Sheaf.scalarEnd_hom_app_apply, finiteCoefficientModEquivalence_smul,
    ← Mod.regularLift_regular_hom]
  rfl

/-- `Φ_W(T_W)` corepresents the sections over `W`: morphisms `Φ_W(T_W) ⟶ G` are morphisms
`T_W ⟶ Φ_W⁻¹ G`, i.e. global sections of `Φ_W⁻¹ G`, which has the same underlying abelian
sheaf as `G`. -/
noncomputable def finiteCoefficientModEquivalenceRegularCorepresentableBy :
    (Sheaf.sectionsTypeFunctor (ProEt.topology W) (R := ULift.{u + 1} T)
      (T := ProEt.mk (𝟙 W))).CorepresentableBy
      ((finiteCoefficientModEquivalence W T).functor.obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) W))) where
  homEquiv {G} := ((finiteCoefficientModEquivalence W T).toAdjunction.homEquiv _ G).trans
    ((Mod.regularHomAddEquiv _).toEquiv.trans
      ((Sheaf.unitHomEvalAddEquiv (ProEt.isTerminalMkId W)
        ((finiteCoefficientModEquivalence W T).inverse.obj G).X).toEquiv.trans
        (((sheafSections _ _).obj (op (ProEt.mk (𝟙 W)))).mapIso
          ((finiteCoefficientModEquivalence W T).counitIso.app G)).toLinearEquiv.toEquiv))
  homEquiv_comp g f := by
    simp only [Equiv.trans_apply, Adjunction.homEquiv_naturality_right,
      AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Mod.regularHomAddEquiv_apply,
      Sheaf.unitHomEvalAddEquiv_apply, Mod.comp_hom']
    exact congrArg (fun φ ↦ φ.hom.app (op (ProEt.mk (𝟙 W)))
      (Sheaf.unitHomEval (J := ProEt.topology W) (ProEt.mk (𝟙 W))
        (F := ((finiteCoefficientModEquivalence W T).inverse.obj _).X)
        ((η : 𝟙_ _ ⟶ condensedRingObj (Profinite.continuousMapRingObj T) W) ≫
        (((finiteCoefficientModEquivalence W T).toAdjunction.homEquiv _ _) f).hom)))
      ((finiteCoefficientModEquivalence W T).counitIso.hom.naturality g)

/-- **`Φ_W(T_W)` is the constant sheaf `T`**, both corepresenting the sections over `W`. -/
noncomputable def finiteCoefficientModEquivalenceRegularIso :
    (finiteCoefficientModEquivalence W T).functor.obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) W)) ≅
      (constantSheaf (ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
        (ModuleCat.of _ (ULift.{u + 1} T)) :=
  (finiteCoefficientModEquivalenceRegularCorepresentableBy W T).uniqueUpToIso
    (Sheaf.constantSheafCorepresentableBy (R := ULift.{u + 1} T) (ProEt.topology W)
      (ProEt.isTerminalMkId W))

variable {W T} in
/-- **Local constancy on a piece**: if on an open `V ⊆ W` the entries of a matrix
`φ : T_W^m ⟶ T_W^n` are the constant functions `c`, then `Φ_V(coker(φ)|_V)` is the constant sheaf
of a finite `T`-module. -/
lemma exists_iso_constantSheaf_finiteCoefficientModEquivalence_upperStar_cokernel {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj T) W) m ⟶
      Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj T) W) n)
    (V : W.Opens) (c : Fin n → Fin m → T)
    (hc : ∀ a b (x : V), CondensedRing.continuousMapEndRegularRingEquiv T W
      (Mod.finFreeEntry φ a b) (V.ι x) = c a b) :
    ∃ N : ModuleCat.{u + 1} (ULift.{u + 1} T), Finite N ∧
      Nonempty ((finiteCoefficientModEquivalence V T).functor.obj
          ((CondensedRing.upperStar (Profinite.continuousMapRingObj T) V.ι).obj (cokernel φ)) ≅
        (constantSheaf (ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj N) := by
  let ψ := CondensedRing.upperStarFinFreeMap _ V.ι φ
  have hψ : ψ = biproduct.matrix fun b a ↦
      Mod.regularLift (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) V))
        (ε (upperStarFromPoint V) ≫
          (upperStarFromPoint V).map (Profinite.continuousMapConstRingHom.{u} T (c a b)).hom) := by
    refine Mod.finFree_hom_ext fun a b ↦ ?_
    rw [CondensedRing.ι_upperStarFinFreeMap_π]
    rw [Mod.finFreeEntry_matrix]
    apply (CondensedRing.continuousMapEndRegularRingEquiv T V).injective
    rw [CondensedRing.continuousMapEndRegularRingEquiv_restrictEnd,
      ← CondensedRing.continuousMapEndRegularRingEquiv_symm_const, RingEquiv.apply_symm_apply]
    ext x
    exact hc a b x
  let Φ := (finiteCoefficientModEquivalence V T).functor
  have : HasFiniteBiproducts (Sheaf (ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  obtain ⟨N, hN, ⟨e⟩⟩ := Sheaf.exists_iso_constantSheaf_cokernel_matrix_scalarEnd
    (ProEt.topology V) (ProEt.isTerminalMkId V) (finiteCoefficientModEquivalenceRegularIso V T)
    (fun b a ↦ (ULift.up (c a b) : ULift.{u + 1} T))
  refine ⟨N, hN, ⟨Φ.mapIso ((CondensedRing.cokernelUpperStarFinFreeMapIso _ V.ι φ).symm ≪≫
    cokernelIsoOfEq hψ) ≪≫ PreservesCokernel.iso Φ _ ≪≫
    cokernel.mapIso _ _ (Φ.mapBiproductConstIso (Iso.refl _) _)
      (Φ.mapBiproductConstIso (Iso.refl _) _) ?_ ≪≫ e⟩⟩
  rw [← Iso.inv_comp_eq, Φ.map_biproduct_matrix_conj]
  simp [Φ, finiteCoefficientModEquivalence_map_regularLift]

variable {W T} in
/-- **Finitely presented module objects are locally constant with finite stalks**: for a
finitely presented module object `P` over `T_W`, the sheaf of `T`-modules `Φ_W(P)` is locally
constant with finite stalks. Writing `P ≅ coker(φ)` for a matrix `φ : T_W^m ⟶ T_W^n` of continuous
functions `W → T`, the opens `W_c` on which the entries of `φ` are the constants `c` cover `W`. -/
theorem isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj
    {P : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) W)}
    (hP : Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) W) P) :
    IsFiniteLocallyConstant (ULift.{u + 1} T)
      ((finiteCoefficientModEquivalence W T).functor.obj P) := by
  obtain ⟨n, m, φ, ⟨e⟩⟩ := hP
  let f (a : Fin n) (b : Fin m) : C(W, T) :=
    CondensedRing.continuousMapEndRegularRingEquiv T W (Mod.finFreeEntry φ a b)
  let V (c : Fin n → Fin m → T) : W.Opens := ⟨{x | ∀ a b, f a b x = c a b}, by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun a ↦ isOpen_iInter_of_finite fun b ↦
      (f a b).continuous.isOpen_preimage {c a b} (isOpen_discrete _)⟩
  refine ⟨ULift.{u + 1} (Fin n → Fin m → T), fun c ↦ (V c.down : Scheme.{u}),
    fun c ↦ (V c.down).ι,
    ofArrows_opens_ι_mem_proetalePrecoverage _ fun x ↦ ⟨⟨fun a b ↦ f a b x⟩, fun a b ↦ rfl⟩,
    fun c ↦ ?_⟩
  obtain ⟨N, hN, ⟨e'⟩⟩ :=
    exists_iso_constantSheaf_finiteCoefficientModEquivalence_upperStar_cokernel φ (V c.down)
      c.down fun a b x ↦ x.2 a b
  exact ⟨N, hN, ⟨(finiteCoefficientModUpperStarIso T (V c.down).ι).app P ≪≫
    (finiteCoefficientModEquivalence (V c.down) T).functor.mapIso
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj T) (V c.down).ι).mapIso e) ≪≫ e'⟩⟩

end AlgebraicGeometry.ProEtale
