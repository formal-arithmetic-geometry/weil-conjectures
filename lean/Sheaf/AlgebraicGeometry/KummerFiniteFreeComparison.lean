/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The finite free Kummer coefficient comparison

Source: blueprint finite-direct-sum argument for Kummer coefficients.
(blueprint: lem-pur-kummer-finite-free-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

private def rootModuleSheaf (C : Scheme.{u}) (m : ℕ) :
    Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) :=
  ⟨kummerRootModulePresheaf C m, by
    apply (Presheaf.isSheaf_of_isSheaf_comp C.smallEtaleTopology _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat))
    exact (C.rootsOfUnitySheaf m).property⟩

private def rootTensorCoordinate (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    (c : A →ₗ[ULift.{u + 1} (ZMod m)] ULift.{u + 1} (ZMod m)) :
    kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A ⟶
      kummerRootModulePresheaf C m where
  app U := ModuleCat.ofHom ((TensorProduct.rid _ _).toLinearMap.comp
    (c.lTensor ((kummerRootModulePresheaf C m).obj U)))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x a
    change c a • (kummerRootModulePresheaf C m).map f x =
      (kummerRootModulePresheaf C m).map f (c a • x)
    exact ((kummerRootModulePresheaf C m).map f).hom.map_smul _ _ |>.symm

private def rootCoordinate (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    (c : A →ₗ[ULift.{u + 1} (ZMod m)] ULift.{u + 1} (ZMod m)) :
    (kummerModuleTwist C m).obj A ⟶ rootModuleSheaf C m :=
  ⟨sheafifyLift C.smallEtaleTopology (rootTensorCoordinate C m A c)
    (rootModuleSheaf C m).property⟩

private lemma rootCoordinate_tmul (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    (c : A →ₗ[ULift.{u + 1} (ZMod m)] ULift.{u + 1} (ZMod m))
    (U : C.Etaleᵒᵖ) (x : (kummerRootModulePresheaf C m).obj U) (a : A) :
    (rootCoordinate C m A c).hom.app U
      ((toSheafify C.smallEtaleTopology
        (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U
          (x ⊗ₜ a)) = c a • x := by
  have h := congrArg (fun f ↦ f.app U (x ⊗ₜ a))
    (toSheafify_sheafifyLift C.smallEtaleTopology (rootTensorCoordinate C m A c)
      (rootModuleSheaf C m).property)
  exact h

private def rootModuleInsertion (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a : A) :
    rootModuleSheaf C m ⟶ (kummerModuleTwist C m).obj A :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
        ((TensorProduct.mk _ ((kummerRootModulePresheaf C m).obj U) A).flip a)
     naturality := by
       intro U V f
       ext x
       rfl } ≫ toSheafify C.smallEtaleTopology
         (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)⟩

private lemma rootCoordinate_insertion (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a : A)
    (c : A →ₗ[ULift.{u + 1} (ZMod m)] ULift.{u + 1} (ZMod m)) :
    rootModuleInsertion C m A a ≫ rootCoordinate C m A c =
      (c a) • 𝟙 (rootModuleSheaf C m) := by
  ext U x
  exact rootCoordinate_tmul C m A c U x a

private lemma rootCoordinate_total (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    {ι : Type*} [Fintype ι] (v : ι → A)
    (c : ι → A →ₗ[ULift.{u + 1} (ZMod m)] ULift.{u + 1} (ZMod m))
    (hc : ∀ a, ∑ j, c j a • v j = a) :
    ∑ j, rootCoordinate C m A (c j) ≫ rootModuleInsertion C m A (v j) =
      𝟙 ((kummerModuleTwist C m).obj A) := by
  apply (sheafToPresheaf _ _).map_injective
  rw [Functor.map_sum, CategoryTheory.Functor.map_id]
  apply sheafify_hom_ext _ _ _ ((kummerModuleTwist C m).obj A).property
  simp only [Preadditive.comp_sum]
  ext U : 2
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x a
  simp only [NatTrans.app_sum, ModuleCat.hom_sum, LinearMap.sum_apply,
    NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  change (∑ j, (rootModuleInsertion C m A (v j)).hom.app U
    ((rootCoordinate C m A (c j)).hom.app U
      ((toSheafify C.smallEtaleTopology
        (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U
          (x ⊗ₜ a)))) = _
  simp only [rootCoordinate_tmul]
  have hi (z : (kummerRootModulePresheaf C m).obj U) (a : A) :
      (rootModuleInsertion C m A a).hom.app U z =
        (toSheafify C.smallEtaleTopology
          (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U
            (z ⊗ₜ a) := rfl
  simp only [hi]
  simp_rw [TensorProduct.smul_tmul]
  let eta := ((toSheafify C.smallEtaleTopology
    (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U).hom
  change (∑ j, eta (x ⊗ₜ (c j a • v j))) = eta (x ⊗ₜ a)
  rw [← map_sum, ← TensorProduct.tmul_sum, hc]

/-- A specified finite dual basis gives the normalized finite-sum tensor comparison.
Source: Stacks Tag 03EK, finite basis calculation in the Kummer coefficient argument.
Proof: project a pure tensor using each coordinate. Insertion followed by projection
is the Kronecker identity; the sum of projection followed by insertion fixes every
pure tensor. The latter identity descends through sheafification. These two identities
give inverse maps between the finite biproduct and the twisted sheaf.
(blueprint: lem-pur-kummer-finite-free-comparison). -/
theorem kummer_dual_basis_sheaf_comparison (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → A)
    (c : ι → A →ₗ[ULift.{u + 1} (ZMod m)] ULift.{u + 1} (ZMod m))
    (hcv : ∀ i j, c j (v i) = if i = j then 1 else 0)
    (hc : ∀ a, ∑ j, c j a • v j = a)
    [HasBiproduct (fun _ : ι ↦ C.rootsOfUnitySheaf m)] :
    ∃ theta : (⨁ fun _ : ι ↦ C.rootsOfUnitySheaf m) ≅
        (kummerAbelianTwist C m).obj A,
      ∀ j, biproduct.ι (fun _ : ι ↦ C.rootsOfUnitySheaf m) j ≫ theta.hom =
        kummerCoefficientInsertion C m A (v j) := by
  let forgetM := sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat)
  let p (j : ι) : (kummerAbelianTwist C m).obj A ⟶ C.rootsOfUnitySheaf m :=
    forgetM.map (rootCoordinate C m A (c j))
  let i (j : ι) := kummerCoefficientInsertion C m A (v j)
  have hip (j k : ι) : i j ≫ p k = if j = k then 𝟙 _ else 0 := by
    change forgetM.map (rootModuleInsertion C m A (v j)) ≫
      forgetM.map (rootCoordinate C m A (c k)) = _
    rw [← forgetM.map_comp, rootCoordinate_insertion, hcv]
    by_cases h : j = k
    · simp only [h, if_true, one_smul]
      rw [forgetM.map_id]
      rfl
    · simp only [h, if_false, zero_smul, Functor.map_zero]
  have htotal : ∑ j, p j ≫ i j = 𝟙 _ := by
    change ∑ j, forgetM.map (rootCoordinate C m A (c j)) ≫
      forgetM.map (rootModuleInsertion C m A (v j)) = _
    simp_rw [← forgetM.map_comp]
    rw [← Functor.map_sum, rootCoordinate_total C m A v c hc]
    exact forgetM.map_id _
  let t : (⨁ fun _ : ι ↦ C.rootsOfUnitySheaf m) ≅
      (kummerAbelianTwist C m).obj A :=
    { hom := biproduct.desc i
      inv := biproduct.lift p
      hom_inv_id := by
        apply biproduct.hom_ext'
        intro j
        apply biproduct.hom_ext
        intro k
        simp [Category.assoc, hip, biproduct.ι_π]
      inv_hom_id := (biproduct.lift_desc (g := p) (h := i)).trans htotal }
  exact ⟨t, fun j ↦ biproduct.ι_desc _ _⟩

private lemma cohomology_map_sum (C : Scheme.{u})
    {F G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {ι : Type*} (s : Finset ι) (f : ι → (F ⟶ G)) (q : ℕ) (x : Sheaf.H F q) :
    Sheaf.H.map (∑ j ∈ s, f j) q x = ∑ j ∈ s, Sheaf.H.map (f j) q x := by
  induction s using Finset.cons_induction with
  | empty =>
    exact congrArg (fun f ↦ f x) ((Sheaf.functorH C.smallEtaleTopology q).map_zero F G)
  | cons a s ha ih => simp only [Finset.sum_cons, Sheaf.H.map_add_apply, ih]

private lemma cohomology_map_zsmul (C : Scheme.{u})
    {F G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) (q : ℕ) (n : ℤ) (x : Sheaf.H F q) :
    Sheaf.H.map (n • f) q x = n • Sheaf.H.map f q x := by
  exact congrArg (fun f ↦ f x) ((Sheaf.functorH C.smallEtaleTopology q).map_zsmul
    (f := f) (r := n))

private def residueLinear {m : ℕ} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ULift.{u + 1} (ZMod m)) M] [Module (ULift.{u + 1} (ZMod m)) N]
    (f : M →+ N) : M →ₗ[ULift.{u + 1} (ZMod m)] N :=
  { f with
    map_smul' := by
      intro t a
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective t.down
      have ht : (n : ULift.{u + 1} (ZMod m)) = t := ULift.ext _ _ hn
      rw [← ht]
      exact map_intCast_smul f _ _ n a }

private def insertionLinear (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) :
    A →ₗ[ULift.{u + 1} (ZMod m)]
      (rootModuleSheaf C m ⟶ (kummerModuleTwist C m).obj A) where
  toFun := rootModuleInsertion C m A
  map_add' a b := by
    ext U x
    change (toSheafify C.smallEtaleTopology
      (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U
        (x ⊗ₜ (a + b)) = _
    simp only [TensorProduct.tmul_add, map_add]
    rfl
  map_smul' t a := by
    ext U x
    change (toSheafify C.smallEtaleTopology
      (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U
        (x ⊗ₜ (t • a)) = t • (toSheafify C.smallEtaleTopology
      (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U (x ⊗ₜ a)
    rw [TensorProduct.tmul_smul, map_smul]

private def cohomologyModuleHom (C : Scheme.{u}) (m q : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) :
    (rootModuleSheaf C m ⟶ (kummerModuleTwist C m).obj A) →ₗ[
      ULift.{u + 1} (ZMod m)]
      (Sheaf.H (C.rootsOfUnitySheaf m) q →+
        Sheaf.H ((kummerAbelianTwist C m).obj A) q) :=
  residueLinear
    ((AddCommGrpCat.homAddEquiv.toAddMonoidHom).comp
    (((Sheaf.functorH C.smallEtaleTopology q).mapAddHom).comp
      ((sheafCompose C.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
          AddCommGrpCat)).mapAddHom)))

/-- Finite free coefficients commute with cohomology of the Kummer root sheaf.
Source: blueprint lem-pur-kummer-coefficient-base-change, steps 1--3; Stacks Tag 015B.
Proof: choose a finite basis b_j of A. On the sheafified tensor define projections
p_j(z tensor a) = lambda_j(a) z. The insertion and projection maps have composites
p_j i_h = delta_jh and sum i_j p_j = id, including for the empty basis. Additivity
of cohomology gives the same identities in degree q. The bilinear map
(x,a) maps to H(i_a)(x) therefore induces beta; its inverse sends y to
sum H(p_j)(y) tensor b_j. The two identities show both composites are identities.
All additive maps of modules over ULift(ZMod m) are linear, because every scalar
is an integer scalar. The pure-tensor formula is independent of the chosen basis.
(blueprint: lem-pur-kummer-finite-free-comparison). -/
theorem kummer_finite_free_comparison (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    [Module.Free (ULift.{u + 1} (ZMod m)) A]
    [Module.Finite (ULift.{u + 1} (ZMod m)) A] :
    ∃ beta : ∀ q : ℕ,
      (Sheaf.H (C.rootsOfUnitySheaf m) q ⊗[ULift.{u + 1} (ZMod m)] A) ≃ₗ[
        ULift.{u + 1} (ZMod m)] Sheaf.H ((kummerAbelianTwist C m).obj A) q,
      ∀ (q : ℕ) (x : Sheaf.H (C.rootsOfUnitySheaf m) q) (a : A),
        beta q (x ⊗ₜ a) = Sheaf.H.map (kummerCoefficientInsertion C m A a) q x  := by
  classical
  let R := ULift.{u + 1} (ZMod m)
  let b := Module.Free.chooseBasis R A
  let ι := Module.Free.ChooseBasisIndex R A
  let : Fintype ι := Fintype.ofFinite ι
  let forgetM := sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat)
  let i (a : A) := kummerCoefficientInsertion C m A a
  let p (j : ι) : (kummerAbelianTwist C m).obj A ⟶ C.rootsOfUnitySheaf m :=
    forgetM.map (rootCoordinate C m A (b.coord j))
  let pair (q : ℕ) : A →ₗ[R]
      (Sheaf.H (C.rootsOfUnitySheaf m) q →ₗ[R]
        Sheaf.H ((kummerAbelianTwist C m).obj A) q) :=
    { toFun := fun a ↦ residueLinear (cohomologyModuleHom C m q A
        (insertionLinear C m A a))
      map_add' := by
        intro a a'
        ext x
        change cohomologyModuleHom C m q A (insertionLinear C m A (a + a')) x = _
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro t a
        ext x
        change cohomologyModuleHom C m q A (insertionLinear C m A (t • a)) x = _
        rw [map_smul, map_smul]
        rfl }
  let T (q : ℕ) := TensorProduct.lift (pair q).flip
  have hT (q : ℕ) (x : Sheaf.H (C.rootsOfUnitySheaf m) q) (a : A) :
      T q (x ⊗ₜ a) = Sheaf.H.map (i a) q x := rfl
  let S (q : ℕ) : Sheaf.H ((kummerAbelianTwist C m).obj A) q →ₗ[R]
      (Sheaf.H (C.rootsOfUnitySheaf m) q ⊗[R] A) :=
    ∑ j : ι, (TensorProduct.mk R (Sheaf.H (C.rootsOfUnitySheaf m) q) A).flip (b j) ∘ₗ
      residueLinear (Sheaf.H.map (p j) q)
  have hpi (q : ℕ) (j : ι) (x : Sheaf.H (C.rootsOfUnitySheaf m) q) (a : A) :
      Sheaf.H.map (p j) q (Sheaf.H.map (i a) q x) = b.coord j a • x := by
    rw [← Sheaf.H.map_comp_apply]
    change Sheaf.H.map (forgetM.map (rootModuleInsertion C m A a) ≫
      forgetM.map (rootCoordinate C m A (b.coord j))) q x = _
    rw [← forgetM.map_comp, rootCoordinate_insertion]
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective (b.coord j a).down
    have ht : (n : R) = b.coord j a := ULift.ext _ _ hn
    rw [← ht, Int.cast_smul_eq_zsmul, CategoryTheory.Functor.map_zsmul,
      CategoryTheory.Functor.map_id]
    change Sheaf.H.map (n • 𝟙 (C.rootsOfUnitySheaf m)) q x = (n : R) • x
    rw [Int.cast_smul_eq_zsmul]
    rw [cohomology_map_zsmul, Sheaf.H.map_id_apply]
  have hST (q : ℕ) : S q ∘ₗ T q = LinearMap.id := by
    apply TensorProduct.ext'
    intro x a
    change S q (T q (x ⊗ₜ a)) = x ⊗ₜ a
    rw [hT]
    simp only [S, LinearMap.sum_apply, LinearMap.comp_apply,
      TensorProduct.mk_apply, LinearMap.flip_apply]
    change (∑ j : ι, Sheaf.H.map (p j) q (Sheaf.H.map (i a) q x) ⊗ₜ b j) = _
    simp_rw [hpi, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum]
    exact congrArg (fun a ↦ x ⊗ₜ[R] a) (b.sum_repr a)
  have hTS (q : ℕ) : T q ∘ₗ S q = LinearMap.id := by
    ext y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, S, LinearMap.sum_apply,
      TensorProduct.mk_apply, LinearMap.flip_apply]
    change T q (∑ j : ι, Sheaf.H.map (p j) q y ⊗ₜ b j) = y
    rw [map_sum]
    simp_rw [hT, ← Sheaf.H.map_comp_apply]
    have htotal : (∑ j : ι, p j ≫ i (b j)) = 𝟙 _ := by
      change (∑ j : ι, forgetM.map (rootCoordinate C m A (b.coord j)) ≫
        forgetM.map (rootModuleInsertion C m A (b j))) = _
      simp_rw [← forgetM.map_comp]
      rw [← CategoryTheory.Functor.map_sum,
        rootCoordinate_total C m A b (fun j ↦ b.coord j) (fun a ↦ b.sum_repr a)]
      exact forgetM.map_id _
    rw [← cohomology_map_sum, htotal]
    exact Sheaf.H.map_id_apply _
  exact ⟨fun q ↦ LinearEquiv.ofLinearMap (T q) (S q) (hTS q) (hST q), hT⟩

end AlgebraicGeometry.Scheme
