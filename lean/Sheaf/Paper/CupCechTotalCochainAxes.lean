module
public import Sheaf.Paper.CupCechPairCochain
public import Sheaf.Paper.CupCechTotalComplex
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 600000 in
-- The beta calculation elaborates several nested sheaf-to-section coercions.
/-- The normalized total Alexander--Whitney map has the alpha and beta axis formulas.
Source: Stacks Project, equation 07MB and the flasque diagram in Lemma 0FKV.
(blueprint: new-cup-cech-total-cochain-axes)

Proof: unfold cupCechAlpha into restrictions followed by the (p,0) inclusion.
Apply the assumed formula with r=p, s=q, i=j=0. The Koszul sign is one.
Evaluate the row pairing at each singleton tuple. Both front and back faces
are that same singleton, so D.restriction identifies their pairing with the
restriction of the global value D.pair p q top a b. Equality at all tuples is
equality of row cochains; applying the target inclusion gives the alpha axis.
For beta, unfold cupCechBeta into the augmentation followed by the (0,p)
inclusion. Apply the assumed formula with r=s=0, i=p, j=q; its sign is one.
At each tuple, naturality of the two augmentation morphisms moves them past
the front and back restriction maps. D.augmentation_pair identifies the
resulting local pair with augmentation of tmulSection. This is exactly the
tuple defining cechCupCochain. The target augmentation followed by its row
inclusion is cupCechBeta, giving the beta axis. These tuplewise arguments also
cover repeated indices, degree zero, and empty index types. -/
theorem cupCech_total_cochain_axes {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (h : HomologicalComplex.mapBifunctor
      ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
      (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ) ⟶
      ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)))
    (hh : ∀ (r s i j m n : ℕ) (hm : r + i = m) (hn : s + j = n)
      (a : ((cupCechDouble U D.left.K).X r).X i)
      (b : ((cupCechDouble U D.right.K).X s).X j),
      h.f (m + n)
        (HomologicalComplex.ιMapBifunctor
          ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
          ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
          (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ)
          m n (m + n) rfl
          (((cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ)
              r i m (by simpa using hm) a) ⊗ₜ[Γ(X, ⊤)]
            ((cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ)
              s j n (by simpa using hn) b))) =
        (-1 : ℤ) ^ (i * s) •
          (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ)
            (r + s) (i + j) (m + n) (by dsimp; omega)
            (cupCechPairCochain U D r s i j a b)) :
      (∀ (p q : ℕ) (a : (cupSections D.left).X p) (b : (cupSections D.right).X q),
        h.f (p + q)
          (HomologicalComplex.ιMapBifunctor
            ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
            ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
            (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ)
            p q (p + q) rfl
            (((cupCechAlpha U D.left).f p a) ⊗ₜ[Γ(X, ⊤)]
              ((cupCechAlpha U D.right).f q b))) =
        (cupCechAlpha U D.target).f (p + q) (D.pair p q ⊤ a b)) ∧
      (∀ (p q : ℕ)
        (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
        (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q),
        h.f (p + q)
          (HomologicalComplex.ιMapBifunctor
            ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
            ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
            (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ)
            p q (p + q) rfl
            (((cupCechBeta U D.left).f p a) ⊗ₜ[Γ(X, ⊤)]
              ((cupCechBeta U D.right).f q b))) =
        (cupCechBeta U D.target).f (p + q) (cechCupCochain U F G p q a b)) := by
  have zero_apply (H : X.Modules)
      (a : (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj H)
      (y : Fin 1 → ι) :
      TopCat.Presheaf.cechComplexFunctorXAddEquiv U H.presheafModuleCat 0
        (moduleCechZero U H a) y =
      H.presheaf.map (homOfLE (le_top (a := ⨅ k, U (y k)))).op a := by
    rw [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply]
    have hπ : TopCat.Presheaf.cechComplexFunctorπ U H.presheafModuleCat 0 y
        (moduleCechZero U H a) =
      H.presheaf.map (homOfLE (le_top (a := ∏ᶜ fun k ↦ U (y k)))).op a := by
      change (moduleCechZero U H ≫
        TopCat.Presheaf.cechComplexFunctorπ U H.presheafModuleCat 0 y) a = _
      dsimp only [moduleCechZero, TopCat.Presheaf.cechComplexFunctorπ]
      rw [Category.assoc]
      erw [Pi.lift_π]
      rfl
    rw [hπ]
    exact TopCat.Presheaf.map_homOfLE_map_homOfLE_apply H.presheaf _ _ _
  have coefficient_apply {H H' : X.Modules} (φ : H ⟶ H') (n : ℕ)
      (a : ((cechComplexFunctor U).obj H.presheafModuleCat).X n)
      (y : Fin (n + 1) → ι) :
      TopCat.Presheaf.cechComplexFunctorXAddEquiv U H'.presheafModuleCat n
        (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            φ.val)).f n a) y =
      φ.val.app (op (⨅ j, U (y j)))
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U H.presheafModuleCat n a y) := by
    let ψ := (PresheafOfModules.forgetToPresheafModuleCat
      (op ⊤) isTerminalTop.op).map φ.val
    have hπ := TopCat.Presheaf.cechComplexFunctor_map_f_π U H.presheafModuleCat ψ n y
    have hπa := congrArg (fun k ↦ k a) hπ
    change TopCat.Presheaf.cechComplexFunctorπ U H'.presheafModuleCat n y
      (((cechComplexFunctor U).map ψ).f n a) =
      ψ.app _ (TopCat.Presheaf.cechComplexFunctorπ U H.presheafModuleCat n y a) at hπa
    change H'.presheaf.map _
      (TopCat.Presheaf.cechComplexFunctorπ U H'.presheafModuleCat n y
        (((cechComplexFunctor U).map ψ).f n a)) = _
    rw [hπa]
    exact (Hom.app_presheaf_map φ (homOfLE (TopCat.Presheaf.iInf_le_piObj U y))
      (TopCat.Presheaf.cechComplexFunctorπ U H.presheafModuleCat n y a)).symm
  constructor
  · intro p q a b
    have hf := hh p q 0 0 p q (by simp) (by simp) (moduleCechZero U (D.left.K.X p) a)
      (moduleCechZero U (D.right.K.X q) b)
    simp only [Nat.zero_mul, pow_zero, one_smul] at hf
    change _ = (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ)
      (p + q) 0 (p + q) (by simp) (moduleCechZero U (D.target.K.X (p + q))
        (D.pair p q ⊤ a b))
    rw [show (cupCechAlpha U D.left).f p a =
        (cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) p 0 p (by simp)
          (moduleCechZero U (D.left.K.X p) a) from rfl,
      show (cupCechAlpha U D.right).f q b =
        (cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) q 0 q (by simp)
          (moduleCechZero U (D.right.K.X q) b) from rfl, hf]
    congr 1
    apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
      (D.target.K.X (p + q)).presheafModuleCat 0).injective
    funext y
    simp only [cupCechPairCochain, AddEquiv.apply_symm_apply]
    rw [zero_apply, zero_apply, zero_apply]
    dsimp only [cupFaceRestriction]
    erw [TopCat.Presheaf.map_homOfLE_map_homOfLE_apply,
      TopCat.Presheaf.map_homOfLE_map_homOfLE_apply]
    exact (D.restriction p q ⊤ _ le_top a b).symm
  · intro p q a b
    let a' : ((cupCechDouble U D.left.K).X 0).X p := ((cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (D.left.augmentation.f 0).val)).f p a
    let b' : ((cupCechDouble U D.right.K).X 0).X q := ((cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (D.right.augmentation.f 0).val)).f q b
    have hf := hh 0 0 p q p q (by simp) (by simp) a' b'
    simp only [Nat.mul_zero, pow_zero, one_smul] at hf
    change h.f (p + q)
      (HomologicalComplex.ιMapBifunctor
        ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
        ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
        (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ) p q (p + q) rfl
        (((cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) 0 p p (by simp) a')
          ⊗ₜ[Γ(X, ⊤)]
          ((cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) 0 q q (by simp) b'))) =
      (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ) 0 (p + q) (p + q)
        (by simp) (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.target.augmentation.f 0).val)).f (p + q) (cechCupCochain U F G p q a b))
    erw [hf]
    congr 1
    apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
      (D.target.K.X 0).presheafModuleCat (p + q)).injective
    funext y
    simp only [cupCechPairCochain, AddEquiv.apply_symm_apply]
    dsimp only [a', b']
    rw [coefficient_apply, coefficient_apply, coefficient_apply]
    erw [← Hom.app_presheaf_map (D.left.augmentation.f 0)
      (cupFaceRestriction U y (cupFront p q)) _,
      ← Hom.app_presheaf_map (D.right.augmentation.f 0)
        (cupFaceRestriction U y (cupBack p q)) _, D.augmentation_pair]
    change _ = (D.target.augmentation.f 0).val.app (op (⨅ k, U (y k)))
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (F ⊗ G).presheafModuleCat (p + q)
        (cechCupCochain U F G p q a b) y)
    simp only [cechCupCochain, AddEquiv.apply_symm_apply]
    rfl


end
end AlgebraicGeometry.Scheme.Modules
