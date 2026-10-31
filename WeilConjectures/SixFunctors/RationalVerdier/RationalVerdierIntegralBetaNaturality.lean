/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality

/-! # Naturality of the integral beta comparison after localization

Source: blueprint thm-coef-rational-verdier, proof, paragraph 3
(blueprint: lem-coef-rational-verdier-integral-beta-naturality).

The integral case is the transpose calculation for the finite coefficient
comparison.  It is isolated from the rational tensor extension so that the
remaining argument only uses tensor-product induction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

private theorem uncurry_source {C : Type*} [Category* C]
    (T : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (adj : ∀ K, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (he : ∀ K K' W (f : K' ⟶ K),
      T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
        (adj K').counit.app W =
      T.map (Prod.mkHom f (𝟙 _)) ≫ (adj K).counit.app W)
    {K K' V W : C} (f : K' ⟶ K) (q : V ⟶ H.obj (op K, W)) :
    ((adj K').homEquiv V W).symm (q ≫ H.map (Prod.mkHom f.op (𝟙 W))) =
      T.map (Prod.mkHom f (𝟙 V)) ≫ ((adj K).homEquiv V W).symm q := by
  simp only [Adjunction.homEquiv_counit]
  change T.map (Prod.mkHom (𝟙 K') (q ≫ H.map (Prod.mkHom f.op (𝟙 W)))) ≫
    (adj K').counit.app W =
    T.map (Prod.mkHom f (𝟙 V)) ≫
      T.map (Prod.mkHom (𝟙 K) q) ≫ (adj K).counit.app W
  have h₁ : Prod.mkHom (𝟙 K') (q ≫ H.map (Prod.mkHom f.op (𝟙 W))) =
      Prod.mkHom (𝟙 K') q ≫ Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 W))) := by
    simp
  rw [h₁, T.map_comp, Category.assoc, he, ← Category.assoc, ← T.map_comp,
    ← Category.assoc, ← T.map_comp]
  congr 2
  simp

private theorem hom_comparison_natural {C : Type*} [Category* C]
    {C' : Type*} [Category* C']
    (T : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (T' : C' × C' ⥤ C') (H' : C'ᵒᵖ × C' ⥤ C')
    (adj : ∀ K, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (adj' : ∀ K, (Functor.curry.obj T').obj K ⊣ (Functor.curry.obj H').obj (op K))
    (he : ∀ K K' W (f : K' ⟶ K),
      T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
        (adj K').counit.app W =
      T.map (Prod.mkHom f (𝟙 _)) ≫ (adj K).counit.app W)
    (he' : ∀ K K' W (f : K' ⟶ K),
      T'.map (Prod.mkHom (𝟙 K') (H'.map (Prod.mkHom f.op (𝟙 W)))) ≫
        (adj' K').counit.app W =
      T'.map (Prod.mkHom f (𝟙 _)) ≫ (adj' K).counit.app W)
    (F : C ⥤ C') (mu : T ⋙ F ≅ F.prod F ⋙ T')
    {K K' W : C} (f : K' ⟶ K) :
    F.map (H.map (Prod.mkHom f.op (𝟙 W))) ≫
        (adj' (F.obj K')).homEquiv _ _
          (mu.inv.app (K', H.obj (op K', W)) ≫ F.map ((adj K').counit.app W)) =
      (adj' (F.obj K)).homEquiv _ _
          (mu.inv.app (K, H.obj (op K, W)) ≫ F.map ((adj K).counit.app W)) ≫
        H'.map (Prod.mkHom (F.map f).op (𝟙 (F.obj W))) := by
  apply ((adj' (F.obj K')).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hs := uncurry_source T' H' adj' he' (W := F.obj W) (F.map f)
    ((adj' (F.obj K)).homEquiv _ _
      (mu.inv.app (K, H.obj (op K, W)) ≫ F.map ((adj K).counit.app W)))
  simp only [Equiv.symm_apply_apply] at hs
  refine Eq.trans ?_ hs.symm
  have hn₁ := mu.inv.naturality
    (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 W))))
  have hn₂ := mu.inv.naturality (Prod.mkHom f (𝟙 (H.obj (op K, W))))
  change T'.map (Prod.mkHom (F.map (𝟙 K'))
      (F.map (H.map (Prod.mkHom f.op (𝟙 W))))) ≫
      mu.inv.app (K', H.obj (op K', W)) =
    mu.inv.app (K', H.obj (op K, W)) ≫
      F.map (T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 W))))) at hn₁
  change T'.map (Prod.mkHom (F.map f) (F.map (𝟙 (H.obj (op K, W))))) ≫
      mu.inv.app (K, H.obj (op K, W)) =
    mu.inv.app (K', H.obj (op K, W)) ≫
      F.map (T.map (Prod.mkHom f (𝟙 (H.obj (op K, W))))) at hn₂
  rw [F.map_id] at hn₁ hn₂
  change T'.map (Prod.mkHom (𝟙 (F.obj K'))
      (F.map (H.map (Prod.mkHom f.op (𝟙 W))))) ≫ _ = _
  rw [← Category.assoc, hn₁, Category.assoc, ← F.map_comp, he, F.map_comp]
  have h := congrArg (fun q ↦ q ≫ F.map ((adj K).counit.app W)) hn₂.symm
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.curry_obj_obj_obj] at h ⊢
  simpa only [Category.assoc] using h

private theorem inverse_square {C : Type*} [Category* C] {U V U' V' : C}
    (a : U ≅ U') (b : V ≅ V') (f : U ⟶ V) (g : U' ⟶ V')
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).1
  calc
    a.hom ≫ g ≫ b.inv = (f ≫ b.hom) ≫ b.inv := by rw [h, Category.assoc]
    _ = f := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = a.hom ≫ a.inv ≫ f := by rw [Iso.hom_inv_id_assoc]

attribute [local irreducible] derivedInternalHomOfUniverses homComplexFunctor
  IntegralHom.totalTensor IntegralHom.homModelMap IntegralHom.projection IntegralHom.evaluate

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem v_natural
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (K K' W : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hK' : IsSfDerivedComplete l E X K')
    (hW : IsSfDerivedComplete l E X W) (f : K' ⟶ K) :
    (integralScalarExtensionOfUniverses l E L i X).map
        ((IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)).map
          (Prod.mkHom f.op (𝟙 W))) ≫
      IntegralFiniteExtension.v l E L i X a b K' W hK' hW =
    IntegralFiniteExtension.v l E L i X a b K W hK hW ≫
      (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).map
        (Prod.mkHom ((integralScalarExtensionOfUniverses l E L i X).map f).op (𝟙 _)) := by
  let F := pbcDerivedExtend (completedCoefficientMap l E L i X)
  let T := integralScalarExtensionOfUniverses l E L i X
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let H' := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
  let cK := IntegralFiniteExtension.completion l E L i X K hK
  let cK' := IntegralFiniteExtension.completion l E L i X K' hK'
  let cW := IntegralFiniteExtension.completion l E L i X W hW
  let cH := IntegralFiniteExtension.completion l E L i X (H.obj (op K, W))
    (scalarInternalHom_complete l E X K W hW)
  let cH' := IntegralFiniteExtension.completion l E L i X (H.obj (op K', W))
    (scalarInternalHom_complete l E X K' W hW)
  have hKnat : F.map f ≫ cK.hom = cK'.hom ≫ T.map f :=
    (completedScalarComparison l E L i X).naturality f
  have hHnat : F.map (H.map (Prod.mkHom f.op (𝟙 W))) ≫ cH'.hom =
      cH.hom ≫ T.map (H.map (Prod.mkHom f.op (𝟙 W))) :=
    (completedScalarComparison l E L i X).naturality _
  have h₀ : F.map (H.map (Prod.mkHom f.op (𝟙 W))) ≫
      IntegralFiniteExtension.homMap X (completedCoefficientMap l E L i X) a b K' W =
    IntegralFiniteExtension.homMap X (completedCoefficientMap l E L i X) a b K W ≫
      H'.map (Prod.mkHom (F.map f).op (𝟙 (F.obj W))) :=
    hom_comparison_natural a.tensor H b.tensor H' a.adjunction b.adjunction
      (IntegralHom.evaluation_naturality X _ a)
      (IntegralHom.evaluation_naturality X _ b) F
      (PurCompactSupport.scalarTensor (completedCoefficientMap l E L i X)
        (IntegralFiniteExtension.tensorModel X a) (IntegralFiniteExtension.tensorModel X b)) f
  have h₁ : H'.map (Prod.mkHom (F.map f).op (𝟙 (F.obj W))) ≫
      H'.map (Prod.mkHom cK'.inv.op cW.hom) =
    H'.map (Prod.mkHom cK.inv.op cW.hom) ≫
      H'.map (Prod.mkHom (T.map f).op (𝟙 (T.obj W))) := by
    rw [← H'.map_comp, ← H'.map_comp]
    congr 1
    ext
    · change (F.map f).op ≫ cK'.inv.op = cK.inv.op ≫ (T.map f).op
      rw [← op_comp, ← op_comp]
      exact congrArg Quiver.Hom.op (inverse_square cK' cK _ _ hKnat).symm
    · change 𝟙 (F.obj W) ≫ cW.hom = cW.hom ≫ 𝟙 (T.obj W)
      rw [Category.id_comp, Category.comp_id]
  change T.map (H.map (Prod.mkHom f.op (𝟙 W))) ≫
      (cH'.inv ≫ IntegralFiniteExtension.homMap X (completedCoefficientMap l E L i X)
        a b K' W ≫ H'.map (Prod.mkHom cK'.inv.op cW.hom)) =
    (cH.inv ≫ IntegralFiniteExtension.homMap X (completedCoefficientMap l E L i X)
      a b K W ≫ H'.map (Prod.mkHom cK.inv.op cW.hom)) ≫ _
  rw [← Category.assoc, inverse_square cH cH' _ _ hHnat, Category.assoc,
    ← Category.assoc (F.map (H.map (Prod.mkHom f.op (𝟙 W)))), h₀]
  simpa only [Category.assoc] using congrArg
    (fun q ↦ cH.inv ≫ IntegralFiniteExtension.homMap X
      (completedCoefficientMap l E L i X) a b K W ≫ q) h₁

private theorem beta_natural
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (K M : sfIntegralConstructibleCategory l E X) (f : K ⟶ M) :
    (integralScalar l X E L i).map
        ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).map f.op) ≫
      ObjectProperty.homMk (X := (integralScalar l X E L i).obj
        ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op K)))
        (Y := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj
          (op ((integralScalar l X E L i).obj K)))
        (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
          K.obj K.property.1) =
    ObjectProperty.homMk (X := (integralScalar l X E L i).obj
        ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op M)))
        (Y := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj
          (op ((integralScalar l X E L i).obj M)))
        (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
          M.obj M.property.1) ≫
      (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).map
        ((integralScalar l X E L i).map f).op := by
  apply ObjectProperty.hom_ext
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let H' := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
  let T := integralScalarExtensionOfUniverses l E L i X
  let vK := IntegralFiniteExtension.v l E L i X A.ordinary B.ordinary
    K.obj wE.omega.obj K.property.1 wE.omega.property.1
  let vM := IntegralFiniteExtension.v l E L i X A.ordinary B.ordinary
    M.obj wE.omega.obj M.property.1 wE.omega.property.1
  let u := IntegralFiniteExtension.u l E L i X D hl wE wL
  change T.map (H.map (Prod.mkHom f.hom.op (𝟙 wE.omega.obj))) ≫
      (vK ≫ H'.map (Prod.mkHom (𝟙 _) u)) =
    (vM ≫ H'.map (Prod.mkHom (𝟙 _) u)) ≫
      H'.map (Prod.mkHom (T.map f.hom).op (𝟙 wL.omega.obj))
  rw [← Category.assoc, v_natural l X E L i A.ordinary B.ordinary
    M.obj K.obj wE.omega.obj M.property.1 K.property.1 wE.omega.property.1 f.hom]
  simp only [Category.assoc]
  congr 1
  rw [← H'.map_comp, ← H'.map_comp]
  congr 1
  ext
  · change (T.map f.hom).op ≫ 𝟙 (op (T.obj K.obj)) =
      𝟙 (op (T.obj M.obj)) ≫ (T.map f.hom).op
    rw [Category.comp_id, Category.id_comp]
  · change 𝟙 (T.obj wE.omega.obj) ≫ u = u ≫ 𝟙 wL.omega.obj
    rw [Category.comp_id, Category.id_comp]

private theorem map_heq {C : Type*} [Category* C] {C' : Type*} [Category* C']
    (F : C ⥤ C') {K M K' M' : C} (hK : K = K') (hM : M = M')
    {f : K ⟶ M} {g : K' ⟶ M'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hK; cases hM; cases h
  rfl

private theorem op_heq {C : Type*} [Category* C] {K M K' M' : C}
    (hK : K = K') (hM : M = M') {f : K ⟶ M} {g : K' ⟶ M'}
    (h : HEq f g) : HEq f.op g.op := by
  cases hK; cases hM; cases h
  rfl

/-- The localized integral beta comparison is natural on integral arrows.
Source: blueprint thm-coef-rational-verdier.proof.md, paragraph 3, the
integral-arrow transpose calculation (blueprint:
lem-coef-rational-verdier-integral-beta-naturality).

Proof: expand `beta` as the evaluation transpose followed by the canonical
dualizing map.  Naturality of the tensor-Hom adjunction in its first argument,
the scalar tensorator formula on pure tensors, and naturality of the internal
Hom map identify the two transposes.  The localized map preserves this
identity.  The statement is strictly the integral-arrow subcase; tensor
product induction and the supplied-family transport are handled by its caller.
-/
theorem integralBeta_naturality
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (c : ∀ K : sfRationalConstructibleCategory l E X,
      (scalar l X E L i).obj (A.dual.obj (op K)) ⟶
        B.dual.obj (op ((scalar l X E L i).obj K)))
    (hc : (∀ K : sfIntegralConstructibleCategory l E X,
    HEq (c ((sfRationalConstructibleLocalization l E X).obj K))
      ((sfRationalConstructibleLocalization l L X).map
        (ObjectProperty.homMk
          (X := (integralScalar l X E L i).obj
            ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op K)))
          (Y := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj
            (op ((integralScalar l X E L i).obj K)))
          (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
            K.obj K.property.1)))))
    (K M : sfIntegralConstructibleCategory l E X)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
    (f : K ⟶ M) :
    (A.dual ⋙ scalar l X E L i).map
        (Quiver.Hom.op (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E X).obj K ⟶
            (sfRationalConstructibleLocalization l E X).obj M)) ≫
      c ((sfRationalConstructibleLocalization l E X).obj K) =
      c ((sfRationalConstructibleLocalization l E X).obj M) ≫
        ((scalar l X E L i).op ⋙ B.dual).map
          (Quiver.Hom.op (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
            (sfRationalConstructibleLocalization l E X).obj K ⟶
              (sfRationalConstructibleLocalization l E X).obj M)) := by
  let T := integralScalar l X E L i
  let R := scalar l X E L i
  let Q := sfRationalConstructibleLocalization l L X
  let QE := sfRationalConstructibleLocalization l E X
  let DE := IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves
  let DL := IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves
  let z := (sfRationalCoefficientEquiv l L).symm (i (sfRationalCoefficientEquiv l E a))
  let beta (N : sfIntegralConstructibleCategory l E X) :
      T.obj (DE.obj (op N)) ⟶ DL.obj (op (T.obj N)) :=
    ObjectProperty.homMk
      (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
        N.obj N.property.1)
  have hR (N : sfRationalConstructibleCategory l E X) :
      R.obj N = Q.obj (T.obj N.obj) :=
    sfRationalScalarExtension_obj l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i N
  have hsource (N : sfIntegralConstructibleCategory l E X) :
      R.obj (A.dual.obj (op (QE.obj N))) = Q.obj (T.obj (DE.obj (op N))) := by
    rw [A.objects (QE.obj N)]
    exact hR _
  have htarget (N : sfIntegralConstructibleCategory l E X) :
      B.dual.obj (op (R.obj (QE.obj N))) = Q.obj (DL.obj (op (T.obj N))) := by
    rw [hR (QE.obj N)]
    exact B.objects _
  have hleft : HEq ((A.dual ⋙ R).map
      (Quiver.Hom.op (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
        QE.obj K ⟶ QE.obj M)))
      (z ⊗ₜ[Padic.coefficientExtensionIntegers l L] T.map (DE.map f.op) :
        Q.obj (T.obj (DE.obj (op M))) ⟶ Q.obj (T.obj (DE.obj (op K)))) :=
    (map_heq R (A.objects (QE.obj M)) (A.objects (QE.obj K)) (A.pure K M f a)).trans
      (sfRationalScalarExtension_map_tmul l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i _ _ (DE.map f.op) a)
  have hscalar := sfRationalScalarExtension_map_tmul l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i K M f a
  have hright : HEq ((R.op ⋙ B.dual).map
      (Quiver.Hom.op (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
        QE.obj K ⟶ QE.obj M)))
      (z ⊗ₜ[Padic.coefficientExtensionIntegers l L] DL.map (T.map f).op :
        Q.obj (DL.obj (op (T.obj M))) ⟶ Q.obj (DL.obj (op (T.obj K)))) :=
    (map_heq B.dual (congrArg op (hR (QE.obj M))) (congrArg op (hR (QE.obj K)))
      (op_heq (hR (QE.obj K)) (hR (QE.obj M)) hscalar)).trans
        (B.pure (T.obj K) (T.obj M) (T.map f) z)
  have h₁ := heq_comp (hsource M) (hsource K) (htarget K) hleft (hc K)
  have h₂ := heq_comp (hsource M) (htarget M) (htarget K) (hc M) hright
  apply eq_of_heq
  refine h₁.trans (HEq.trans ?_ h₂.symm)
  apply heq_of_eq
  change ScalarLocalization.composition _ _ _ _ _ _
      (1 ⊗ₜ[Padic.coefficientExtensionIntegers l L] beta K)
      (z ⊗ₜ[Padic.coefficientExtensionIntegers l L] T.map (DE.map f.op)) =
    ScalarLocalization.composition _ _ _ _ _ _
      (z ⊗ₜ[Padic.coefficientExtensionIntegers l L] DL.map (T.map f).op)
      (1 ⊗ₜ[Padic.coefficientExtensionIntegers l L] beta M)
  simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
  exact congrArg (fun q ↦ z ⊗ₜ[Padic.coefficientExtensionIntegers l L] q)
    (beta_natural D l hl X E L i wE wL A B K M f)

end WeilConjectures.RationalVerdier
