/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierScalarInterchange

/-! # Biduality follows from the scalar evaluation square

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-comparison-biduality). -/

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

private theorem tensor_map_comp {C : Type*} [Category* C] (T : C × C ⥤ C)
    (K : C) {M N P : C} (f : M ⟶ N) (g : N ⟶ P) :
    T.map (Prod.mkHom (𝟙 K) (f ≫ g)) =
      T.map (Prod.mkHom (𝟙 K) f) ≫ T.map (Prod.mkHom (𝟙 K) g) := by
  rw [← T.map_comp]
  congr 1
  ext <;> simp

private theorem tensor_map_exchange {C : Type*} [Category* C] (T : C × C ⥤ C)
    {K K' M M' : C} (f : K ⟶ K') (g : M ⟶ M') :
    T.map (Prod.mkHom (𝟙 K) g) ≫ T.map (Prod.mkHom f (𝟙 M')) =
      T.map (Prod.mkHom f (𝟙 M)) ≫ T.map (Prod.mkHom (𝟙 K') g) := by
  rw [← T.map_comp, ← T.map_comp]
  simp

private theorem evaluation_bidual
    {C C' : Type*} [Category* C] [Category* C']
    (T : C × C ⥤ C) (T' : C' × C' ⥤ C') (F : C ⥤ C')
    (DA : Cᵒᵖ ⥤ C) (DB : C'ᵒᵖ ⥤ C') (W : C) (W' : C')
    (ev : ∀ K : C, T.obj (K, DA.obj (op K)) ⟶ W)
    (ev' : ∀ K : C', T'.obj (K, DB.obj (op K)) ⟶ W')
    (delta : ∀ K : C, K ⟶ DA.obj (op (DA.obj (op K))))
    (delta' : ∀ K : C', K ⟶ DB.obj (op (DB.obj (op K))))
    (s : ∀ K M : C, T.obj (K, M) ⟶ T.obj (M, K))
    (s' : ∀ K M : C', T'.obj (K, M) ⟶ T'.obj (M, K))
    (mu : T ⋙ F ≅ F.prod F ⋙ T') (w : F.obj W ⟶ W')
    (beta : ∀ K : C, F.obj (DA.obj (op K)) ⟶ DB.obj (op (F.obj K)))
    (hdelta : ∀ K, T.map (Prod.mkHom (𝟙 (DA.obj (op K))) (delta K)) ≫
      ev (DA.obj (op K)) = s (DA.obj (op K)) K ≫ ev K)
    (hdelta' : ∀ K, T'.map (Prod.mkHom (𝟙 (DB.obj (op K))) (delta' K)) ≫
      ev' (DB.obj (op K)) = s' (DB.obj (op K)) K ≫ ev' K)
    (hnat : ∀ (K M K' M' : C') (f : K ⟶ K') (g : M ⟶ M'),
      T'.map (Prod.mkHom f g) ≫ s' K' M' =
        s' K M ≫ T'.map (Prod.mkHom g f))
    (hevnat : ∀ (K M : C') (f : K ⟶ M),
      T'.map (Prod.mkHom f (𝟙 (DB.obj (op M)))) ≫ ev' M =
        T'.map (Prod.mkHom (𝟙 K) (DB.map f.op)) ≫ ev' K)
    (hdetect : ∀ (K V : C') (f g : V ⟶ DB.obj (op K)),
      T'.map (Prod.mkHom (𝟙 K) f) ≫ ev' K =
        T'.map (Prod.mkHom (𝟙 K) g) ≫ ev' K → f = g)
    (hs : ∀ K M, s' (F.obj K) (F.obj M) ≫ mu.inv.app (M, K) =
      mu.inv.app (K, M) ≫ F.map (s K M))
    (heval : ∀ K, T'.map (Prod.mkHom (𝟙 (F.obj K)) (beta K)) ≫ ev' (F.obj K) =
      mu.inv.app (K, DA.obj (op K)) ≫ F.map (ev K) ≫ w) (K : C) :
    F.map (delta K) ≫ beta (DA.obj (op K)) =
      delta' (F.obj K) ≫ DB.map (beta K).op := by
  apply hdetect (F.obj (DA.obj (op K))) (F.obj K)
  have hmu := mu.inv.naturality (Prod.mkHom (𝟙 (DA.obj (op K))) (delta K))
  change T'.map (Prod.mkHom (F.map (𝟙 (DA.obj (op K)))) (F.map (delta K))) ≫
      mu.inv.app (DA.obj (op K), DA.obj (op (DA.obj (op K)))) =
    mu.inv.app (DA.obj (op K), K) ≫
      F.map (T.map (Prod.mkHom (𝟙 (DA.obj (op K))) (delta K))) at hmu
  rw [F.map_id] at hmu
  calc
    _ = T'.map (Prod.mkHom (𝟙 (F.obj (DA.obj (op K)))) (F.map (delta K))) ≫
        mu.inv.app (DA.obj (op K), DA.obj (op (DA.obj (op K)))) ≫
          F.map (ev (DA.obj (op K))) ≫ w := by
      rw [tensor_map_comp, Category.assoc, heval]
    _ = mu.inv.app (DA.obj (op K), K) ≫
        F.map (T.map (Prod.mkHom (𝟙 (DA.obj (op K))) (delta K)) ≫
          ev (DA.obj (op K))) ≫ w := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun q ↦ q ≫ F.map (ev (DA.obj (op K))) ≫ w) hmu
    _ = mu.inv.app (DA.obj (op K), K) ≫ F.map (s (DA.obj (op K)) K) ≫
        F.map (ev K) ≫ w := by
      simp only [hdelta, Functor.map_comp, Category.assoc]
    _ = s' (F.obj (DA.obj (op K))) (F.obj K) ≫
        T'.map (Prod.mkHom (𝟙 (F.obj K)) (beta K)) ≫ ev' (F.obj K) := by
      rw [heval]
      simpa only [Category.assoc] using
        congrArg (fun q ↦ q ≫ F.map (ev K) ≫ w) (hs (DA.obj (op K)) K).symm
    _ = T'.map (Prod.mkHom (beta K) (𝟙 (F.obj K))) ≫
        s' (DB.obj (op (F.obj K))) (F.obj K) ≫ ev' (F.obj K) := by
      simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ ev' (F.obj K))
        (hnat _ _ _ _ (beta K) (𝟙 (F.obj K))).symm
    _ = T'.map (Prod.mkHom (beta K) (𝟙 (F.obj K))) ≫
        T'.map (Prod.mkHom (𝟙 (DB.obj (op (F.obj K)))) (delta' (F.obj K))) ≫
          ev' (DB.obj (op (F.obj K))) := by rw [hdelta']
    _ = T'.map (Prod.mkHom (𝟙 (F.obj (DA.obj (op K)))) (delta' (F.obj K))) ≫
        T'.map (Prod.mkHom (𝟙 (F.obj (DA.obj (op K)))) (DB.map (beta K).op)) ≫
          ev' (F.obj (DA.obj (op K))) := by
      calc
        _ = T'.map (Prod.mkHom (𝟙 (F.obj (DA.obj (op K)))) (delta' (F.obj K))) ≫
            T'.map (Prod.mkHom (beta K)
              (𝟙 (DB.obj (op (DB.obj (op (F.obj K))))))) ≫
                ev' (DB.obj (op (F.obj K))) := by
          simpa only [Category.assoc] using congrArg
            (fun q ↦ q ≫ ev' (DB.obj (op (F.obj K))))
            (tensor_map_exchange T' (beta K) (delta' (F.obj K))).symm
        _ = _ := by rw [hevnat]
    _ = _ := by rw [tensor_map_comp, Category.assoc]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Biduality follows from the scalar evaluation square.
Source: current blueprint thm-coef-rational-verdier.proof.md, paragraph 3;
lem-coef-integral-finite-extension.proof.md, evaluation and transposition paragraphs.
(blueprint: lem-coef-rational-verdier-comparison-biduality).

Proof: the natural signed symmetries of A and B are uniquely determined by
their Koszul representative equations. Indeed represent each ambient derived
object by a K-flat complex and use naturality of the swap to conjugate to those
representatives. The completed tensorator respects the two swaps: on homogeneous
K-flat tensors its coefficient factors have degree zero, so the Koszul signs
on the two paths agree, and the completion normalizations identify the maps.
For every integral representative K, transpose the supplied evaluation square
again, now in the dual input. IntegralVerdier.delta is exactly the transpose of
evaluation after the signed swap. Use the preceding symmetry square and
naturality of the comparison isomorphism to identify the two transposes with
the two displayed double-dual composites. The tensor-Hom Hom equivalence is
injective, so these composites are equal. A.bidual_integral and
B.bidual_integral identify the localized deltas with the specified bidual maps.
All raw rational objects are integral representatives; hence the same equality
holds for every K. No identity-field or zero-object exception is required -/
theorem evaluation_implies_biduality
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (hA : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (f : K ⟶ K') (g : M ⟶ M'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' M').hom =
        (A.symmetry.swap K M).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f))
    (hB : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X))
      (f : K ⟶ K') (g : M ⟶ M'),
      B.ordinary.tensor.map (Prod.mkHom f g) ≫ (B.symmetry.swap K' M').hom =
        (B.symmetry.swap K M).hom ≫ B.ordinary.tensor.map (Prod.mkHom g f))
    (e : Extension D l hl X E L i wE wL A B)
    (heval : (∀ K : sfRationalConstructibleCategory l E X,
    (tensor D l hl X L).map
        (Prod.mkHom (𝟙 ((scalar l X E L i).obj K)) (e.comparison.hom.app (op K))) ≫
      B.evaluation ((scalar l X E L i).obj K) =
    (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X)).inv.app
        (K, A.dual.obj (op K)) ≫
      (scalar l X E L i).map (A.evaluation K) ≫ e.omega.hom)) :
    (∀ K : sfRationalConstructibleCategory l E X,
    (scalar l X E L i).map (A.bidual.hom.app K) ≫
      e.comparison.hom.app (op (A.dual.obj (op K))) =
    B.bidual.hom.app ((scalar l X E L i).obj K) ≫
      B.dual.map (e.comparison.hom.app (op K)).op)  := by
  obtain ⟨sA⟩ := pairing_calculus D l hl X E wE A hA
  obtain ⟨sB⟩ := pairing_calculus D l hl X L wL B hB
  intro K
  exact evaluation_bidual (tensor D l hl X E) (tensor D l hl X L)
    (scalar l X E L i) A.dual B.dual
    ((sfRationalConstructibleLocalization l E X).obj wE.omega)
    ((sfRationalConstructibleLocalization l L X).obj wL.omega)
    A.evaluation B.evaluation (fun K ↦ A.bidual.hom.app K)
    (fun K ↦ B.bidual.hom.app K) sA.swap sB.swap
    (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X))
    e.omega.hom (fun K ↦ e.comparison.hom.app (op K))
    sA.bidual sB.bidual sB.natural B.evaluation_natural sB.detect
    (scalar_interchange D l hl X E L i wE wL A B hA hB sA sB) heval K

end WeilConjectures.RationalVerdier
