/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import all WeilConjectures.WeilSheaf.Native.NativeHomEvaluationSquareAllSources

/-! # Forgetting homogeneous uncurrying maps -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

open TensorEvaluation
variable {k₀ l X}

-- Comparing total components instantiates the two native tensor-Hom adjunctions.
/-- Forgetting the two normalized chain-level uncurrying maps gives the same map
after the total-tensor comparison.

Source: Stacks 08J9 and 0A97; native tensor-model evaluation argument, computation
on homogeneous tensor summands.
(blueprint: lem-sf-native-weil-chain-uncurry-forget).

Proof: test the two chain maps on every coproduct inclusion in each degree.
Cancel the underived tensor isomorphism and use N.chain_summand to identify the
inverse total comparison on that inclusion. Apply the two supplied component
normalizations. The projection condition on c identifies the curried components,
and N.underived_uncurry identifies their uncurrying. The coproduct universal
property and degreewise extensionality conclude the chain-map equality. -/
theorem native_weil_chain_uncurry_forget
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (W : CoefficientClosedStructure M.weilHom)
    (t : W.tensor ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (N : NativeWeilTensorPresentation k₀ l X M S W.monoidal t)
    (P Q I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    let U₀ := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
    let UC₀ := U₀.mapHomologicalComplex (.up ℤ)
    let H₀ := ihomBifunctor k₀ l X
    let H₁ := ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    ∀ (c : (UC₀).obj (CochainComplex.bifunctorHomObj (H₀) P I) ≅
      CochainComplex.bifunctorHomObj (H₁) ((UC₀).obj P) ((UC₀).obj I))
    (_hc : ∀ (n p q : ℤ) (hpq : p + n = q),
      c.hom.f n ≫ CochainComplex.bifunctorHomπ (H₁)
        ((UC₀).obj P) ((UC₀).obj I) n p q hpq =
          (U₀).map (CochainComplex.bifunctorHomπ (H₀) P I n p q hpq))
    (φ : Q ⟶ CochainComplex.bifunctorHomObj (H₀) P I)
    (ψ : CochainComplex.mapBifunctor P Q N.tensor ⟶ I)
    (ψ' : ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      ((UC₀).obj P) ((UC₀).obj Q) ⟶ (UC₀).obj I)
    (_hψ : ∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex.ιMapBifunctor P Q N.tensor (.up ℤ) p q n hpq ≫ ψ.f n =
        (N.tensor.obj (P.X p)).map (φ.f q ≫
          CochainComplex.bifunctorHomπ (H₀) P I q p n hpq) ≫
            (N.adjunction.adj (P.X p)).counit.app (I.X n))
    (_hψ' : ∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex.ιMapBifunctor ((UC₀).obj P) ((UC₀).obj Q)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n hpq ≫ ψ'.f n =
        ((ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
          (((UC₀).obj P).X p)).map
          ((((UC₀).map φ ≫ c.hom).f q) ≫
            CochainComplex.bifunctorHomπ (H₁) ((UC₀).obj P) ((UC₀).obj I) q p n hpq) ≫
          (Mod.ihomAdjunction (((UC₀).obj P).X p)).counit.app (((UC₀).obj I).X n)),
    (N.chain P Q).inv ≫ (UC₀).map ψ = ψ' := by
  dsimp only
  intro c hc φ ψ ψ' hψ hψ'
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine HomologicalComplex.mapBifunctor.hom_ext (K₁ := P) (K₂ := Q) (fun p q hpq => ?_)
  have hi : HomologicalComplex.ιMapBifunctor ((UC).obj P) ((UC).obj Q)
        (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (.up ℤ) p q n hpq ≫ (N.chain P Q).inv.f n =
      N.underived.inv.app (P.X p, Q.X q) ≫
        (U).map (HomologicalComplex.ιMapBifunctor P Q N.tensor (.up ℤ) p q n hpq) := by
    apply (cancel_epi (N.underived.hom.app (P.X p, Q.X q))).mp
    rw [← Category.assoc, ← N.chain_summand P Q p q n hpq]
    simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
      HomologicalComplex.id_f, Iso.hom_inv_id_app_assoc]
    exact Category.comp_id _
  change _ ≫ ((N.chain P Q).inv.f n ≫ (U).map (ψ.f n)) = _
  rw [← Category.assoc, hi, Category.assoc, ← Functor.map_comp, hψ, hψ' p q n hpq]
  have hu := N.underived_uncurry (P.X p) (Q.X q) (I.X n)
    (φ.f q ≫ CochainComplex.bifunctorHomπ (HW) P I q p n hpq)
  simp only [Adjunction.homEquiv_counit] at hu
  rw [hu]
  simp only [HomologicalComplex.comp_f, Category.assoc, hc]
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
