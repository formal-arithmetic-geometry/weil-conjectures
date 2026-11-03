/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion

/-! # Strict scalar extension commutes with reassociation of total tensors

On cochain quotient systems, the strict scalar tensor comparison `sigma` is compatible
with any reassociation of total tensors which rebrackets pure triple tensors without a sign.
Source: Stacks Project, Tags 07A4 and 06YN.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftAdjoint integralComparisonSequenceScalarModel coefficientTotalTensor
attribute [local implicit_reducible] ScalarExtensionTower.tensor Functor.mapHomologicalComplex
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

open Opposite ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

/-- Paste a cochain square through an adjunction unit.
Source: naturality of the adjunction unit
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem adjunction_comparison_paste {B D : Type*} [Category B] [Category D]
    {F : B ⥤ D} {G : D ⥤ B} (adj : F ⊣ G)
    {P Q : B} {T V T' V' : D} (a : P ⟶ Q)
    (b : F.obj Q ⟶ T) (c : T ⟶ V)
    (b' : F.obj P ⟶ T') (c' : T' ⟶ V') (d : V' ⟶ V)
    (h : a ≫ adj.unit.app Q ≫ G.map b ≫ G.map c =
      adj.unit.app P ≫ G.map b' ≫ G.map c' ≫ G.map d) :
    F.map a ≫ b ≫ c = b' ≫ c' ≫ d := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  simpa only [Category.assoc] using h

/-- Pasting the six pure-section equations requires only function congruence.
Source: the pure-tensor calculation of Stacks 07A4
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem associativitySectionSquare
    {A B C D E F G H : Type*}
    (σ : A → B) (ηB : B → C) (κB : C → D) (tB : D → H)
    (ηA : A → E) (κA : E → F) (tA : F → G) (τ : G → H)
    (x : A) (b : B) (d : D) (h : H) (f : F) (g : G)
    (hσ : σ x = b) (hκB : κB (ηB b) = d) (htB : tB d = h)
    (hκA : κA (ηA x) = f) (htA : tA f = g) (hτ : τ g = h) :
    tB (κB (ηB (σ x))) = τ (tA (κA (ηA x))) := by
  rw [hσ, hκB, htB, hκA, htA, hτ]

/-- The strict scalar comparison on a generator of arbitrary total degree.
Source: Stacks 07A4 (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
theorem scalarSigma_generator (P Q : Complex l E W) (p q k : ℤ) (h : p + q = k)
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    ((((comparisons l).sigma E L ι W).hom.app (P, Q)).f k).val.app V (
      integralComparisonSequenceTensorSection l E L ι W
        (((tensor l E W).obj (P, Q)).X k) V 1
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q k h V x y)) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W)
        ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q k h V
        (integralComparisonSequenceTensorSection l E L ι W (P.X p) V 1 x)
        (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) := by
  subst k
  exact (comparisons l).sigma_formula E L ι W P Q p q V 1 x y

set_option maxHeartbeats 800000 in
-- Elaborating the nested total-complex comparison uses extra heartbeats.
/-- The strict scalar tensor comparison commutes with unsigned cochain reassociation.
Source: Stacks 07A4, with the unsigned reassociation of Tag 06YN
(blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: transpose both chain maps by the scalar-extension adjunction and detect equality
on local pure triples `x ⊗ y ⊗ z`. Both routes send such a triple to
`(1 ⊗ x) ⊗ ((1 ⊗ y) ⊗ (1 ⊗ z))`. -/
theorem scalarSigma_cochain_associativity (P Q N : Complex l E W)
    (aE : (tensor l E W).obj ((tensor l E W).obj (P, Q), N) ≅
      (tensor l E W).obj (P, (tensor l E W).obj (Q, N)))
    (aL : (tensor l L W).obj ((tensor l L W).obj
        ((scalar l E L ι W).obj P, (scalar l E L ι W).obj Q), (scalar l E L ι W).obj N) ≅
      (tensor l L W).obj ((scalar l E L ι W).obj P,
        (tensor l L W).obj ((scalar l E L ι W).obj Q, (scalar l E L ι W).obj N)))
    (haE : ∀ (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = n) (hn' : p + qr = n) (U : (ℕ × W.ProEt)ᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
      (aE.hom.f n).val.app U
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          ((tensor l E W).obj (P, Q)) N pq r n hn U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) P Q p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P
        ((tensor l E W).obj (Q, N)) p qr n hn' U x
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) Q N q r qr hqr U y z))
    (haL : ∀ (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = n) (hn' : p + qr = n) (U : (ℕ × W.ProEt)ᵒᵖ)
      (x : (((scalar l E L ι W).obj P).X p).val.obj U)
      (y : (((scalar l E L ι W).obj Q).X q).val.obj U)
      (z : (((scalar l E L ι W).obj N).X r).val.obj U),
      (aL.hom.f n).val.app U
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l L W)
          ((tensor l L W).obj ((scalar l E L ι W).obj P, (scalar l E L ι W).obj Q))
          ((scalar l E L ι W).obj N) pq r n hn U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l L W)
            ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W) ((scalar l E L ι W).obj P)
        ((tensor l L W).obj ((scalar l E L ι W).obj Q, (scalar l E L ι W).obj N))
        p qr n hn' U x
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l L W)
          ((scalar l E L ι W).obj Q) ((scalar l E L ι W).obj N) q r qr hqr U y z)) :
    (scalar l E L ι W).map aE.hom ≫
        ((comparisons l).sigma E L ι W).hom.app (P, (tensor l E W).obj (Q, N)) ≫
        (tensor l L W).map (Prod.mkHom (𝟙 ((scalar l E L ι W).obj P))
          (((comparisons l).sigma E L ι W).hom.app (Q, N))) =
      ((comparisons l).sigma E L ι W).hom.app ((tensor l E W).obj (P, Q), N) ≫
        (tensor l L W).map (Prod.mkHom (((comparisons l).sigma E L ι W).hom.app (P, Q))
          (𝟙 ((scalar l E L ι W).obj N))) ≫ aL.hom := by
  let adj := scalar_adj l E L ι W
  let κ := (comparisons l).sigma E L ι W
  let T := tensor l E W
  let TL := tensor l L W
  let C := scalar l E L ι W
  apply adjunction_comparison_paste (adj.mapHomologicalComplex (.up ℤ))
  apply CategoryTheory.tensorGenerator_ext₃.{u + 1, u, u}
  intro p q r pq k hpq hn U x y z
  have hqr : q + r = q + r := rfl
  have hn' : p + (q + r) = k := by omega
  let J := coefficientSequenceTopology (ProEt.topology W)
  let RE := coefficientSequenceCommRingSheaf l E W
  let RL := coefficientSequenceCommRingSheaf l L W
  let sc := fun (M : coefficientSequenceModules l E W) (w : M.val.obj U) ↦
    integralComparisonSequenceTensorSection l E L ι W M U 1 w
  have hu (M : coefficientSequenceModules l E W) (w : M.val.obj U) :
      (adj.unit.app M).val.app U w = sc M w := by
    dsimp only [adj, sc]
    unfold scalar_adj
    exact sequenceScalarAdjunction_unit l E L ι W M U w
  let gPQ := coefficientTensorGenerator.{u, u + 1, u} J RE P Q p q pq hpq U x y
  let gQN := coefficientTensorGenerator.{u, u + 1, u} J RE Q N q r (q + r) hqr U y z
  let g := coefficientTensorGenerator.{u, u + 1, u} J RE (T.obj (P, Q)) N pq r k hn U gPQ z
  let gR := coefficientTensorGenerator.{u, u + 1, u} J RE P (T.obj (Q, N))
    p (q + r) k hn' U x gQN
  let xs := sc (P.X p) x
  let ys := sc (Q.X q) y
  let zs := sc (N.X r) z
  let gQN' := coefficientTensorGenerator.{u, u + 1, u} J RL (C.obj Q) (C.obj N)
    q r (q + r) hqr U ys zs
  let gPQ' := coefficientTensorGenerator.{u, u + 1, u} J RL (C.obj P) (C.obj Q)
    p q pq hpq U xs ys
  let dR := coefficientTensorGenerator.{u, u + 1, u} J RL (C.obj P) (C.obj (T.obj (Q, N)))
    p (q + r) k hn' U xs (sc _ gQN)
  let hR := coefficientTensorGenerator.{u, u + 1, u} J RL (C.obj P) (TL.obj (C.obj Q, C.obj N))
    p (q + r) k hn' U xs gQN'
  let fL := coefficientTensorGenerator.{u, u + 1, u} J RL (C.obj (T.obj (P, Q))) (C.obj N)
    pq r k hn U (sc _ gPQ) zs
  let gL := coefficientTensorGenerator.{u, u + 1, u} J RL (TL.obj (C.obj P, C.obj Q)) (C.obj N)
    pq r k hn U gPQ' zs
  change ((TL.map (Prod.mkHom (𝟙 (C.obj P)) (κ.hom.app (Q, N)))).f k).val.app U
      (((κ.hom.app (P, T.obj (Q, N))).f k).val.app U
        ((adj.unit.app _).val.app U ((aE.hom.f k).val.app U g))) =
    (aL.hom.f k).val.app U
      (((TL.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (C.obj N)))).f k).val.app U
        (((κ.hom.app (T.obj (P, Q), N)).f k).val.app U
          ((adj.unit.app _).val.app U g)))
  refine associativitySectionSquare
    ((aE.hom.f k).val.app U)
    ((adj.unit.app ((T.obj (P, T.obj (Q, N))).X k)).val.app U)
    (((κ.hom.app (P, T.obj (Q, N))).f k).val.app U)
    (((TL.map (Prod.mkHom (𝟙 (C.obj P)) (κ.hom.app (Q, N)))).f k).val.app U)
    ((adj.unit.app ((T.obj (T.obj (P, Q), N)).X k)).val.app U)
    (((κ.hom.app (T.obj (P, Q), N)).f k).val.app U)
    (((TL.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (C.obj N)))).f k).val.app U)
    ((aL.hom.f k).val.app U)
    g gR dR hR fL gL ?_ ?_ ?_ ?_ ?_ ?_
  · exact haE p q r pq (q + r) k hpq hqr hn hn' U x y z
  · rw [hu]
    exact scalarSigma_generator l E L ι W P (T.obj (Q, N)) p (q + r) k hn' U x gQN
  · have hm := generator_map l L W (𝟙 (C.obj P)) (κ.hom.app (Q, N)) p (q + r) k hn' U xs
      (sc _ gQN)
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, u + 1, u}
      J RL (C.obj P) (TL.obj (C.obj Q, C.obj N)) p (q + r) k hn' U xs w)
      (scalarSigma_generator l E L ι W Q N q r (q + r) hqr U y z))
  · rw [hu]
    exact scalarSigma_generator l E L ι W (T.obj (P, Q)) N pq r k hn U gPQ z
  · have hm := generator_map l L W (κ.hom.app (P, Q)) (𝟙 (C.obj N)) pq r k hn U
      (sc _ gPQ) zs
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, u + 1, u}
      J RL (TL.obj (C.obj P, C.obj Q)) (C.obj N) pq r k hn U w zs)
      (scalarSigma_generator l E L ι W P Q p q pq hpq U x y))
  · exact haL p q r pq (q + r) k hpq hqr hn hn' U xs ys zs

end WeilConjectures
