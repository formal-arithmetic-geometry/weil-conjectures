/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData

/-!
# Factorwise naturality of the tower compactification projection

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md`, clause (2),
factorwise naturality of the projection-formula composite and its tensor-source
realization lift (blueprint: lem-route-tensor-projection-factorwise-naturality).

The proof expands the proper counit transpose, the prescribed open tensor inverse mate,
and the fixed pullback compositor. Proper adjunction transpose naturality
(`proper_projection_natural₂`) gives the square in the proper factor; the open
adjunction mate and tensor comparison naturality (`open_tensor_natural₂`) give the
square in the open factor; naturality of the pullback compositor and functoriality of
`j_!` paste these into the displayed equality (`projection_natural₂`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (base : Base l E) (ops : Operations l E base)

private theorem proper_projection_natural₂
    {C D : Type*} [Category* C] [Category* D]
    (TX : C × C ⥤ C) (TY : D × D ⥤ D)
    (P : D ⥤ C) (R : C ⥤ D) (adj : P ⊣ R)
    (μ : TY ⋙ P ≅ (P.prod P) ⋙ TX)
    {N N' : C} {K K' : D} (u : N ⟶ N') (v : K ⟶ K') :
    TY.map (Prod.mkHom (R.map u) v) ≫
        adj.homEquiv _ _ (μ.hom.app (R.obj N', K') ≫
          TX.map (Prod.mkHom (adj.counit.app N') (𝟙 _))) =
      adj.homEquiv _ _ (μ.hom.app (R.obj N, K) ≫
          TX.map (Prod.mkHom (adj.counit.app N) (𝟙 _))) ≫
        R.map (TX.map (Prod.mkHom u (P.map v))) := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  have hμ := μ.hom.naturality (Prod.mkHom (R.map u) v)
  simp only [Functor.comp_map, Functor.prod_map] at hμ
  rw [← Category.assoc, hμ]
  simp only [Category.assoc]
  rw [← TX.map_comp, ← TX.map_comp]
  congr 2
  ext
  · exact adj.counit_naturality u
  · simp

private theorem open_tensor_natural₂
    {C D : Type*} [Category* C] [Category* D]
    (TX : C × C ⥤ C) (TY : D × D ⥤ D)
    (J : C ⥤ D) (P : D ⥤ C) (adj : J ⊣ P)
    (μ : TY ⋙ P ≅ (P.prod P) ⋙ TX)
    (χ : ∀ (N : C) (K : D), TY.obj (J.obj N, K) ≅
      J.obj (TX.obj (N, P.obj K)))
    (hχ : ∀ (N : C) (K : D),
      adj.homEquiv _ _ (χ N K).inv =
        TX.map (Prod.mkHom (adj.unit.app N) (𝟙 _)) ≫ μ.inv.app (J.obj N, K))
    {N N' : C} {K K' : D} (u : N ⟶ N') (v : K ⟶ K') :
    TY.map (Prod.mkHom (J.map u) v) ≫ (χ N' K').hom =
      (χ N K).hom ≫ J.map (TX.map (Prod.mkHom u (P.map v))) := by
  apply (cancel_mono (χ N' K').inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (χ N K).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left, hχ, hχ]
  have hμ := μ.inv.naturality (Prod.mkHom (J.map u) v)
  simp only [Functor.comp_map, Functor.prod_map] at hμ
  simp only [Category.assoc]
  rw [← hμ]
  simp only [← Category.assoc]
  rw [← TX.map_comp, ← TX.map_comp]
  congr 2
  ext
  · exact adj.unit_naturality u
  · simp

set_option maxHeartbeats 800000 in
-- The concrete derived tensor elaboration needs a larger local heartbeat budget.
private theorem projection_natural₂ {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {M N : D l E X} (v : M ⟶ N)
    {K L : D l E Y} (w : K ⟶ L) :
    (tensor l E base Y).map
        (Prod.mkHom ((F l E base ops c).map v) w) ≫
      projection l E base ops c N L =
    projection l E base ops c M K ≫
      (F l E base ops c).map
        ((tensor l E base X).map
          (Prod.mkHom v ((pull l E base (ops.geometry f)).map w))) := by
  let TX := tensor l E base X
  let TZ := tensor l E base c.Z
  let TY := tensor l E base Y
  let J := openD l E base (ops.openOp c.i)
  let R := push l E base (ops.geometry c.g)
  let Lf := pull l E base (ops.geometry c.g)
  let π := fun W T ↦ (adjunction l E base (ops.geometry c.g)).homEquiv _ _
    ((ops.geometry c.g).tensorPullback.hom.app (R.obj W, T) ≫
      TZ.map (Prod.mkHom
        ((adjunction l E base (ops.geometry c.g)).counit.app W) (𝟙 _)))
  let e := fun T ↦ (ops.comp c.i c.g).hom.app T ≫
    (eqToIso (congrArg (fun h ↦ pull l E base (ops.geometry h)) c.comm.symm)).hom.app T
  let χ := fun W T ↦ (ops.openTensor c.i W (Lf.obj T)).hom ≫
    J.map (TX.map (Prod.mkHom (𝟙 W) (e T)))
  have hπ := proper_projection_natural₂ TZ TY Lf R
    (adjunction l E base (ops.geometry c.g))
    (ops.geometry c.g).tensorPullback (J.map v) w
  have hχ₀ := open_tensor_natural₂ TX TZ J
    (pull l E base (ops.geometry c.i))
    (ops.openOp c.i).derivedAdjunction (ops.geometry c.i).tensorPullback
    (ops.openTensor c.i) (ops.openTensor_mate c.i) v (Lf.map w)
  have hc := (ops.comp c.i c.g).hom.naturality w
  simp only [Functor.comp_map] at hc
  have he : (pull l E base (ops.geometry c.i)).map (Lf.map w) ≫ e L =
      e K ≫ (pull l E base (ops.geometry f)).map w := by
    dsimp only [Lf] at hc ⊢
    dsimp only [e]
    simp only [Category.assoc]
    rw [← Category.assoc
      ((pull l E base (ops.geometry c.i)).map _)
      ((ops.comp c.i c.g).hom.app L)]
    rw [hc]
    simpa using (eqToIso (congrArg
      (fun h ↦ pull l E base (ops.geometry h)) c.comm.symm)).hom.naturality w
  have hχ : TZ.map (Prod.mkHom (J.map v) (Lf.map w)) ≫ χ N L =
      χ M K ≫ J.map (TX.map (Prod.mkHom v ((pull l E base (ops.geometry f)).map w))) := by
    dsimp only [χ]
    rw [← Category.assoc, hχ₀]
    simp only [Category.assoc]
    rw [← J.map_comp, ← J.map_comp, ← TX.map_comp, ← TX.map_comp]
    simp only [CategoryTheory.prod_comp, Prod.mkHom]
    rw [he]
    simp
  change TY.map (Prod.mkHom (R.map (J.map v)) w) ≫
    (π (J.obj N) L ≫ R.map (χ N L)) =
      (π (J.obj M) K ≫ R.map (χ M K)) ≫
        R.map (J.map (TX.map (Prod.mkHom v ((pull l E base (ops.geometry f)).map w))))
  rw [← Category.assoc, hπ, Category.assoc, ← R.map_comp, hχ,
    R.map_comp, Category.assoc]

/-- The specified compactification projection is natural in both ambient inputs.

Source: blueprint latest, `sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md`, clause (2), factorwise naturality
(blueprint: lem-route-tensor-projection-factorwise-naturality).

Proof. Write `J = j_!`, `Q = j^*`, `L = p^*`, `R = Rp_*`, `H = f^*`,
so `F = R J`; `α : L ⊣ R` has counit `ε`, `β : J ⊣ Q` has unit `η`;
`μ^p`, `μ^j` are the specified tensor-pullback comparisons and
`e_B : Q L B ≅ H B` is `ops.comp` followed by the `c.comm` transport.
1. Unfold `projection`: with `d_{N,B} = (ε_N ⊗ 1) ∘ μ^p_{RN,B}` and
   `π_{N,B} = α.homEquiv d_{N,B}`, one has `PF_{A,B} = R(k_{A,B}) ∘ π_{JA,B}`, where
   `k_{A,B} = J(1_A ⊗ e_B) ∘ χ_{A,LB}` and `χ = ops.openTensor`, whose inverse mate is
   `r_{A,C} = β.homEquiv χ_{A,C}⁻¹ = (μ^j_{JA,C})⁻¹ ∘ (η_A ⊗ 1)` (`openTensor_mate`).
2. For `n : N ⟶ N'` and `b : B ⟶ B'`, naturality of `μ^p` and of `ε` give
   `d_{N',B'} ∘ L(Rn ⊗ b) = (n ⊗ Lb) ∘ d_{N,B}`; the adjunction transpose square
   for `α` (`Adjunction.homEquiv_naturality_left`/`_right`, proved here as
   `proper_projection_natural₂`) gives
   `π_{N',B'} ∘ (Rn ⊗ b) = R(n ⊗ Lb) ∘ π_{N,B}`.
3. For `a : A ⟶ A'` and `c : C ⟶ C'`, unit naturality and naturality of `(μ^j)⁻¹` give
   `r_{A',C'} ∘ (a ⊗ Qc) = Q(Ja ⊗ c) ∘ r_{A,C}`; the transpose square for `β`
   (`open_tensor_natural₂`) gives
   `χ⁻¹_{A',C'} ∘ J(a ⊗ Qc) = (Ja ⊗ c) ∘ χ⁻¹_{A,C}`, and conjugating by the fixed
   isomorphisms `χ` gives `χ_{A',C'} ∘ (Ja ⊗ c) = J(a ⊗ Qc) ∘ χ_{A,C}`.
4. Put `c = Lb`; naturality `e_{B'} ∘ QLb = Hb ∘ e_B` and functoriality of `J` and of
   the tensor give `k_{A',B'} ∘ (Ja ⊗ Lb) = J(a ⊗ Hb) ∘ k_{A,B}`.
5. Step 2 with `n = Ja`, then Step 4, and Step 1 give
   `PF_{A',B'} ∘ (Fa ⊗ b) = F(a ⊗ f^*b) ∘ PF_{A,B}`.
Only the functors, the natural comparisons and the specified adjunctions occur: no
boundedness, constructibility, finite-Tor, smoothness or invertibility assumption. -/
theorem projection_factorwise_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {A A' : D l E X} (a : A ⟶ A')
    {B B' : D l E Y} (β : B ⟶ B') :
    (tensor l E base Y).map
          (Prod.mkHom ((F l E base ops c).map a) β) ≫
        projection l E base ops c A' B' =
      projection l E base ops c A B ≫
        (F l E base ops c).map
          ((tensor l E base X).map
            (Prod.mkHom a
              ((pull l E base (ops.geometry f)).map β))) := by
  exact projection_natural₂ l E base ops c a β

end AlgebraicGeometry.ProEtale.SpTowerShriek
