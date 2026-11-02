/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData

/-! # Restriction of the ambient exchange and the constant strict mate

The third strict coefficient equation `towerV'_delta` reduces, through the strict reduction
comparison `rho`, to the ambient-level equation `restriction_strictExchange` below. That
equation splits into the compatibility of scalar restriction with the ambient exchange
(`res_integralExchange`) and the constant-coefficient strict realization of the ambient
exchange (`constantExchange_reduction`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The ambient exchange with constant coefficients.
Source: Stacks 07A7 (blueprint: def-weil-pbc-ambient-ringed-exchange). -/
abbrev constantExchange (sq : ChosenCartesianSquare g' f' f g) :
    push (A := A) f ⋙ pull (A := A) g ⟶ pull (A := A) g' ⋙ push (A := A) f' :=
  proEtaleAmbientRingedExchange sq (exchangeConstantRing X A) (exchangeConstantRing Y A)
    (exchangeConstantRing X' A) (exchangeConstantRing Y' A) (exchangeConstantIso f A)
    (exchangeConstantIso g A) (exchangeConstantIso g' A) (exchangeConstantIso f' A)
    (exchangeConstant_coherent sq)

/-- The strict projection is natural in the ambient input.
Source: Stacks 0B56 (blueprint: lem-sp-completion-mate-comparison). -/
theorem projection_naturality {U V : Scheme.{t}} (u : U ⟶ V) {M N : D (A := A) U}
    (a : M ⟶ N) :
    (reduction d V).map ((push (A := A) u).map a) ≫ projection d u N =
      projection d u M ≫ (exchangeConstantPush (A := A) u).map ((reduction d U).map a) := by
  let aj := exchangeTowerAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)
  let ar := proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)
  let pi0 := (mateEquiv ar aj (TwoSquare.mk _ _ _ _ (reductionPullIso d u).hom)).natTrans
  have hpi (M : D (A := A) U) : pi0.app M = projection d u M := by
    apply (aj.homEquiv _ _).symm.injective
    change (aj.homEquiv _ _).symm (pi0.app M) =
      (aj.homEquiv _ _).symm ((aj.homEquiv _ _)
        ((reductionPullIso d u).hom.app ((push (A := A) u).obj M) ≫
          (reduction d U).map (ar.counit.app M)))
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact mateEquiv_counit ar aj (TwoSquare.mk _ _ _ _ (reductionPullIso d u).hom) M
  rw [← hpi, ← hpi]
  exact pi0.naturality a

/-- Scalar restriction carries the completed ambient exchange to the constant one,
conjugated by `alpha` and `chi`.
Source: Stacks 07A7, 0D6D, 0E48 (blueprint: lem-weil-pbc-ordered-strict-coefficient-equations).
Both exchanges are mates of the canonical pullback-composition comparisons
(`proEtaleCanonicalDerivedPullbackComparison`, transported along the square), `chi` is the
mate of the inverse of `alpha`, so by pasting of mates this reduces to the compatibility of
`alpha` with the two pullback-composition comparisons. Those comparisons are exact descents
of the ordinary composition isomorphisms on K-flat flat-term models, and `alpha` is the
exact descent of the ordinary restriction/pullback identity, so the remaining equation is
an ordinary identity-component cube (compare `Functor.mapDerivedCategory_cube`). Not yet
formalized. -/
theorem res_integralExchange (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) :
    (res d Y').map ((d.integralExchange sq).app K) ≫
        (chi d f').hom.app ((d.pull g').obj K) ≫
        (push (A := A) f').map ((alpha d g').hom.app K) =
      (alpha d g).hom.app ((d.push f).obj K) ≫
        (pull (A := A) g).map ((chi d f).hom.app K) ≫
        (constantExchange (A := A) sq).app ((res d X).obj K) := by
  sorry


/-- The adjunct computation behind `constantExchange_reduction`, for abstract adjunctions:
if the reduction/pullback comparisons are compatible with the two pullback squares, then
the reduction of the ambient mate and the tower mate agree through the projections. -/
theorem exchange_reduction_generic
    {DY DX DY' DX' TY TX TY' TX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category TY] [Category TX] [Category TY'] [Category TX']
    {pf : DY ⥤ DX} {pushf : DX ⥤ DY} (arf : pf ⊣ pushf)
    {pf' : DY' ⥤ DX'} {pushf' : DX' ⥤ DY'} (arf' : pf' ⊣ pushf')
    {Pf : TY ⥤ TX} {Pushf : TX ⥤ TY} (ajf : Pf ⊣ Pushf)
    {Pf' : TY' ⥤ TX'} {Pushf' : TX' ⥤ TY'} (ajf' : Pf' ⊣ Pushf')
    {pg : DY ⥤ DY'} {pg' : DX ⥤ DX'} {Pg : TY ⥤ TY'} {Pg' : TX ⥤ TX'}
    {redY : DY ⥤ TY} {redX : DX ⥤ TX} {redY' : DY' ⥤ TY'} {redX' : DX' ⥤ TX'}
    (τf : redY ⋙ Pf ≅ pf ⋙ redX) (τf' : redY' ⋙ Pf' ≅ pf' ⋙ redX')
    (τg : redY ⋙ Pg ≅ pg ⋙ redY') (τg' : redX ⋙ Pg' ≅ pg' ⋙ redX')
    (θ : pg ⋙ pf' ≅ pf ⋙ pg') (Θ : Pg ⋙ Pf' ≅ Pf ⋙ Pg')
    (E : pushf ⋙ pg ⟶ pg' ⋙ pushf') (T : Pushf ⋙ Pg ⟶ Pg' ⋙ Pushf')
    (πf : ∀ M, redY.obj (pushf.obj M) ⟶ Pushf.obj (redX.obj M))
    (πf' : ∀ M, redY'.obj (pushf'.obj M) ⟶ Pushf'.obj (redX'.obj M))
    (hE : ∀ N, pf'.map (E.app N) ≫ arf'.counit.app (pg'.obj N) =
      θ.hom.app (pushf.obj N) ≫ pg'.map (arf.counit.app N))
    (hT : ∀ Z, Pf'.map (T.app Z) ≫ ajf'.counit.app (Pg'.obj Z) =
      Θ.hom.app (Pushf.obj Z) ≫ Pg'.map (ajf.counit.app Z))
    (hπ : ∀ M, Pf.map (πf M) ≫ ajf.counit.app (redX.obj M) =
      τf.hom.app (pushf.obj M) ≫ redX.map (arf.counit.app M))
    (hπ' : ∀ M, Pf'.map (πf' M) ≫ ajf'.counit.app (redX'.obj M) =
      τf'.hom.app (pushf'.obj M) ≫ redX'.map (arf'.counit.app M))
    (hsq : ∀ N, Θ.hom.app (redY.obj N) ≫ Pg'.map (τf.hom.app N) ≫ τg'.hom.app (pf.obj N) =
      Pf'.map (τg.hom.app N) ≫ τf'.hom.app (pg.obj N) ≫ redX'.map (θ.hom.app N))
    (N : DX) :
    redY'.map (E.app N) ≫ πf' (pg'.obj N) ≫ Pushf'.map (τg'.inv.app N) =
      τg.inv.app (pushf.obj N) ≫ Pg.map (πf N) ≫ T.app (redX.obj N) := by
  apply (ajf'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Functor.comp_obj]
  have c1 := ajf'.counit.naturality (τg'.inv.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at c1
  rw [c1, reassoc_of% (hπ' (pg'.obj N)), hT]
  have n1 := τf'.hom.naturality (E.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n1
  rw [reassoc_of% n1, ← redX'.map_comp_assoc, hE, redX'.map_comp_assoc]
  have n2 := Θ.hom.naturality (πf N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n2
  rw [reassoc_of% n2, ← Pg'.map_comp, hπ, Pg'.map_comp]
  have h := hsq (pushf.obj N)
  have n3 := τg'.inv.naturality (arf.counit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n3
  have h' : Θ.hom.app (redY.obj (pushf.obj N)) ≫ Pg'.map (τf.hom.app (pushf.obj N)) =
      Pf'.map (τg.hom.app (pushf.obj N)) ≫ τf'.hom.app (pg.obj (pushf.obj N)) ≫
        redX'.map (θ.hom.app (pushf.obj N)) ≫ τg'.inv.app (pf.obj (pushf.obj N)) := by
    rw [← reassoc_of% h, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  rw [reassoc_of% h', ← Pf'.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Pf'.map_id, Category.id_comp]
  rw [← n3]
  rfl


/-- The strict projection is the adjunct of `reductionPullIso` followed by the reduction of the
ambient counit. -/
theorem projection_counit {U V : Scheme.{t}} (u : U ⟶ V) (M : D (A := A) U) :
    (exchangeConstantPull (A := A) u).map (projection d u M) ≫
        (exchangeTowerAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso u A)).counit.app ((reduction d U).obj M) =
      (reductionPullIso d u).hom.app ((push (A := A) u).obj M) ≫
        (reduction d U).map ((proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso u A)).counit.app M) := by
  refine (Adjunction.homEquiv_counit (exchangeTowerAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)) (g := projection d u M)).symm.trans ?_
  unfold projection
  exact Equiv.symm_apply_apply _ _


/-- The constant strict tower mate realizes the reduction of the constant ambient exchange
through the reduction/pullback comparisons and the strict projections.
Source: Stacks 07A7, 0B56, 099M (blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof plan: `exchange_reduction_generic` (proved above) gives this equation from the adjunct
formulas `mateEquiv_counit` (for `constantExchange` and the tower mate), `projection_counit`
(for `f` and `f'`), and the square compatibility
`Θ.app (red N) ≫ P_g'.map (τ_f.app N) ≫ τ_g'.app (p_f N) =
  P_f'.map (τ_g.app N) ≫ τ_f'.app (p_g N) ≫ red.map (θ.app N)`.
Here `τ = reductionPullIso`, `Θ = (exchangeConstantSquare sq).exchangeTowerSquare` and
`θ = proEtaleAmbientRingedPullbackComparison sq …`. The square compatibility is still to be
checked on K-flat flat-term models through `ordinaryReductionPullIso` and
`exchangeModuleComposition`.
Attempted: the instantiation of `exchange_reduction_generic` elaborates, but the kernel
times out even on the adjunct formula for `constantExchange` alone (`mateEquiv_counit`
against the stated adjunct, in its own lemma). With `maxHeartbeats 1000000` that lemma
exceeds 6 GB. The cost is in matching `pull`/`push` and `constantExchange` against the
types of `proEtaleRingDerivedAdjunction` and `proEtaleAmbientRingedExchange`. -/
theorem constantExchange_reduction (sq : ChosenCartesianSquare g' f' f g) (N : D (A := A) X) :
    (reduction d Y').map ((constantExchange (A := A) sq).app N) ≫
        projection d f' ((pull (A := A) g').obj N) ≫
        (exchangeConstantPush (A := A) f').map ((reductionPullIso d g').inv.app N) =
      (reductionPullIso d g).inv.app ((push (A := A) f).obj N) ≫
        (exchangeConstantPull (A := A) g).map (projection d f N) ≫
        (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app ((reduction d X).obj N) := by
  sorry

/-- The ambient form of the third strict coefficient equation.
Source: Stacks 099M, 0E48 (blueprint: lem-weil-pbc-ordered-strict-coefficient-equations).
Proof: combine `res_integralExchange` and `constantExchange_reduction` with the naturality
of the projection and of the reduction/pullback comparison. -/
theorem restriction_strictExchange (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) :
    (reduction d Y').map ((res d Y').map ((d.integralExchange sq).app K)) ≫
        (reduction d Y').map ((chi d f').hom.app ((d.pull g').obj K)) ≫
        projection d f' ((res d X').obj ((d.pull g').obj K)) ≫
        (exchangeConstantPush (A := A) f').map ((reduction d X').map ((alpha d g').hom.app K)) ≫
        (exchangeConstantPush (A := A) f').map ((reductionPullIso d g').inv.app ((res d X).obj K)) =
      (reduction d Y').map ((alpha d g).hom.app ((d.push f).obj K)) ≫
        (reductionPullIso d g).inv.app ((res d Y).obj ((d.push f).obj K)) ≫
        (exchangeConstantPull (A := A) g).map ((reduction d Y).map ((chi d f).hom.app K)) ≫
        (exchangeConstantPull (A := A) g).map (projection d f ((res d X).obj K)) ≫
        (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
          ((reduction d X).obj ((res d X).obj K)) := by
  have hA := congrArg (reduction d Y').map (res_integralExchange d sq K)
  simp only [Functor.map_comp] at hA
  have hB := constantExchange_reduction d sq ((res d X).obj K)
  have hP := projection_naturality d f' ((alpha d g').hom.app K)
  have hR := (reductionPullIso d g).inv.naturality ((chi d f).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hR
  rw [← reassoc_of% hP, reassoc_of% hA, hB, reassoc_of% hR]

end AlgebraicGeometry.Scheme.OrderedExchange
