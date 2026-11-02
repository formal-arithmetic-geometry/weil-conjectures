/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement

/-!
# Invertibility of the completed proper/open gamma

The proper/open comparison `cbcProperOpenGamma` on completed-ring modules is invertible
on complete objects with compatible bounded-below etale origins. The proof passes to the
strict quotient tower after constant-coefficient restriction, where the strict proper/open
gamma is invertible by finite compact-support base change.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

section Reflection

private theorem derivedReflectsIso
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] {X Y : DerivedCategory C} (f : X ⟶ Y)
    (hf : IsIso (F.mapDerivedCategory.map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map f)) :=
    inferInstance
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2 (by
      dsimp only [Functor.comp_map]
      infer_instance)
  exact isIso_of_reflects_iso _ F

/-- Termwise constant-coefficient restriction of strict towers reflects isomorphisms.
Source: Stacks 03DA (blueprint: thm-cbc-complete-proetale). -/
theorem exchangeTowerModuleRes_reflectsIsomorphisms (T : Scheme.{t}) :
    (exchangeTowerModuleRes d T).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have hr := (proEtaleRingRestrictScalars_properties (exchangeScalar d T)).2.2
    have h2 (n : ℕᵒᵖ) : IsIso (f.app n) := by
      have : IsIso ((proEtaleRingRestrictScalars (exchangeScalar d T)).map (f.app n)) :=
        (inferInstance : IsIso (((exchangeTowerModuleRes d T).map f).app n))
      exact isIso_of_reflects_iso (f.app n) (proEtaleRingRestrictScalars (exchangeScalar d T))
    exact NatIso.isIso_of_isIso_app f

/-- Derived constant-coefficient restriction of strict towers reflects isomorphisms.
Source: Stacks 05RT, 03DA (blueprint: thm-cbc-complete-proetale). -/
theorem exchangeTowerRes_isIso_iff (T : Scheme.{t})
    {M N : DerivedCategory (exchangeTowers T (d.completedRing T))} (f : M ⟶ N) :
    IsIso ((exchangeTowerRes d T).map f) ↔ IsIso f := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  have := exchangeTowerModuleRes_reflectsIsomorphisms d T
  exact derivedReflectsIso (exchangeTowerModuleRes d T) f h

/-- The quotient completion unit is natural.
Source: blueprint completed pullback (blueprint: thm-cbc-complete-proetale). -/
theorem completionUnit_naturality (T : Scheme.{t}) {K L : d.derived T} (f : K ⟶ L) :
    f ≫ d.completionUnit T L = d.completionUnit T K ≫
      (completedRlim T (d.completedRing T)).map ((completedReductionTower T d).map f) := by
  have h := ((d.constantRlimAdjunction T).unit ≫ Functor.whiskerRight
    (completedReductionAugmentation d T) (completedRlim T (d.completedRing T))).naturality f
  simpa only [AdicCoefficientDatum.completionUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.id_map, Category.assoc] using h

/-- A map of quotient-tower complete objects is invertible if its reduction tower is.
Source: Stacks 099N; blueprint step 8 (blueprint: thm-cbc-complete-proetale). -/
theorem isIso_of_reductionTower_isIso (T : Scheme.{t}) {K L : d.derived T} (f : K ⟶ L)
    (hK : d.TowerComplete T K) (hL : d.TowerComplete T L)
    (hf : IsIso ((completedReductionTower T d).map f)) : IsIso f := by
  have : IsIso (d.completionUnit T K) := hK
  have : IsIso (d.completionUnit T L) := hL
  have : IsIso (f ≫ d.completionUnit T L) := by
    rw [completionUnit_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right f (d.completionUnit T L)

end Reflection

/-- Intrinsic completeness implies quotient-tower completeness.
Source: blueprint order 1587 (blueprint: thm-cbc-complete-proetale). -/
theorem cbcTowerComplete_of_completeProperty (T : Scheme.{t})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) (hK : cbcCompleteProperty d T r a ha K) :
    d.TowerComplete T K := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)
  change IsIso (intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)) at hK
  change IsIso (d.completionUnit T K)
  change intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫
      c.hom = d.completionUnit T K at hc
  rw [← hc]
  infer_instance

/-- Strict reduction followed by constant-coefficient restriction: the comparison of
completed-ring objects with derived strict towers of constant-coefficient modules.
Source: blueprint step 8 (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcStrictReduction (T : Scheme.{t}) : d.derived T ⥤ ProEtale.StrictTower.Derived A T :=
  completedReductionTower T d ⋙ exchangeTowerRes d T

/-- Extension by zero along a quasi-compact open immersion preserves quotient-tower
completeness. Source: blueprint lem-cbc-completed-extension-zero-comparison, Stacks 099N
(blueprint: thm-cbc-complete-proetale).
Proof sketch: for quasi-compact j, recollement writes j_! as the kernel of two
product-preserving functors, so j_! commutes with countable products and hence with Rlim;
it also commutes with strict quotient reduction (cbcRingedOpenStrictReduction). Thus the
completion unit of j_! M is j_! of that of M, up to these isomorphisms. -/
theorem cbcJ_towerComplete {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    [QuasiCompact j] (M : d.derived U) (hM : d.TowerComplete U M) :
    d.TowerComplete T ((cbcJ d j).obj M) := by
  sorry

/-- After strict reduction and constant-coefficient restriction, the completed proper/open
gamma is conjugate to the strict-tower proper/open gamma.
Source: blueprint step 8 (blueprint: thm-cbc-complete-proetale).
Proof sketch: strict reduction followed by restriction commutes with inverse image (the
normalized reduction/pullback comparison and `exchangeResPull`), with direct image
(`towerProjection` and `exchangeResPush`, the mates of the former) and with open
extension (`cbcRingedOpenStrictReduction`). These comparisons are compatible with the
adjunction units and counits, with the inverse-image compositors and hence with the open
compositors. Therefore they carry the open base-change comparison, the clopen projection
and alpha to their strict versions, and the proper-adjunction mate gamma to the strict
gamma. -/
theorem cbcProperOpenGamma_strictConjugate {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (K : d.derived V) :
    ∃ (e₁ : (cbcStrictReduction d T).obj ((cbcJ d i).obj ((d.push r).obj K)) ≅
        (ProEtale.StrictTower.J A i).obj
          ((ProEtale.StrictTower.R A r).obj ((cbcStrictReduction d V).obj K)))
      (e₂ : (cbcStrictReduction d T).obj ((d.push p).obj ((cbcJ d k).obj K)) ≅
        (ProEtale.StrictTower.R A p).obj
          ((ProEtale.StrictTower.J A k).obj ((cbcStrictReduction d V).obj K))),
      (cbcStrictReduction d T).map ((cbcProperOpenGamma d k r p i h).app K) =
        e₁.hom ≫ (ProEtale.StrictTower.gamma A k r p i h).app
          ((cbcStrictReduction d V).obj K) ≫ e₂.inv := by
  sorry

/-- Compatible etale origins of a completed object give finite constant-coefficient etale
origins of every level of its restricted strict reduction tower.
Source: blueprint def-weil-pbc-bounded-constructible-complete and
def-cbc-finite-constant-coefficient-transport (blueprint: thm-cbc-complete-proetale).
Proof sketch: at level n take Λ = A/I^(n+1), the quotient map A → Λ and the retained
bounded-below etale origin of the n-th witnessed level; its realization is identified
with the n-th completed reduction, which is the n-th level of the strict reduction tower,
and restriction of scalars along A → Λ matches constant-coefficient restriction. -/
theorem cbcStrictReduction_scalarEtaleOrigin (V : Scheme.{t}) (K : d.derived V)
    (origins : PbcHasCompatibleEtaleOrigins V d K) (n : ℕ) :
    Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A V
      ((ProEtale.StrictTower.ev A V n).obj ((cbcStrictReduction d V).obj K))) := by
  sorry

/-- The proper/open gamma is invertible on complete objects with compatible etale origins.
Source: blueprint proof step 8; Stacks 0F7B, 09C9 (blueprint: thm-cbc-complete-proetale).
Proof: both sides are quotient-tower complete, so it suffices that the strict reduction of
gamma is invertible; constant-coefficient restriction reflects this. After restriction
gamma is conjugate to the strict gamma, which is invertible levelwise by finite
compact-support base change on the retained etale origins. -/
theorem cbcProperOpenGamma_app_isIso {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (n : ℕ) (a : Fin n → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d V n a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins V d K.obj) :
    IsIso ((cbcProperOpenGamma d k r p i h).app K.obj) := by
  have hK : d.TowerComplete V K.obj :=
    cbcTowerComplete_of_completeProperty d V n a ha K.obj K.property
  have hs : d.TowerComplete T ((cbcJ d i).obj ((d.push r).obj K.obj)) :=
    cbcJ_towerComplete d i _ (d.push_complete r K.obj hK)
  have ht : d.TowerComplete T ((d.push p).obj ((cbcJ d k).obj K.obj)) :=
    d.push_complete p _ (cbcJ_towerComplete d k _ hK)
  refine isIso_of_reductionTower_isIso d T _ hs ht ?_
  rw [← exchangeTowerRes_isIso_iff]
  obtain ⟨e₁, e₂, he⟩ := cbcProperOpenGamma_strictConjugate d k r p i h K.obj
  have := ProEtale.StrictTower.gamma_isIso A k r p i h ((cbcStrictReduction d V).obj K.obj)
    (fun m ↦ cbcStrictReduction_scalarEtaleOrigin d V K.obj origins m)
  change IsIso ((cbcStrictReduction d T).map _)
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme
