/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.ReductionLeft
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# The projection formula for torsion objects

Let `Λ` be a principal ideal domain (for instance `Λ = 𝒪_E`). This file proves the projection
formula `PF_{f, K, L} : Rf_! K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)` over `Λ` when `K` is *torsion* (killed
by a nonzero integer) and bounded below, `K ⊗ᴸ Lf^* L` is bounded below, and `L` is bounded
constructible. The coefficient ring itself need not be torsion.

The proof is that of the finite projection formula, `sk-thm-sf-pf-finite`, run at the geometric
points of `Y`:

* geometric points detect isomorphisms
  (`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map`);
* the projection map commutes with compactly supported base change
  (`AlgebraicGeometry.Etale.projectionMapOfCompactification_baseChange'`), and the base change
  maps occurring there are invertible by proper base change for bounded below complexes with
  torsion cohomology (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`);
* on a geometric fibre `Spec Ω` the pullback of `L` is bounded with constructible, hence constant
  and finitely generated, cohomology sheaves. Over the principal ideal domain `Λ` a finitely
  generated module is the cokernel of an injective map `Λᵇ ⟶ Λᵃ`, and the constant complexes
  `(Λᵃ)` are dualizable, so the projection formula holds there by dévissage
  (`DerivedCategory.prop_of_bounded`).

## Main statements

- `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_of_forall_algClosurePoint`:
  the geometric-point criterion.
- `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_of_isSepClosed`: the
  projection formula over a separably closed field, at bounded constructible objects.
- `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_of_nsmul_id_eq_zero`: the
  projection formula for torsion objects.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)`. -/
local notation "𝐃(" X ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-! ### Torsion and proper base change -/

/-- If a nonzero integer kills an object of `D(X_ét, Λ)`, its cohomology sheaves are torsion. -/
lemma isTorsionModuleSheaf_homology_of_nsmul_id_eq_zero {X : Scheme.{u}} {M : 𝐃(X)} {N : ℕ}
    (hN : N ≠ 0) (hM : N • 𝟙 M = 0) (q : ℤ) :
    IsTorsionModuleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj M) := by
  set H := (_root_.DerivedCategory.homologyFunctor _ q).obj M
  have hH : N • 𝟙 H = 0 := by
    rw [← (_root_.DerivedCategory.homologyFunctor _ q).map_id, ← Functor.map_nsmul, hM,
      Functor.map_zero]
  rw [isTorsionModuleSheaf_iff_isTorsion]
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U s ↦ ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, Nat.pos_of_ne_zero hN, ?_⟩
  have := congr_arg (fun φ : H ⟶ H ↦ (φ.hom.app U).hom s) hH
  simpa using this

/-- **Proper base change for torsion objects**: the unbounded derived base change map of a
cartesian square with `f` proper is invertible at a bounded below object killed by a nonzero
integer. -/
theorem isIso_derivedBaseChangeMap_app_of_nsmul_id_eq_zero {X Y X' Y' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : IsPullback g' f' f g) (M : 𝐃(X)) (n : ℤ) [M.IsGE n] {N : ℕ} (hN : N ≠ 0)
    (hM : N • 𝟙 M = 0) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app M) :=
  (isIso_derivedBaseChangeMap_app_ι_obj_iff _ sq.toCommSq ⟨M, n, ‹_›⟩).2
    (isIso_baseChange_of_isProper_of_torsionHomology Λ sq _
      fun q ↦ isTorsionModuleSheaf_homology_of_nsmul_id_eq_zero hN hM q)

/-! ### The geometric point criterion -/

/-- **The projection formula can be checked on geometric fibres.** Let `c` be a compactification
of `f : X ⟶ Y`. Suppose that at every geometric point `x : Spec Ω ⟶ Y` the derived base change
maps of the proper part of `c` are invertible at `i_! K` and at `i_!(K ⊗ᴸ Lf^* L)`, and that the
projection formula holds on the fibre over `x` for the pullbacks of `K` and `L`. Then the
projection formula holds at `(K, L)`. -/
theorem hasProjectionFormulaOfCompactification_of_forall_algClosurePoint {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (K : 𝐃(X)) (L : 𝐃(Y))
    (h₁ : ∀ y : Y, IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback c.g (Y.algClosurePoint y)).toCommSq).app
        (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj K)))
    (h₂ : ∀ y : Y, IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback c.g (Y.algClosurePoint y)).toCommSq).app
        (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)))))
    (h₃ : ∀ y : Y, HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ)
      (c.ofIsPullback (IsPullback.of_hasPullback f (Y.algClosurePoint y)))
      ((L((pullback.fst f (Y.algClosurePoint y))^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ])).obj L)) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c K L := by
  refine isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map Λ _ fun y ↦ ?_
  have sq := IsPullback.of_hasPullback f (Y.algClosurePoint y)
  have key := projectionMapOfCompactification_baseChange' (ModuleCat.{u + 1} Λ) sq.toCommSq c
    (c.ofIsPullback sq) (pullback.fst c.g (Y.algClosurePoint y))
    (c.isPullback_i_ofIsPullback sq)
    (IsPullback.of_hasPullback c.g (Y.algClosurePoint y)).toCommSq K L
  simp only [rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app] at key
  have := h₁ y
  have := h₂ y
  have : IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ)
      (c.ofIsPullback sq)).app
        ((L((pullback.fst f (Y.algClosurePoint y))^*[ModuleCat.{u + 1} Λ])).obj K)).app
        ((L((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ])).obj L)) := h₃ y
  have hR : IsIso (_ ≫ _ ≫ _) := key ▸ (inferInstance : IsIso (_ ≫ _ ≫ _))
  exact IsIso.of_isIso_comp_right _ _

/-! ### Separably closed fields -/

variable (Λ) in
/-- The projection formula holds at the constant complex `(Λᵐ)` placed in degree `0`, which is
dualizable. -/
lemma hasProjectionFormulaOfCompactification_constantSheaf_pi {X' Y' : Scheme.{u}}
    {f' : X' ⟶ Y'} (c' : Compactification f') (E : 𝐃(X')) (m : ℕ) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c' E
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin m → Λ)))) := by
  refine hasProjectionFormulaOfCompactification_of_isDualizable _ c' E ?_
  let F := (constantSheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ (Fin m → Λ))
  refine isDualizableEtale_of_trivialization
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) 0 0 inferInstance inferInstance
    (fun n ↦ ?_) ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app F)
  by_cases hn : n = 0
  · subst hn
    exact ⟨m, ⟨Retract.ofIso (HomologicalComplex.singleObjXSelf _ 0 F)⟩⟩
  · exact ⟨0, ⟨{ i := 0, r := 0, retract :=
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn).eq_of_src _ _ }⟩⟩

variable (Λ) in
/-- Over a principal ideal domain a finitely generated module `M` sits in a short exact sequence
`0 ⟶ Λᵇ ⟶ Λᵃ ⟶ M ⟶ 0`. -/
lemma exists_shortExact_pi [IsPrincipalIdealRing Λ] [IsDomain Λ] (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    ∃ (a b : ℕ) (S : ShortComplex (ModuleCat.{u + 1} Λ)), S.ShortExact ∧
      Nonempty (S.X₁ ≅ ModuleCat.of Λ (Fin b → Λ)) ∧
      Nonempty (S.X₂ ≅ ModuleCat.of Λ (Fin a → Λ)) ∧ Nonempty (S.X₃ ≅ M) := by
  obtain ⟨a, φ, hφ⟩ := Module.Finite.exists_fin' Λ M
  let K := LinearMap.ker φ
  have : Module.Finite Λ K := Module.IsNoetherian.finite Λ K
  have : Module.Free Λ K := Module.free_of_finite_type_torsion_free'
  let S : ShortComplex (ModuleCat.{u + 1} Λ) :=
    ShortComplex.mk (ModuleCat.ofHom K.subtype) (ModuleCat.ofHom φ) (by
      ext x
      exact x.2)
  refine ⟨a, Module.finrank Λ K, S, ModuleCat.shortComplex_shortExact S ?_ ?_ ?_,
    ⟨(Module.finBasis Λ K).equivFun.toModuleIso⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  · intro y
    change φ y = 0 ↔ ∃ x : K, (x : Fin a → Λ) = y
    exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
  · exact Subtype.val_injective
  · exact hφ

/-- **The projection formula over a separably closed field.** Let `Λ` be a principal ideal
domain, `Ω` a separably closed field and `c'` a compactification of `f' : X' ⟶ Spec Ω`. The
projection formula holds at `(E, C)` for every `E` and every bounded constructible `C`: the
cohomology sheaves of `C` are constant with finitely generated values, built out of the
dualizable constant complexes `(Λᵃ)` by cones. -/
theorem hasProjectionFormulaOfCompactification_of_isSepClosed [IsPrincipalIdealRing Λ]
    [IsDomain Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of Ω)} (c' : Compactification f') (E : 𝐃(X')) {C : 𝐃(Spec (.of Ω))}
    (hC : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) C) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c' E C := by
  let τ := (projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c').app E
  let e := constantSheafEquivalenceOfIsSepClosed Λ (k := Ω)
  -- the projection formula at a constant sheaf with finitely generated value
  have hM : ∀ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M →
      τ.isoLocus ((_root_.DerivedCategory.singleFunctor _ 0).obj (e.functor.obj M)) := by
    intro M _
    obtain ⟨a, b, S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_shortExact_pi Λ M
    have hT := (hS.map_of_exact e.functor).singleTriangle_distinguished
    have h₁ : IsIso (τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (e.functor.obj S.X₁))) :=
      (NatTrans.isIso_app_iff_of_iso τ ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        (e.functor.mapIso e₁))).2
        (hasProjectionFormulaOfCompactification_constantSheaf_pi Λ c' E b)
    have h₂ : IsIso (τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (e.functor.obj S.X₂))) :=
      (NatTrans.isIso_app_iff_of_iso τ ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        (e.functor.mapIso e₂))).2
        (hasProjectionFormulaOfCompactification_constantSheaf_pi Λ c' E a)
    have h₃ := NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ τ hT h₁ h₂
    exact (NatTrans.isIso_app_iff_of_iso τ ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (e.functor.mapIso e₃))).1 h₃
  have hP : ∀ F : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) F →
      τ.isoLocus ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    intro F hF
    have : IsConstructibleSheaf F := hF
    have hfin := finite_Γ_of_isConstructibleSheaf (Λ := Λ) (k := Ω) F
    have : Module.Finite Λ (e.inverse.obj F) :=
      Module.Finite.equiv ((Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ) isTerminalEtalePoint).app F).toLinearEquiv
    exact (NatTrans.isIso_app_iff_of_iso τ ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (e.counitIso.app F))).1 (hM _ this)
  exact _root_.DerivedCategory.prop_of_bounded τ.isoLocus
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) (Spec (.of Ω))) hP C hC.1 hC.2

/-! ### Torsion objects -/

/-- **The projection formula for torsion objects.** Let `Λ` be a principal ideal domain and `c`
a compactification of `f : X ⟶ Y`. If `K` is killed by a nonzero integer and bounded below,
`K ⊗ᴸ Lf^* L` is bounded below and `L` is bounded constructible, the projection formula holds at
`(K, L)`. -/
theorem hasProjectionFormulaOfCompactification_of_nsmul_id_eq_zero [IsPrincipalIdealRing Λ]
    [IsDomain Λ] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : 𝐃(X)) (L : 𝐃(Y))
    {N : ℕ} (hN : N ≠ 0) (hK : N • 𝟙 K = 0) (n₁ : ℤ) [K.IsGE n₁] (n₂ : ℤ)
    [(((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)).IsGE n₂]
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y L) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c K L := by
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have hKL : N • 𝟙 (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj
      (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) = 0 := by
    rw [← NatTrans.id_app, ← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hK,
      Functor.map_zero, NatTrans.app_zero]
  have hi : ∀ T : 𝐃(X), N • 𝟙 T = 0 →
      N • 𝟙 (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj T) = 0 := fun T hT ↦ by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hT, Functor.map_zero]
  refine hasProjectionFormulaOfCompactification_of_forall_algClosurePoint c K L
    (fun y ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_)
  · have := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).isGE_mapDerivedCategory_obj
      K n₁
    exact isIso_derivedBaseChangeMap_app_of_nsmul_id_eq_zero _ _ n₁ hN (hi K hK)
  · have := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).isGE_mapDerivedCategory_obj
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) n₂
    exact isIso_derivedBaseChangeMap_app_of_nsmul_id_eq_zero _ _ n₂ hN (hi _ hKL)
  · exact hasProjectionFormulaOfCompactification_of_isSepClosed _ _
      (boundedConstructible_leftDerivedUpperStar _ _ hL)

end Etale

end AlgebraicGeometry
