/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.LocalSubring
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.RingTheory.Artinian.Ring

/-!
# Schemes over a field whose global functions are the constants

A `k`-scheme `X` satisfies `AlgebraicGeometry.Scheme.GlobalSectionsBijective k X` if the
structure map `k → Γ(X, 𝒪_X)` is bijective, i.e. `H⁰(X, 𝒪_X) = k`. This is the hypothesis
under which Riemann–Roch on a curve takes the form `χ(𝒪_X) = 1 - g`.

It does not hold for every proper connected `X`: `ℙ¹_ℂ` viewed as an `ℝ`-scheme has
`H⁰(X, 𝒪_X) = ℂ`. It holds for proper `X` that is geometrically connected and geometrically
reduced (Stacks 0BUG), hence for proper geometrically integral `X`, and for smooth proper
connected `X` over a separably closed field.

## Main definitions

- `AlgebraicGeometry.Scheme.GlobalSectionsBijective`: the structure map `k → Γ(X, 𝒪_X)` is
  bijective.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.finrankH_unit_zero`: `h⁰(X, 𝒪_X) = 1` when
  `H⁰(X, 𝒪_X) = k`.
- `AlgebraicGeometry.Scheme.finite_globalSectionsRingHom_of_isProper`: `Γ(X, 𝒪_X)` is finite
  over `k` for proper `X`.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyConnected`: a proper,
  geometrically connected and geometrically reduced `k`-scheme has `H⁰(X, 𝒪_X) = k`.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral` and
  `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isSepClosed`: the geometrically integral
  case and the case of a smooth connected scheme over a separably closed field.
- `AlgebraicGeometry.Scheme.isIntegralElem_of_universallyClosed`: global functions on an integral
  scheme universally closed over `k` are integral over `k` (valuative criterion), and
  `AlgebraicGeometry.Scheme.bijective_appTop_of_universallyClosed_of_isAlgClosed`: such a scheme
  over an algebraically closed field has `H⁰(X, 𝒪_X) = k`.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isAlgClosed`: a proper, reduced and
  connected scheme over an algebraically closed field has `H⁰(X, 𝒪_X) = k`.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.pullback`: `H⁰(X, 𝒪_X) = k` is stable under
  base change along a field extension `K/k`, for quasi-compact quasi-separated `X`.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.isIso_appTop_pullback_snd`: more generally
  `Γ(X ×_k U, 𝒪) = Γ(U, 𝒪_U)` for every affine `k`-scheme `U`.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.isIso_app_of_isPullback`: for a base change
  `π : X ×_k B ⟶ B`, `Γ(B, A) ≅ Γ(X ×_k B, π⁻¹ A)` for every affine open `A ⊆ B`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The structure map `k → Γ(X, 𝒪_X)` of a `k`-scheme `X` is bijective, i.e. `H⁰(X, 𝒪_X) = k`.

This is the hypothesis under which Riemann–Roch holds in the form `χ(𝒪_X) = 1 - g` with
`g = dim_k H¹(X, 𝒪_X)`. It fails for `ℙ¹_ℂ` viewed as an `ℝ`-scheme, which has `H⁰ = ℂ`, so
`χ(𝒪) = 2 ≠ 1 - 0` over `ℝ`. -/
class GlobalSectionsBijective : Prop where
  bijective_globalSectionsRingHom : Function.Bijective (globalSectionsRingHom k (X := X))

variable {k X}

/-- On a proper `k`-scheme `X`, the ring `Γ(X, 𝒪_X)` is finite over `k`: it is `H⁰(X, 𝒪_X)`,
which is finite-dimensional by finiteness of coherent cohomology. -/
theorem finite_globalSectionsRingHom_of_isProper [IsProper (X ↘ Spec (.of k))] :
    (globalSectionsRingHom k (X := X)).Finite := by
  let := (globalSectionsRingHom k (X := X)).toAlgebra
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := Modules.finiteDimensional_H_of_isProper (k := k) O 0
  let e : O.H 0 ≃ₗ[k] Γ(X, ⊤) :=
    { (Modules.H.zeroLinearEquiv O).toAddEquiv with
      map_smul' c x := by
        change Modules.H.zeroLinearEquiv O (globalSectionsRingHom k (X := X) c • x) = _
        rw [LinearEquiv.map_smul]
        rfl }
  exact Module.Finite.equiv e

/-- A proper `k`-scheme that is geometrically connected and geometrically reduced has
`H⁰(X, 𝒪_X) = k` (Stacks 0BUG). This is the input `Γ(X, 𝒪_X) = k` of Step 4 of blueprint
`lem-sc-rigidity` (`sk-prop-av-rigidity`).

Let `K` be an algebraic closure of `k`, `A = Γ(X, 𝒪_X)` and `B = Γ(X_K, 𝒪_{X_K})`. By flat base
change `B = K ⊗_k A`, and `A` is finite over `k` as `X` is proper. So `B` is a finite `K`-algebra,
reduced since `X_K` is reduced and without nontrivial idempotents since `X_K` is connected, hence
`B = K` (`IsAlgClosed.finrank_eq_one_of_isReduced`). Thus `A` has dimension `1` over `k`, and the
injective map `k → A` is bijective. -/
instance GlobalSectionsBijective.of_geometricallyConnected [IsProper (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))] :
    GlobalSectionsBijective k X := by
  let K := AlgebraicClosure k
  set iX := X ↘ Spec (.of k)
  set f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hpb := IsPullback.of_hasPullback iX f
  have : IsReduced (Limits.pullback iX f) :=
    GeometricallyReduced.geometrically_isReduced f _ _ hpb
  have : ConnectedSpace ↥(Limits.pullback iX f) :=
    GeometricallyConnected.geometrically_connectedSpace f _ _ hpb
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace iX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated iX
  have H := isPushout_appTop_of_flat f iX
  let A := Γ(X, ⊤)
  let B := Γ(Limits.pullback iX f, ⊤)
  let : Algebra k A := (globalSectionsRingHom k (X := X)).toAlgebra
  let : Algebra K B :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop).hom.toAlgebra
  let : Algebra A B := (Limits.pullback.fst iX f).appTop.hom.toAlgebra
  let : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  have hw : CommRingCat.ofHom (algebraMap k K) ≫ CommRingCat.ofHom (algebraMap K B) =
      CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom (algebraMap A B) := by
    change _ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ iX.appTop) ≫ (Limits.pullback.fst iX f).appTop
    rw [reassoc_of% Scheme.ΓSpecIso_inv_naturality, Category.assoc, H.w]
  have : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' congr($(hw).hom).symm
  -- Flat base change: `B = K ⊗_k A`.
  have : Algebra.IsPushout k K A B := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    refine H.flip.of_iso (Scheme.ΓSpecIso (.of k)) (Scheme.ΓSpecIso (.of K)) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
      simp [f]
    · change _ = _ ≫ (Scheme.ΓSpecIso (.of k)).inv ≫ iX.appTop
      simp
    · change _ = _ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop
      simp
    · simp
      rfl
  have : Module.Finite k A := finite_globalSectionsRingHom_of_isProper
  let e := (Algebra.IsPushout.equiv k K A B).toLinearEquiv
  have : Module.Finite K B := Module.Finite.equiv e
  obtain ⟨x⟩ : Nonempty ↥(Limits.pullback iX f) := inferInstance
  have : Nonempty (⊤ : (Limits.pullback iX f).Opens) := ⟨⟨x, trivial⟩⟩
  have hB : Module.finrank K B = 1 := IsAlgClosed.finrank_eq_one_of_isReduced
    ((connectedSpace_iff_isIdempotentElem (Limits.pullback iX f)).1 inferInstance)
  have hA : Module.finrank k A = 1 := by
    rw [← hB, ← e.finrank_eq, Module.finrank_baseChange]
  have : Nontrivial A := Module.nontrivial_of_finrank_eq_succ hA
  refine ⟨⟨(globalSectionsRingHom k (X := X)).injective, ?_⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := Algebra.linearMap k A) (by rw [hA, Module.finrank_self])).1
    (algebraMap k A).injective

/-- **Global functions on a proper curve.** A proper, reduced and connected scheme `X` over an
algebraically closed field `k` has `H⁰(X, 𝒪_X) = k`: the ring `Γ(X, 𝒪_X)` is a finite reduced
`k`-algebra (`AlgebraicGeometry.Scheme.finite_globalSectionsRingHom_of_isProper`) without
nontrivial idempotents, hence equal to `k` (`IsAlgClosed.finrank_eq_one_of_isReduced`).

The blueprint states this for proper connected curves; reducedness is needed, as the proper
connected curve `ℙ¹_k ×_k Spec k[ε]/(ε²)` has `H⁰ = k[ε]/(ε²)`. It holds for the smooth curves to
which the blueprint applies it.
(blueprint: `lem-sc-global-functions`) -/
instance GlobalSectionsBijective.of_isAlgClosed [IsAlgClosed k] [IsProper (X ↘ Spec (.of k))]
    [IsReduced X] [ConnectedSpace X] : GlobalSectionsBijective k X := by
  let A := Γ(X, ⊤)
  let : Algebra k A := (globalSectionsRingHom k (X := X)).toAlgebra
  have : Module.Finite k A := finite_globalSectionsRingHom_of_isProper
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  have hA : Module.finrank k A = 1 := IsAlgClosed.finrank_eq_one_of_isReduced
    ((connectedSpace_iff_isIdempotentElem X).1 inferInstance)
  refine ⟨⟨(globalSectionsRingHom k (X := X)).injective, ?_⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := Algebra.linearMap k A) (by rw [hA, Module.finrank_self])).1
    (algebraMap k A).injective

/-- **Global functions on a universally closed integral scheme are algebraic.** Let `Y` be an
integral scheme with a universally closed morphism `p : Y ⟶ Spec k`. Every global function on `Y`
is integral over `k`.

Otherwise some `a ∈ Γ(Y, 𝒪_Y)` is transcendental over `k`, and so is its image `b` in the function
field `K` of `Y`. Then `b` is not integral over (the image of) `k`, so some valuation ring `V` of
`K` contains `k` but not `b`. By the valuative criterion the generic point `Spec K ⟶ Y` extends to
`Spec V ⟶ Y`, and `b` is the image of a section of `𝒪_{Spec V}`, i.e. `b ∈ V`: a contradiction. -/
theorem isIntegralElem_of_universallyClosed {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] (p : Y ⟶ Spec (.of k)) [UniversallyClosed p] (a : Γ(Y, ⊤)) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.IsIntegralElem a := by
  classical
  set ψ := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom with hψ
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  let K : Type u := Y.functionField
  let φ : Γ(Y, ⊤) →+* K := (Y.germToFunctionField ⊤).hom
  have hφ : Function.Injective φ := germ_injective_of_isIntegral Y (U := ⊤) (genericPoint Y) trivial
  let f : k →+* K := φ.comp ψ
  by_contra ha
  -- the image `φ a` of `a` in the function field is not integral over `k`
  have hb : φ a ∉ (integralClosure (Subring.closure (Set.range f)) K).toSubring := by
    intro hb
    apply ha
    have hcl : Subring.closure (Set.range f) = f.range := by
      rw [← RingHom.coe_range, Subring.closure_eq]
    rw [hcl] at hb
    obtain ⟨q, hqm, hq⟩ := hb
    have hl : q ∈ Polynomial.lifts f.rangeRestrict :=
      Polynomial.mem_lifts_of_surjective f.rangeRestrict_surjective q
    obtain ⟨q', hq'map, -, hq'm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hqm
    refine ⟨q', hq'm, hφ ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, ← hq, ← hq'map, Polynomial.eval₂_map]
    rfl
  rw [← iInf_valuationSubring_superset, Subring.mem_iInf] at hb
  push Not at hb
  obtain ⟨⟨V, hsV⟩, hV⟩ := hb
  have hex : ValuativeCriterion.Existence p := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact this.1
  let ι : k →+* V := f.codRestrict V.toSubring fun c ↦ hsV ⟨c, rfl⟩
  have hsq : Y.fromSpecStalk (genericPoint Y) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ Spec.map (CommRingCat.ofHom ι) := by
    rw [← Spec.map_comp]
    apply ext_of_isAffine
    rw [← cancel_epi (ΓSpecIso (.of k)).inv, ← ΓSpecIso_inv_naturality, Scheme.Hom.comp_appTop,
      fromSpecStalk_appTop]
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  obtain ⟨⟨l⟩⟩ := hex ⟨V, K, Y.fromSpecStalk (genericPoint Y), Spec.map (CommRingCat.ofHom ι),
    ⟨hsq⟩⟩
  have e : (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l.l).appTop ≫
      (ΓSpecIso (.of K)).hom =
      (Y.fromSpecStalk (genericPoint Y)).appTop ≫ (ΓSpecIso (.of K)).hom := by
    rw [l.fac_left]
  rw [Scheme.Hom.comp_appTop, Category.assoc, ΓSpecIso_naturality, fromSpecStalk_appTop] at e
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id] at e
  have h : algebraMap V K ((ΓSpecIso (.of V)).hom.hom (l.l.appTop.hom a)) = φ a := by
    have h := congr($(e).hom a)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    rw [h]
    exact Iso.inv_hom_id_apply (ΓSpecIso _) _
  apply hV
  change φ a ∈ V
  rw [← h]
  exact ((ΓSpecIso (.of V)).hom.hom (l.l.appTop.hom a)).2
/-- **Global functions over an algebraically closed field.** An integral scheme `Y` universally
closed over an algebraically closed field `K` has `H⁰(Y, 𝒪_Y) = K`: every global function is
integral over `K` (`isIntegralElem_of_universallyClosed`), and `Γ(Y, 𝒪_Y)` is a domain. -/
theorem bijective_appTop_of_universallyClosed_of_isAlgClosed {K : Type u} [Field K]
    [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y] (p : Y ⟶ Spec (.of K)) [UniversallyClosed p] :
    Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom :=
  IsAlgClosed.ringHom_bijective_of_isIntegral _ (isIntegralElem_of_universallyClosed p)

/-- A proper geometrically integral `k`-scheme has `H⁰(X, 𝒪_X) = k`.

Let `K` be an algebraic closure of `k`, `A = Γ(X, 𝒪_X)` and `B = Γ(X_K, 𝒪_{X_K})`. Since `X_K` is
integral and proper over `K`, `B = K` (`bijective_appTop_of_universallyClosed_of_isAlgClosed`).
By flat base change `B = K ⊗_k A`, so `A` has dimension `1` over `k`. -/
theorem GlobalSectionsBijective.of_geometricallyIntegral [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] : GlobalSectionsBijective k X := by
  let K := AlgebraicClosure k
  set iX := X ↘ Spec (.of k)
  set f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hpb := IsPullback.of_hasPullback iX f
  have : IsIntegral (Limits.pullback iX f) :=
    GeometricallyIntegral.geometrically_isIntegral f _ _ hpb
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace iX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated iX
  have H := isPushout_appTop_of_flat f iX
  let A := Γ(X, ⊤)
  let B := Γ(Limits.pullback iX f, ⊤)
  let : Algebra k A := (globalSectionsRingHom k (X := X)).toAlgebra
  let : Algebra K B :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop).hom.toAlgebra
  let : Algebra A B := (Limits.pullback.fst iX f).appTop.hom.toAlgebra
  let : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  have hw : CommRingCat.ofHom (algebraMap k K) ≫ CommRingCat.ofHom (algebraMap K B) =
      CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom (algebraMap A B) := by
    change _ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ iX.appTop) ≫ (Limits.pullback.fst iX f).appTop
    rw [reassoc_of% Scheme.ΓSpecIso_inv_naturality, Category.assoc, H.w]
  have : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' congr($(hw).hom).symm
  -- Flat base change: `B = K ⊗_k A`.
  have : Algebra.IsPushout k K A B := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    refine H.flip.of_iso (Scheme.ΓSpecIso (.of k)) (Scheme.ΓSpecIso (.of K)) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
      simp [f]
    · change _ = _ ≫ (Scheme.ΓSpecIso (.of k)).inv ≫ iX.appTop
      simp
    · change _ = _ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop
      simp
    · simp
      rfl
  -- `B = K`, as `X_K` is integral and proper over the algebraically closed field `K`
  have hB : Function.Bijective (algebraMap K B) :=
    bijective_appTop_of_universallyClosed_of_isAlgClosed (Limits.pullback.snd iX f)
  let e := (Algebra.IsPushout.equiv k K A B).toLinearEquiv.trans
    (LinearEquiv.ofBijective (Algebra.linearMap K B) hB).symm
  have hA : Module.rank k A = 1 := by
    have h := e.rank_eq
    rw [Module.rank_baseChange, Module.rank_self] at h
    exact Cardinal.lift_eq_one.mp h
  have : Module.Finite k A := Module.finite_of_rank_eq_one hA
  have hA' : Module.finrank k A = 1 := Module.finrank_eq_of_rank_eq hA
  have : Nontrivial A := Module.nontrivial_of_finrank_eq_succ hA'
  refine ⟨⟨(globalSectionsRingHom k (X := X)).injective, ?_⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := Algebra.linearMap k A) (by rw [hA', Module.finrank_self])).1
    (algebraMap k A).injective

/-- A smooth proper connected scheme over a separably closed field `k` has
`H⁰(X, 𝒪_X) = k`.

(blueprint: `prop-pc-xk-integral`, part (1)) -/
theorem GlobalSectionsBijective.of_isSepClosed [IsSepClosed k] [Smooth (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] : GlobalSectionsBijective k X :=
  have := GeometricallyConnected.of_isSepClosed (k := k) X
  inferInstance

/-- **Flat base change of `H⁰(X, 𝒪_X) = k`.** If a quasi-compact quasi-separated `k`-scheme `X`
has `H⁰(X, 𝒪_X) = k`, then so does its base change `X_K = X ×_{Spec k} Spec K` along a field
extension `K/k`: `Γ(X_K, 𝒪_{X_K}) = Γ(X, 𝒪_X) ⊗_k K = K` since `K` is flat over `k`. -/
instance GlobalSectionsBijective.pullback (K : Type u) [Field K] [Algebra k K]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [GlobalSectionsBijective k X] :
    GlobalSectionsBijective K
      (Limits.pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  set f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  set iX := X ↘ Spec (.of k)
  have H := IsPullback.of_hasPullback iX f
  -- `Γ(X_K, ⊤)` is the pushout of `Γ(X, ⊤) ← k → K`.
  have hUY : (⊤ : (Limits.pullback iX f).Opens) =
      Limits.pullback.fst iX f ⁻¹ᵁ ⊤ ⊓ Limits.pullback.snd iX f ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H
    (US := ⊤) (UT := ⊤) (UX := ⊤) le_top le_top hUY
    (isAffineOpen_top _) (isAffineOpen_top _) isCompact_univ isQuasiSeparated_univ
  have hX : IsIso (iX.appLE ⊤ ⊤ le_top) := by
    have h := GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k) (X := X)
    rw [globalSectionsRingHom, ← ConcreteCategory.isIso_iff_bijective] at h
    have : IsIso iX.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv _
    simpa [Hom.appTop, Hom.app_eq_appLE] using this
  -- The pushout of the isomorphism `k → Γ(X, ⊤)` along `k → K` is an isomorphism.
  have hY : IsIso ((Limits.pullback.snd iX f).appLE ⊤ ⊤ (hUY.trans_le inf_le_right)) := by
    have e : pushout.inr _ _ ≫ pushoutSection H (US := ⊤) le_top le_top hUY = _ :=
      pushout.inr_desc _ _ _
    rw [← e]
    exact IsIso.comp_isIso' inferInstance hiso
  constructor
  rw [globalSectionsRingHom, ← ConcreteCategory.isIso_iff_bijective]
  have : IsIso (Limits.pullback.snd iX f).appTop := by
    simpa [Hom.appTop, Hom.app_eq_appLE] using hY
  exact IsIso.comp_isIso' inferInstance this

/-- **Flat base change of `H⁰(X, 𝒪_X) = k` to an affine scheme.** If a quasi-compact
quasi-separated `k`-scheme `X` has `H⁰(X, 𝒪_X) = k` and `U` is an affine `k`-scheme, then the
second projection induces an isomorphism `Γ(U, 𝒪_U) ≅ Γ(X ×_k U, 𝒪)`: by flat base change
along the flat map `k ⟶ Γ(U, 𝒪_U)`, `Γ(X ×_k U, 𝒪) = Γ(X, 𝒪_X) ⊗_k Γ(U, 𝒪_U)`. -/
theorem GlobalSectionsBijective.isIso_appTop_pullback_snd [CompactSpace X]
    [QuasiSeparatedSpace X] [GlobalSectionsBijective k X] {U : Scheme.{u}} [IsAffine U]
    (fU : U ⟶ Spec (.of k)) : IsIso (Limits.pullback.snd (X ↘ Spec (.of k)) fU).appTop := by
  have h := GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k) (X := X)
  rw [globalSectionsRingHom, ← ConcreteCategory.isIso_iff_bijective] at h
  have : IsIso (X ↘ Spec (.of k)).appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv _
  exact (isPushout_appTop_of_flat fU (X ↘ Spec (.of k))).isIso_inr_of_isIso

/-- A `k`-scheme with `H⁰(X, 𝒪_X) = k` is nonempty, since the ring of global functions of the
empty scheme is zero. -/
theorem GlobalSectionsBijective.nonempty [GlobalSectionsBijective k X] : Nonempty X := by
  by_contra h
  have : IsEmpty X := not_nonempty_iff.mp h
  exact one_ne_zero
    ((GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k) (X := X)).1
      (Subsingleton.elim _ _))

/-- A `k`-scheme with `H⁰(X, 𝒪_X) = k` is connected: its only idempotent global functions are
the idempotents `0` and `1` of the field `k`. -/
theorem GlobalSectionsBijective.connectedSpace [GlobalSectionsBijective k X] :
    ConnectedSpace X := by
  have := GlobalSectionsBijective.nonempty (k := k) (X := X)
  rw [connectedSpace_iff_isIdempotentElem]
  intro e he
  have hb := GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k) (X := X)
  obtain ⟨c, rfl⟩ := hb.2 e
  have hc : IsIdempotentElem c := hb.1 (by rw [map_mul]; exact he)
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hc with rfl | rfl
  · exact .inl (map_zero _)
  · exact .inr (map_one _)

/-- **`h⁰(X, 𝒪_X) = 1`** for a `k`-scheme `X` with `H⁰(X, 𝒪_X) = k`, using
`H⁰(X, 𝒪_X) = Γ(X, 𝒪_X)`. -/
theorem Modules.finrankH_unit_zero [GlobalSectionsBijective k X] :
    Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) 0 = 1 := by
  let φ := RingEquiv.ofBijective (globalSectionsRingHom k (X := X))
    GlobalSectionsBijective.bijective_globalSectionsRingHom
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : O.H 0 ≃ₗ[k] k :=
    { (Modules.H.zeroLinearEquiv O).toAddEquiv.trans φ.symm.toAddEquiv with
      map_smul' c x := by
        change φ.symm (Modules.H.zeroLinearEquiv O (globalSectionsRingHom k (X := X) c • x)) =
          c • _
        rw [LinearEquiv.map_smul]
        exact (map_mul φ.symm (φ c) (Modules.H.zeroLinearEquiv O x : Γ(X, ⊤))).trans
          (congrArg (· * _) (φ.symm_apply_apply c)) }
  exact e.finrank_eq.trans (Module.finrank_self k)

section BaseChange

/-- **Flat base change of `H⁰(X, 𝒪_X) = k` over an affine open.** Let `X` be a quasi-compact
quasi-separated `k`-scheme with `H⁰(X, 𝒪_X) = k`, and let `P = X ×_k B` be a base change of `X`.
Then for every affine open `A ⊆ B` the projection `π : P ⟶ B` induces an isomorphism
`Γ(B, A) ≅ Γ(P, π⁻¹ A)`: by flat base change, `Γ(P, π⁻¹ A) = Γ(X, 𝒪_X) ⊗_k Γ(B, A)`. -/
theorem GlobalSectionsBijective.isIso_app_of_isPullback [CompactSpace X] [QuasiSeparatedSpace X]
    [GlobalSectionsBijective k X] {P B : Scheme.{u}} {ρ : P ⟶ X} {π : P ⟶ B}
    {g : B ⟶ Spec (.of k)} (H : IsPullback ρ π (X ↘ Spec (.of k)) g) {A : B.Opens}
    (hA : IsAffineOpen A) : IsIso (π.app A) := by
  have hUY : π ⁻¹ᵁ A = ρ ⁻¹ᵁ ⊤ ⊓ π ⁻¹ᵁ A := by simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := A)
    (UX := ⊤) le_top le_top hUY (isAffineOpen_top _) hA isCompact_univ isQuasiSeparated_univ
  have hpush := (isIso_pushoutSection_iff _ _ _ _).mp hiso
  have hX : IsIso ((X ↘ Spec (.of k)).appLE ⊤ ⊤ le_top) := by
    have h := GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k) (X := X)
    rw [globalSectionsRingHom, ← ConcreteCategory.isIso_iff_bijective] at h
    have : IsIso (X ↘ Spec (.of k)).appTop :=
      IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv _
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using this
  have := hpush.isIso_inr_of_isIso
  rw [Scheme.Hom.app_eq_appLE]
  exact this

end BaseChange

end AlgebraicGeometry.Scheme
