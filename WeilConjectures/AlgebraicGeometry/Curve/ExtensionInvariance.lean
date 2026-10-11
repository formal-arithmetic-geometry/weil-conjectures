/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AffineBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport

/-!
# Invariance of the cohomology of a smooth curve under algebraically closed extension

Let `k ⊆ k'` be algebraically closed fields, `C` a smooth separated curve over `k` and `n` prime
to `char k`. The pullback `Hᵠ(C, ℤ/n) ⟶ Hᵠ(C_{k'}, ℤ/n)` is bijective for every `q`.

It is injective in general (`AlgebraicGeometry.injective_cohomologyMap_pullback_fst_of_isAlgClosed`).
A smooth curve is the disjoint union of its finitely many connected components, each of which is
either a point `Spec k`, a smooth proper connected curve or a smooth affine connected curve; in
each case both sides are finite of the same order.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.bijective_fieldExtensionCohomologyMap`: the case of a smooth
  connected curve.
- `AlgebraicGeometry.IsCurve.bijective_fieldExtensionCohomologyMap_of_connectedSpace`: the case of
  a connected smooth curve, possibly a point.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) (k' : Type u) [Field k']
  [Algebra k k']

/-- **Invariance of the cohomology of a smooth connected curve.** Let `k ⊆ k'` be algebraically
closed fields, `C` a smooth connected curve over `k` and `n` prime to `char k`. Then the pullback
`Hᵠ(C, ℤ/n) ⟶ Hᵠ(C_{k'}, ℤ/n)` is bijective for every `q`. If the smooth compactification
`C ⊆ C̄` is all of `C̄`, then `C` is proper
(`AlgebraicGeometry.IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isProper`);
otherwise `C` is affine (`AlgebraicGeometry.IsConnectedCurve.isAffine_of_ne_top`,
`AlgebraicGeometry.IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isAffine`).
(blueprint: `thm-sc-constant-invariance`) -/
theorem IsConnectedCurve.bijective_fieldExtensionCohomologyMap [IsAlgClosed k]
    [IsConnectedCurve f] [Smooth f] [IsAlgClosed k'] (n : ℕ) (hn : (n : k) ≠ 0) (q : ℕ) :
    Function.Bijective (f.fieldExtensionCohomologyMap k' (C.constantZMod n) q) := by
  obtain ⟨c, hc, hsm, -, -⟩ := IsConnectedCurve.exists_smooth_properCompactification f
  by_cases h : Function.Surjective c.i.base
  · have : Surjective c.i := ⟨h⟩
    have : IsIso c.i := (isIso_iff_isOpenImmersion_and_surjective c.i).mpr ⟨inferInstance, ‹_›⟩
    have : IsProper f := c.comm ▸ inferInstance
    exact bijective_fieldExtensionCohomologyMap_of_isProper f k' n hn q
  · have hV : c.i.opensRange ≠ ⊤ := fun hV ↦ h fun x ↦ by
      have hx : x ∈ c.i.opensRange := hV ▸ trivial
      exact hx
    have := IsConnectedCurve.isAffine_of_ne_top c.g c.i.opensRange hV
    have : IsAffine C := IsAffine.of_isIso c.i.isoOpensRange.hom
    exact bijective_fieldExtensionCohomologyMap_of_isAffine (f := f) k' n hn q

/-- The cohomology of the pullback of `ℤ/n` is that of `ℤ/n`. -/
noncomputable def Scheme.Hom.sheafHUpperStarConstantZModAddEquiv {X Y : Scheme.{u}} (g : X ⟶ Y)
    (n q : ℕ) :
    Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj (Y.constantZMod n)) q ≃+
      Sheaf.H (X.constantZMod n) q :=
  ((Sheaf.functorH _ q).mapIso ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    g).app (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))).addCommGroupIsoToAddEquiv

/-- A smooth connected curve of dimension other than one is a point: the structure morphism is an
isomorphism. -/
lemma IsCurve.isIso_of_connectedSpace [IsAlgClosed k] [IsCurve f] [Smooth f] [ConnectedSpace C]
    (hdim : topologicalKrullDim C ≠ 1) : IsIso f := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have hle : topologicalKrullDim C ≤ 0 := by
    have h1 := IsCurve.krullDim_le_one (f := f)
    generalize topologicalKrullDim C = d at h1 hdim
    induction d using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe m =>
      induction m using ENat.recTopCoe with
      | top => exact absurd h1 (by decide)
      | coe m =>
        have h1' : m ≤ 1 := by exact_mod_cast h1
        have hdim' : m ≠ 1 := fun h ↦ hdim (by rw [h]; rfl)
        have : m = 0 := by omega
        subst this
        exact le_rfl
  have : Subsingleton C := subsingleton_of_topologicalKrullDim_le_zero hle
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  have hx : IsClosed ({x} : Set C) := by
    rw [show ({x} : Set C) = Set.univ from Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y x]
    exact isClosed_univ
  obtain ⟨σ, -⟩ := f.exists_fieldPoints_base_eq_of_isClosed hx
  let s : Spec (.of k) ⟶ C := σ.1
  have hs : s ≫ f = 𝟙 _ := by
    rw [σ.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have : IsClosedImmersion (s ≫ f) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  have : Surjective s := ⟨fun y ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : IsReduced C := isReduced_of_smooth f
  have : IsIso s := isIso_of_isClosedImmersion_of_surjective s
  have : IsIso (s ≫ f) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s f

/-- **Invariance of the cohomology of a connected smooth curve.** Let `k ⊆ k'` be algebraically
closed fields, `C` a connected smooth curve over `k` (possibly a point) and `n` prime to
`char k`. Then the pullback `Hᵠ(C, ℤ/n) ⟶ Hᵠ(C_{k'}, ℤ/n)` is bijective for every `q`.
`Hᵠ(C, ℤ/n)` is finite. If `C` has dimension one, this is
`AlgebraicGeometry.IsConnectedCurve.bijective_fieldExtensionCohomologyMap`; otherwise `C` and
`C_{k'}` are the points `Spec k` and `Spec k'`, with cohomology `ℤ/n` in degree zero only
(`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`).
(blueprint: `sk-prop-ext-invariance`) -/
theorem IsCurve.bijective_fieldExtensionCohomologyMap_of_connectedSpace [IsAlgClosed k]
    [IsCurve f] [Smooth f] [ConnectedSpace C] [IsAlgClosed k'] (n : ℕ) (hn : (n : k) ≠ 0)
    (q : ℕ) :
    Function.Bijective (f.fieldExtensionCohomologyMap k' (C.constantZMod n) q) := by
  by_cases hdim : topologicalKrullDim C = 1
  · have : IsConnectedCurve f := { connectedSpace := inferInstance, krullDim_eq_one := hdim }
    exact IsConnectedCurve.bijective_fieldExtensionCohomologyMap f k' n hn q
  have : IsIso f := IsCurve.isIso_of_connectedSpace f hdim
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace C := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have hinj := injective_cohomologyMap_pullback_fst_of_isAlgClosed f k' (C.constantZMod n) q
  let E := f.sheafHBaseChangeConstantZModAddEquiv k' n q
  set C' := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have : Subsingleton C' := Scheme.subsingleton_of_iso (asIso (f.baseChangeField k'))
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := Spec.map (CommRingCat.ofHom (algebraMap k k'))) x₀
    (default : Spec (.of k')) (Subsingleton.elim _ _)
  have : Nonempty C' := ⟨z⟩
  have : ConnectedSpace C' := inferInstance
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have : NeZero n := ⟨hn0⟩
  rcases q with _ | q
  · obtain ⟨e₀⟩ := C.nonempty_addEquiv_sheafH_zero_constantZMod n
    obtain ⟨e₀'⟩ := C'.nonempty_addEquiv_sheafH_zero_constantZMod n
    have : Finite (Sheaf.H (C'.constantZMod n) 0) := Finite.of_equiv _ e₀'.symm.toEquiv
    have := Finite.of_equiv _ E.symm.toEquiv
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_congr E.toEquiv, Nat.card_congr e₀.toEquiv, Nat.card_congr e₀'.toEquiv]
  · have : Subsingleton (Sheaf.H (C'.constantZMod n) (q + 1)) := by
      have := Scheme.subsingleton_H_of_isSepClosed k'
        ((Etale.upperStar AddCommGrpCat.{u + 1} (inv (f.baseChangeField k'))).obj
          (C'.constantZMod n)) q
      exact (Etale.injective_cohomologyMap_of_comp_eq_id (inv (f.baseChangeField k'))
        (f.baseChangeField k') (IsIso.hom_inv_id _) _ (q + 1)).subsingleton
    have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj
          (C.constantZMod n)) (q + 1)) := E.toEquiv.subsingleton
    exact ⟨hinj, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **Finiteness of the cohomology of a connected smooth curve.** For a connected smooth curve `C`
over an algebraically closed field `k` and `n` prime to `char k`, every `Hᵠ(C, ℤ/n)` is finite:
by the curve estimate if `C` is proper
(`AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isProper`), by
`AlgebraicGeometry.IsConnectedCurve.natCard_sheafH_one_constantZMod_mul` and
`AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isAffine` if `C` is affine, and since
`C = Spec k` otherwise. -/
theorem IsCurve.finite_sheafH_constantZMod_of_connectedSpace [IsAlgClosed k] [IsCurve f]
    [Smooth f] [ConnectedSpace C] (n : ℕ) (hn : (n : k) ≠ 0) (q : ℕ) :
    Finite (Sheaf.H (C.constantZMod n) q) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have : NeZero n := ⟨hn0⟩
  by_cases hdim : topologicalKrullDim C = 1
  · have : IsConnectedCurve f := { connectedSpace := inferInstance, krullDim_eq_one := hdim }
    obtain ⟨c, hc, hsm, -, -⟩ := IsConnectedCurve.exists_smooth_properCompactification f
    by_cases h : Function.Surjective c.i.base
    · have : Surjective c.i := ⟨h⟩
      have : IsIso c.i :=
        (isIso_iff_isOpenImmersion_and_surjective c.i).mpr ⟨inferInstance, ‹_›⟩
      have : IsProper f := c.comm ▸ inferInstance
      obtain ⟨⟨e₀⟩, ⟨e₁⟩, ⟨e₂⟩, h₃⟩ := IsConnectedCurve.sheafH_constantZMod_of_isProper f n hn
      rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ 2 < q by omega) with rfl | rfl | rfl | hq
      · exact Finite.of_equiv _ e₀.symm.toEquiv
      · exact Finite.of_equiv _ e₁.symm.toEquiv
      · exact Finite.of_equiv _ e₂.symm.toEquiv
      · have := h₃ q hq
        infer_instance
    · have hV : c.i.opensRange ≠ ⊤ := fun hV ↦ h fun x ↦ by
        have hx : x ∈ c.i.opensRange := hV ▸ trivial
        exact hx
      have := IsConnectedCurve.isAffine_of_ne_top c.g c.i.opensRange hV
      have : IsAffine C := IsAffine.of_isIso c.i.isoOpensRange.hom
      obtain ⟨⟨e₀⟩, -, -, -, h₂⟩ := IsConnectedCurve.sheafH_constantZMod_of_isAffine f n hn
      rcases (show q = 0 ∨ q = 1 ∨ 1 < q by omega) with rfl | rfl | hq
      · exact Finite.of_equiv _ e₀.symm.toEquiv
      · refine Nat.finite_of_card_ne_zero fun h0 ↦ ?_
        have h₁ := IsConnectedCurve.natCard_sheafH_one_constantZMod_mul f c hn
        rw [h0, zero_mul] at h₁
        exact pow_ne_zero _ hn0 h₁.symm
      · have := h₂ q hq
        infer_instance
  have : IsIso f := IsCurve.isIso_of_connectedSpace f hdim
  rcases q with _ | q
  · obtain ⟨e₀⟩ := C.nonempty_addEquiv_sheafH_zero_constantZMod n
    exact Finite.of_equiv _ e₀.symm.toEquiv
  · have := Scheme.subsingleton_H_of_isSepClosed k
      ((Etale.upperStar AddCommGrpCat.{u + 1} (inv f)).obj (C.constantZMod n)) q
    have := (Etale.injective_cohomologyMap_of_comp_eq_id (inv f) f (IsIso.hom_inv_id _)
      (C.constantZMod n) (q + 1)).subsingleton
    infer_instance

end AlgebraicGeometry
