/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Higher open direct images over a field

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
cor-fin-deligne-open-over-field (blueprint: cor-fin-deligne-open-over-field).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Higher open direct images of constructible prime-field sheaves over a field are
bounded constructible in the ordinary derived category.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
cor-fin-deligne-open-over-field (blueprint: cor-fin-deligne-open-over-field).

Proof plan:
1. Take S = Spec k with its identity structure map. A field has only the prime ideal (0)
and is reduced, so S is integral and its underlying space is a singleton. The identity
is of finite type, since k is generated over itself by the empty family. The given
finite-type k-schemes, open immersion and constructible F_l-sheaf meet all hypotheses
of thm-fin-deligne-generic-open, since l differs from the characteristic of k.
2. That theorem supplies a nonempty open U of S with bounded constructible open direct
image. The only nonempty open of the singleton S is S itself. The canonical identity
base-change identifications identify X_U, Y_U, j_U and the restricted sheaf with X, Y,
j and F. Thus its conclusion is precisely bounded constructibility of Rj_*F on Y.
The exchange-isomorphism conclusion of the generic theorem is not needed. -/
theorem isBoundedConstructible_rightDerivedLowerStar_primeSheaf_of_isOpenImmersion
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : l ≠ ringChar k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : X ⟶ Y) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod l)) Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) j).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  obtain ⟨U, ⟨s⟩, hU⟩ :=
    exists_nonempty_open_isBoundedConstructible_derived_open_pushforward k
      (Spec (.of k)) (𝟙 _) l hl X Y (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))
      j (by simp) F hF
  have htop : U = ⊤ := by
    apply top_unique
    intro x hx
    exact Subsingleton.elim (x : Spec (.of k)) s.val ▸ s.property
  subst U
  let : IsIso (⊤ : (Spec (.of k)).Opens).ι :=
    inferInstanceAs (IsIso (Spec (.of k)).topIso.hom)
  have hcart : IsPullback (𝟙 Y)
      ((Y ↘ Spec (.of k)) ≫ (Spec (.of k)).topIso.inv)
      (Y ↘ Spec (.of k)) (⊤ : (Spec (.of k)).Opens).ι :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := (hU X Y (𝟙 X) (𝟙 Y)
    ((Y ↘ Spec (.of k)) ≫ (Spec (.of k)).topIso.inv) j
    hcart (IsPullback.id_horiz j)).1
  let e := (rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) j).mapIso
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) X).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F))
  obtain ⟨hc, a, b, hab, hv⟩ := h
  refine ⟨fun i ↦ ?_, a, b, hab, fun i hi ↦ ?_⟩
  · obtain ⟨S, hS⟩ := hc i
    refine ⟨S, fun t ↦ ?_⟩
    obtain ⟨d, hd⟩ := hS t
    let ei := (_root_.DerivedCategory.homologyFunctor _ i).mapIso e
    let es := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l)))
      (S.immersion t)).mapIso ei
    let d' : Scheme.LocallyConstantDatum _ :=
      { cover := d.cover
        isConstant := fun q ↦ by
          obtain ⟨M, _, ⟨eM⟩⟩ := hd q
          exact Sheaf.isConstant_of_iso _
            ((((S.domain t).smallEtaleTopology.overPullback _ _).mapIso es).symm ≪≫ eM) }
    refine ⟨d', fun q ↦ ?_⟩
    obtain ⟨M, hM, ⟨eM⟩⟩ := hd q
    exact ⟨M, hM, ⟨(((S.domain t).smallEtaleTopology.overPullback _ _).mapIso es).symm ≪≫
      eM⟩⟩
  · exact (hv i hi).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e).symm

end AlgebraicGeometry.Etale
