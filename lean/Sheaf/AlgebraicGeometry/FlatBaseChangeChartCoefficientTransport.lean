/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison

/-! # Coefficient h-maps on the affine scalar-extension chart

Source: Stacks Project, Tags 02KH, 0096 and 0097.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
attribute [local irreducible] pushforward pushforwardComp pushforwardCongr pushforwardId

set_option maxHeartbeats 800000 in
-- Elaborating the coefficient comparisons uses several module functors.
/-- The affine base-change chart and its coefficient h-maps, before taking cohomology.
Source: Stacks Project, Tags 02KH (first paragraph), 0096 and 0097.
(blueprint: new-flat-base-change-chart-coefficient-transport)

Proof: Identify V and W with their spectra using hV and hW. The condition hAlgebra
makes the map of these spectra equal to the restriction of g. The fibre-product
universal property then gives σ from L to T, with inverse obtained from the two
projections. Pullback.hom_ext gives both inverse identities and the equation ef.
Pullback composition identifies the pullback of A along σ.hom with M. Here replace
tensorPullback by ordinary pullback using the unique left-adjoint comparison for
the same pushforward, then use restrictFunctorIsoPullback. Transpose this coefficient
isomorphism and its inverse to obtain φ and ψ. The adjunction triangle identities
and the inverse identities give the two displayed coefficient composite identities.
The equality of the projections to Spec Gamma(W) identifies the scalars; naturality
of multiplication under the coefficient identification gives the scalar square.
For the unit square transpose both routes along the composite pullback adjunction.
The composite-unit equations reduce the equality to D.unit_square restricted to L.
The restriction composition comparison is c below. All these are identities of
modules; no cohomology, Leray edge or invertibility of a base-change unit is used.
The construction also applies to empty opens and zero modules. -/
theorem exists_flatBaseChange_chart_coefficient_transport
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V) (D : FlatBaseChangeOpenChoices f g F I J V)
    [Algebra Γ(S, V) Γ(S', W)]
    (hAlgebra : algebraMap Γ(S, V) Γ(S', W) = (g.appLE V W eVW).hom) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (pullback (f ⁻¹ᵁ V).ι).obj F
    let T := baseChangedScheme (S := Γ(S', W)) h
    let A := baseChangedModule (S := Γ(S', W)) h N
    let G := (tensorPullback (pullback.snd g f)).obj F
    let U := (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
    let L := (pullback.fst g f) ⁻¹ᵁ W
    let e : L ≤ U := by
      change (pullback.fst g f) ⁻¹ᵁ W ≤ (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
      rw [flatBaseChangeOpenEquality f g V]
      exact (pullback.fst g f).preimage_mono eVW
    let M := (restrictFunctor L.ι).obj G
    let k := (pullback.fst g f).resLE W L le_rfl ≫ W.toSpecΓ
    let j := (Limits.pullback g f).homOfLE e
    let c := (restrictFunctorComp j U.ι).symm.app G ≪≫
      (restrictFunctorCongr ((Limits.pullback g f).homOfLE_ι e)).app G
    let r := (restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj G) ≫
      (pushforward j).map c.hom
    let q := (pullback.snd g f).resLE (f ⁻¹ᵁ V) U le_rfl
    let α := ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).hom
    ∃ (σ : L.toScheme ≅ T)
      (φ : A ⟶ (pushforward σ.hom).obj M)
      (ψ : M ⟶ (pushforward σ.inv).obj A),
      (φ ≫ (pushforward σ.hom).map ψ ≫ (pushforwardComp σ.inv σ.hom).hom.app A ≫
        (pushforwardCongr σ.inv_hom_id).hom.app A = (pushforwardId T).inv.app A) ∧
      (ψ ≫ (pushforward σ.inv).map φ ≫ (pushforwardComp σ.hom σ.inv).hom.app M ≫
        (pushforwardCongr σ.hom_inv_id).hom.app M =
          (pushforwardId L.toScheme).inv.app M) ∧
      (∀ a : Γ(S', W),
        A.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
          (baseChangeSnd (S := Γ(S', W)) h).appTop).hom a) ≫ φ =
        φ ≫ (pushforward σ.hom).map
          (M.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫ k.appTop).hom a))) ∧
      ∃ ef : σ.hom ≫ baseChangeFst (S := Γ(S', W)) h = j ≫ q,
        α ≫ baseChangeUnit (S := Γ(S', W)) h N ≫
          (pushforward (baseChangeFst (S := Γ(S', W)) h)).map φ ≫
          (pushforwardComp σ.hom (baseChangeFst (S := Γ(S', W)) h)).hom.app M ≫
          (pushforwardCongr ef).hom.app M =
        D.psi ≫ (pushforward q).map r ≫ (pushforwardComp j q).hom.app M := by sorry

end AlgebraicGeometry.Scheme.Modules
