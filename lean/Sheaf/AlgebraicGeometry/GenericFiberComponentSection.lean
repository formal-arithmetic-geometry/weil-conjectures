/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.AffineComponentSiteProjection
public import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The continuous section on generic-fibre components

Source: Hemo--Richarz--Scholbach, proof of Theorem 4.13, diagram (4.4).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every component of a flat scheme over an irreducible scheme meets the geometric
 generic fibre. Source: HRS Theorem 4.13, proof of (4.4); Stacks Tag 03H4
(blueprint: lem-zl-generic-fiber-component-section).

Proof: choose a point in the component. Going-down lifts the generic point to a
 generalization of that point. A point of the geometric point over the generic point
 then lifts with this generalization to the fibre product. Specializing points have
 the same connected component. This also handles an empty source. -/
private theorem generic_fiber_components_surjective
    (X : Scheme.{u}) [Nonempty X] [IrreducibleSpace X]
    (Ω : Type u) [Field Ω]
    (η : Spec (.of Ω) ⟶ X) (hη : ∀ x, η x = genericPoint X)
    {T : Scheme.{u}} (f : T ⟶ X) [Flat f] :
    Function.Surjective (pullback.fst f η).continuous.connectedComponentsMap := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, hyx, hy⟩ := Flat.generalizingMap f (genericPoint_specializes (f x))
  let z : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback y z
    (hy.trans (hη z).symm)
  refine ⟨ConnectedComponents.mk v, ?_⟩
  rw [Continuous.connectedComponentsMap_mk, hv]
  exact hyx.connectedComponents_mk_eq

/-- The geometric generic-fibre component map of an affine w-contractible scheme has
 a continuous section. Source: HRS Theorem 4.13, proof of (4.4)
(blueprint: lem-zl-generic-fiber-component-section).

Proof: the preceding going-down argument proves surjectivity. The affine spectrum
 homeomorphism transports extremal disconnectedness from the component space of the
 global-section ring. Gleason projectivity splits the continuous surjection of
 compact Hausdorff component spaces. The empty scheme causes no exception. -/
theorem generic_fiber_component_section
    (X : Scheme.{u}) [IsAffine X] [Nonempty X] [IrreducibleSpace X]
    (Ω : Type u) [Field Ω]
    (η : Spec (.of Ω) ⟶ X) (hη : ∀ x, η x = genericPoint X)
    (U : X.ProEt) [IsAffine U.left]
    (hw : IsWContractibleRing Γ(U.left, ⊤)) :
    let : IsAffineHom (show U.left ⟶ X from U.hom) :=
      isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
    let : IsAffineHom η := isAffineHom_of_isAffine η
    let : IsAffine (pullback U.hom η) :=
      instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
    let S := componentProfinite U.left
    let Sη := componentProfinite (pullback U.hom η)
    let r : C(Sη, S) :=
      ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
        (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
    ∃ s : C(S, Sη), Function.LeftInverse r s := by
  let := hw
  let : IsAffineHom (show U.left ⟶ X from U.hom) :=
      isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
  let : IsAffineHom η := isAffineHom_of_isAffine η
  let : IsAffine (pullback U.hom η) :=
    instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
  let S := componentProfinite U.left
  let Sη := componentProfinite (pullback U.hom η)
  let r : C(Sη, S) :=
    ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
      (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
  let e : U.left ≃ₜ PrimeSpectrum Γ(U.left, ⊤) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso U.left.isoSpec)
  let ec : ConnectedComponents U.left ≃ₜ
      ConnectedComponents (PrimeSpectrum Γ(U.left, ⊤)) :=
    e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (fun y ↦ by
      rw [show e ⁻¹' {y} = {e.symm y} by
        ext x
        exact (Equiv.eq_symm_apply e.toEquiv).symm]
      exact isConnected_singleton)
  have : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum Γ(U.left, ⊤))) :=
    IsWContractibleRing.extremallyDisconnected_connectedComponents
  have : ExtremallyDisconnected S := extremallyDisconnected_of_homeo ec.symm
  obtain ⟨s, hs, he⟩ := (CompactT2.ExtremallyDisconnected.projective (A := S))
    continuous_id r.continuous (generic_fiber_components_surjective X Ω η hη U.hom)
  exact ⟨⟨s, hs⟩, fun x ↦ congrFun he x⟩

end AlgebraicGeometry.Scheme.ProEt
