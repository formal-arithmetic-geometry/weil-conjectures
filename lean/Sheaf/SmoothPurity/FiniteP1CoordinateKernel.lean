/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import Sheaf.AlgebraicGeometry.SfDiagonalKernelIntegrals
import Sheaf.AlgebraicGeometry.SfP1IntegralTransport
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Changing coordinates in the finite projective-line diagonal integrals

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the diagonal kernel and its two coordinate traces.
(blueprint: lem-sp-finite-p1-coordinate-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable def renameGraded {σ τ : Type u} (e : σ ≃ τ) :
    MvPolynomial.homogeneousSubmodule σ (ULift.{u} ℤ) →+*ᵍ
      MvPolynomial.homogeneousSubmodule τ (ULift.{u} ℤ) where
  __ := (MvPolynomial.renameEquiv (ULift.{u} ℤ) e).toRingEquiv.toRingHom
  map_mem := fun h ↦ h.rename_isHomogeneous

private theorem rename_irrelevant {σ τ : Type u} (e : σ ≃ τ) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule τ (ULift.{u} ℤ)) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule σ (ULift.{u} ℤ))).map (renameGraded e) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule,
    MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h := Ideal.mem_map_of_mem (renameGraded e)
    (Ideal.subset_span (Set.mem_range_self (f := MvPolynomial.X) (e.symm i)))
  simpa [renameGraded] using h

private noncomputable def renameProjIso {σ τ : Type u} (e : σ ≃ τ) :
    Proj.projectiveSpaceOverAffine τ (ULift.{u} ℤ) ≅
      Proj.projectiveSpaceOverAffine σ (ULift.{u} ℤ) where
  hom := Proj.map (renameGraded e) (rename_irrelevant e)
  inv := Proj.map (renameGraded e.symm) (rename_irrelevant e.symm)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (renameGraded e).comp (renameGraded e.symm) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule τ (ULift.{u} ℤ)) := by
      ext i
      simp [renameGraded]
    simp only [h, Proj.map_id, Proj.projectiveSpaceOverAffine]
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h : (renameGraded e.symm).comp (renameGraded e) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule σ (ULift.{u} ℤ)) := by
      ext i
      simp [renameGraded]
    simp only [h, Proj.map_id, Proj.projectiveSpaceOverAffine]

@[irreducible]
private noncomputable def p1CoordinateIso (S : Scheme.{u}) :
    ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ≅ ProjectiveLine S := by
  let e : ULift.{u} (Fin 2) ≃ Option (ULift.{u} (Fin 1)) :=
    Equiv.ulift.trans ((finSuccEquiv 1).trans (Equiv.optionCongr Equiv.ulift.symm))
  let i := renameProjIso e
  exact asIso (pullback.map _ _ _ _ (𝟙 S) i.hom (𝟙 _)
    (by simp) (by simp))

private theorem p1CoordinateIso_over (S : Scheme.{u}) :
    (p1CoordinateIso S).hom ≫ (ProjectiveLine S ↘ S) =
      (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S) := by
  change _ ≫ pullback.fst _ _ = pullback.fst _ _
  simp only [p1CoordinateIso, asIso_hom, pullback.map, pullback.lift_fst,
    Category.comp_id]

private theorem conjugate_identity
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U : C} {V : D} (c : F.obj U ≅ V) (g : U ⟶ U) (hg : g = 𝟙 U) :
    c.inv ≫ F.map g ≫ c.hom = 𝟙 V := by
  rw [hg, F.map_id, Category.id_comp, c.inv_hom_id]

/-- Express the supplied finite projective-line integrals in the trace-diagonal
conventions for the standard-chart coordinates. The conclusion concerns only
coefficient objects and degree-zero integral equations, with no triangle identity
or adjunction on arbitrary complexes.

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the supported diagonal
and the identification of both coordinate traces by base change.
(blueprint: lem-sp-finite-p1-coordinate-kernel).

Proof in words: send none to the first homogeneous coordinate and some of the
unique element of ULift (Fin 1) to the second. Renaming the polynomial variables
and its inverse preserve total degree. Their Proj morphisms are inverse and
base change gives an isomorphism eP from the standard-chart P to ProjectiveLine S
over S. The induced isomorphism on the self-products carries each projection and
the diagonal to its counterpart. Pull back (d S hS).trace and the supported class
witnessed by hi S hS through these isomorphisms. Use the canonical proper
forget-supports isomorphism to express them as the trace and diagonalClass fields
of TraceDiagonalDatum. The target of diagonalClass is the second pullback of B:
identify the finite line on the self-product using t.line and its shifted
comparison. The same comparison along P -> S gives the coefficient isomorphism e.
For either projection, the trace equation of hbc along ProjectiveLine S -> S,
composed with the projective-line diagonal-chart comparison, says that its trace
is inverse proper exchange followed by pullback of the original trace. For the
second projection use the common-base pullback comparison to change the target
from the first to the second coefficient pullback. These are precisely traceFirst
and traceSecond. The derived direct-image composition maps carry the canonical
alpha for p_i Delta = id to diagonalFirst and idIsoDiagonalSnd. Substitute the
transported supported class into each integral equation in hi S hS. Naturality
of proper exchange and composition cancels each adjacent comparison with its
inverse, giving the two equations in Integrals for the same datum. This is
conjugation of morphism equalities by isomorphisms, so uses neither detection of
arbitrary derived arrows on a cover nor a boundedness assertion. It also applies
to the empty base and zero coefficient ring. -/
theorem finiteP1CoordinateKernel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    (hi : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      finiteP1DiagonalProperty A N hA t d T hT)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ k : TraceDiagonalDatum A
        (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
        (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine
            ℙ(Option (ULift.{u} (Fin 1)); S) N A hA))⟦(2 : ℤ)⟧),
      ∃ e : (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine
            ℙ(Option (ULift.{u} (Fin 1)); S) N A hA))⟦(2 : ℤ)⟧) ≅
        (CoordinateTrace.pull A (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).obj
          (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1),
        SfDiagonalKernel.Integrals A k
          (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1) e := by
  classical
  obtain ⟨hI, κ, hκ, hκintegrals⟩ := hi S hS
  obtain ⟨k, c, hfirst, hsecond⟩ := sfP1IntegralTransport A N hA t d hbc S
    ℙ(Option (ULift.{u} (Fin 1)); S) (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
    (p1CoordinateIso S) (p1CoordinateIso_over S) hS κ
  refine ⟨k, (ordinaryFiniteShiftedLinePullback A N hA t _ hS).symm, ?_⟩
  constructor
  · exact hfirst.trans (conjugate_identity _ c _ (hκintegrals false).2)
  · exact hsecond.trans (conjugate_identity _ c _ (hκintegrals true).2)

end AlgebraicGeometry.Etale
