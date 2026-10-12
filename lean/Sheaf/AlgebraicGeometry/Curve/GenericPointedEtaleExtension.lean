/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Finite.Stalk
import Sheaf.Paper.EtaleFiniteDataDescent
import WeilConjectures.AlgebraicGeometry.FunctionFieldLimit
import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions

/-! # Extension of pointed étale neighbourhoods from the generic point

Source: Stacks Project, Tags 02GH and 07RP, and blueprint
`lem-sc-affine-generic-second`, proof paragraph 3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A pointed étale neighbourhood over the function field is dominated by a generic
fibre of a pointed étale neighbourhood over the integral scheme.

Source: Stacks Project, Tags 02GH (standard étale presentations) and 07RP;
blueprint `lem-sc-affine-generic-second`, proof paragraph 3.
(blueprint: lem-sc-generic-pointed-etale-extension)

Proof: Restrict the given neighbourhood to an affine standard étale neighbourhood
of the marked point. Choose a nonempty affine open Spec A of D; its fraction field
is K. A standard étale presentation over K uses finitely many coefficients,
including coefficients witnessing invertibility of the derivative. Clear all
denominators and localize A at their nonzero product. The resulting standard
étale algebra over this localization has generic fibre equal to the chosen
standard étale K-algebra. Compose its spectrum with the open immersion into D.
Through the generic-fibre identification, the original geometric marking lifts
to this fibre. Its composite with projection to the extended neighbourhood is a
marking above the given geometric point of D. The canonical identification of
its base-changed marking with the pair of these two markings gives a morphism
in the category of pointed neighbourhoods to the original neighbourhood.
This construction only needs an affine neighbourhood of the marking, so the
original neighbourhood need not be quasi-compact or separated. -/
theorem exists_hom_generic_baseChangeNbhd
    (D : Scheme.{u}) [IsIntegral D]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec D.functionField)
    (d : (pointSmallEtale s).fiber.Elements) :
    ∃ c, Nonempty ((Etale.baseChangeNbhd D.fromSpecFunctionField
      (s ≫ D.fromSpecFunctionField) ⟨s, rfl⟩).obj c ⟶ d) := by
  classical
  -- Restrict to an affine neighbourhood of the marking.
  obtain ⟨W, w⟩ := d
  obtain ⟨U, hU, hwU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := w.left (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
  obtain ⟨w₀, hw₀⟩ := exists_pointSmallEtale_fiber_ofOpens s w U (by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint Ω :=
      @Subsingleton.elim (Spec (.of Ω)) _ x (IsLocalRing.closedPoint Ω)
    exact hx ▸ hwU)
  let W₀ := Etale.ofOpens W U
  have : IsAffine W₀.left := hU
  have : IsAffineHom W₀.hom :=
    @isAffineHom_of_isAffine W₀.left (Spec D.functionField) W₀.hom ‹IsAffine W₀.left›
      (inferInstanceAs (IsAffine (Spec D.functionField)))
  have : QuasiCompact W₀.hom := by infer_instance
  have : QuasiSeparated W₀.hom := by infer_instance
  -- Reindex the proved generic-point limit to the directed-set descent API.
  let e := (orderDualEquivalence D.NonemptyAffineOpens).op.trans
    (opOpEquivalence D.NonemptyAffineOpens)
  let S := e.functor ⋙ D.affineOpensDiagram
  let c := D.functionFieldCone.whisker e.functor
  have hc : Limits.IsLimit c := D.isLimitFunctionFieldCone.whiskerEquivalence e
  have : ∀ i, IsAffine (S.obj i) := fun i ↦ inferInstanceAs
    (IsAffine (Spec (Γ(D, (e.functor.obj i).1))))
  have : ∀ {i j} (f : i ⟶ j), IsAffineHom (S.map f) := fun f ↦ by infer_instance
  have : ∀ i, CompactSpace (S.obj i) := fun i ↦ by infer_instance
  have : ∀ i, QuasiSeparatedSpace (S.obj i) := fun i ↦ by infer_instance
  -- Only the object-descent clause is needed.
  obtain ⟨i, V, hV, ⟨α⟩⟩ := (etale_finite_data_descent.{u, u} S c hc).1
    (Over.mk W₀.hom) (by
      change Etale W₀.hom ∧ LocallyOfFinitePresentation W₀.hom ∧
        QuasiCompact W₀.hom ∧ QuasiSeparated W₀.hom
      have : Etale W₀.hom := W₀.prop
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩)
  have := hV.1
  let j := D.affineOpensDiagramι.app (e.functor.obj i)
  let q := V.hom ≫ j
  have : IsOpenImmersion j := (e.functor.obj i).2.1.isOpenImmersion_fromSpec
  have : Etale q := by dsimp [q]; infer_instance
  have hj : c.π.app i ≫ j = D.fromSpecFunctionField :=
    (D.fromSpecFunctionField_eq_functionFieldCone_comp (e.functor.obj i)).symm
  -- Transport the marking through the generic-fibre isomorphism.
  let z := w₀.left ≫ α.inv.left
  have hz : z ≫ Limits.pullback.snd V.hom (c.π.app i) = s := by
    dsimp [z]
    change w₀.left ≫ α.inv.left ≫ ((Over.pullback (c.π.app i)).obj V).hom = s
    rw [Over.w α.inv]
    exact Over.w w₀
  let v := z ≫ Limits.pullback.fst V.hom (c.π.app i)
  have hv : v ≫ q = s ≫ D.fromSpecFunctionField := by
    change (z ≫ Limits.pullback.fst V.hom (c.π.app i)) ≫ (V.hom ≫ j) = _
    rw [Category.assoc, Limits.pullback.condition_assoc, ← Category.assoc, hz, hj]
  let b : (pointSmallEtale (s ≫ D.fromSpecFunctionField)).fiber.Elements :=
    ⟨Scheme.Etale.mk q, Over.homMk v hv⟩
  -- Compare the two pullbacks after composing with the open immersion j.
  let g : Limits.pullback q D.fromSpecFunctionField ⟶
      Limits.pullback V.hom (c.π.app i) :=
    Limits.pullback.lift (Limits.pullback.fst q D.fromSpecFunctionField)
      (Limits.pullback.snd q D.fromSpecFunctionField) (by
        apply (cancel_mono j).mp
        rw [Category.assoc, Category.assoc, hj]
        exact Limits.pullback.condition)
  have hg : g ≫ Limits.pullback.snd V.hom (c.π.app i) =
      Limits.pullback.snd q D.fromSpecFunctionField := Limits.pullback.lift_snd _ _ _
  let ρ := g ≫ α.hom.left ≫ U.ι
  have hρ : ρ ≫ W.hom = Limits.pullback.snd q D.fromSpecFunctionField := by
    change (g ≫ α.hom.left ≫ (Over.mk W₀.hom).hom) = _
    rw [Over.w α.hom]
    exact hg
  refine ⟨b, ⟨CategoryOfElements.homMk _ _ (MorphismProperty.Over.homMk ρ hρ) ?_⟩⟩
  apply Over.OverMorphism.ext
  change Scheme.Hom.basePt D.fromSpecFunctionField b ⟨s, rfl⟩ ≫ ρ = w.left
  -- The canonical base-changed marking maps to the transported marking.
  have hp : Scheme.Hom.basePt D.fromSpecFunctionField b ⟨s, rfl⟩ ≫ g = z := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]
      exact Scheme.Hom.basePt_fst D.fromSpecFunctionField b ⟨s, rfl⟩
    · rw [Category.assoc, hg, hz]
      exact Scheme.Hom.basePt_snd D.fromSpecFunctionField b ⟨s, rfl⟩
  dsimp [ρ]
  rw [← Category.assoc, hp]
  have hzα : z ≫ α.hom.left = w₀.left := by
    dsimp [z]
    have hα := congrArg Over.Hom.left α.inv_hom_id
    change α.inv.left ≫ α.hom.left = 𝟙 _ at hα
    rw [Category.assoc, hα]
    exact Category.comp_id w₀.left
  rw [← Category.assoc, hzα]
  exact congrArg (fun t ↦ t.left) hw₀

end AlgebraicGeometry.Scheme
