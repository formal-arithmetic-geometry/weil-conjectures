/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.AffineClosedSepClosedSectionsExact
import Sheaf.AlgebraicGeometry.StrictLocalBaseGeometry
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Exact conservative sections on a geometric strict-local base

Source: Stacks Project, Tag 0EZV, corrected all-lifts proof, steps 1--4; Tags 09AY and 03PN.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Exactness follows from affine acyclicity; surjectivity of global germs makes
sections faithful, and a faithful functor out of an abelian category reflects isomorphisms.
Source: Stacks Project, Tags 09AY and 03PN; corrected Tag 0EZV proof, step 4.
(blueprint: lem-weil-pbc-strict-local-base-sections).
Proof: affine closed-point acyclicity makes the constant integer sheaf projective, so
its coyoneda functor Γ preserves finite colimits. If Γ sends two sheaf maps to the same
map, terminal evaluation sends them to the same map on global sections. Naturality
of global germs and their surjectivity then give equality of the maps on every geometric
stalk. The conservative family of geometric points is jointly faithful, hence the sheaf
maps coincide. A faithful functor reflects monomorphisms and epimorphisms. The sheaf
category is abelian, hence balanced, so Γ reflects isomorphisms. -/
theorem strictLocalBase_sections_exact_conservative
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (K : Type u) [Field K] [IsSepClosed K]
    (u : Spec (.of K) ⟶ Scheme.strictHenselizationScheme s) :
    let E := pullback (Scheme.strictHenselizationStructuralMap s)
      (u ≫ Scheme.strictHenselizationStructuralMap s)
    PreservesFiniteColimits (Sheaf.Γ E.smallEtaleTopology AddCommGrpCat.{u + 1}) ∧
      (Sheaf.Γ E.smallEtaleTopology AddCommGrpCat.{u + 1}).ReflectsIsomorphisms := by
  let E := pullback (Scheme.strictHenselizationStructuralMap s)
    (u ≫ Scheme.strictHenselizationStructuralMap s)
  obtain ⟨haffine, hclosed, hsep, hgerm⟩ := strictLocalBase_geometry s K u
  let : IsAffine E := haffine
  have hexact := Scheme.affineClosedSepClosed_sections_preservesFiniteColimits
    E hclosed hsep
  let Γ := Sheaf.Γ E.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : Γ.Faithful := by
    constructor
    intro F G φ ψ h
    have heval : φ.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 E))) =
        ψ.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 E))) := by
      let e := Sheaf.ΓNatIsoSheafSections E.smallEtaleTopology AddCommGrpCat.{u + 1}
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ E)
          (Scheme.Etale.mk (𝟙 E)) Over.mkIdTerminal)
      apply (cancel_epi (e.hom.app F)).mp
      calc
        _ = Γ.map φ ≫ e.hom.app G := (e.hom.naturality φ).symm
        _ = Γ.map ψ ≫ e.hom.app G := congrArg (fun z ↦ z ≫ e.hom.app G) h
        _ = _ := e.hom.naturality ψ
    apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro e
    let Φ := Scheme.pointSmallEtale (E.algClosurePoint e)
    let v : Φ.fiber.obj (Scheme.Etale.mk (𝟙 E)) :=
      Over.homMk (E.algClosurePoint e) (Category.comp_id _)
    let g := Φ.toPresheafFiber (Scheme.Etale.mk (𝟙 E)) v F.obj
    have : Epi g := (AddCommGrpCat.epi_iff_surjective g).mpr (hgerm F e)
    apply (cancel_epi g).mp
    change g ≫ Φ.presheafFiber.map φ.hom = g ≫ Φ.presheafFiber.map ψ.hom
    rw [Φ.toPresheafFiber_naturality, Φ.toPresheafFiber_naturality, heval]
  exact ⟨hexact, inferInstanceAs Γ.ReflectsIsomorphisms⟩

end AlgebraicGeometry.Etale
