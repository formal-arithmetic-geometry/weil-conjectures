/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

import Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent
import Sheaf.AlgebraicGeometry.ProperFlatSingleLocalFiniteTor
import Sheaf.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension
import Sheaf.AlgebraicGeometry.OpenRestrictionPerfectLocalModels
import Mathlib.CategoryTheory.Localization.Equivalence

/-! # Perfection of the direct image of a relatively flat single module

Source: Stacks Project, Tag 0B91(2), via the proof of Tag 0A1H.
(blueprint: lem-pc-proper-flat-single-derived-direct-image-perfect).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wS

open CategoryTheory

namespace AlgebraicGeometry

open CategoryTheory.Functor in
/-- Transport a localization along an exact equivalence in the same morphism universe. -/
private theorem hasDerivedCategory_of_equivalence {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{wS} D] : Nonempty (HasDerivedCategory.{wS} C) := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := eC.functor ⋙ (DerivedCategory.Q (C := D))
  have : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    refine Functor.IsLocalization.of_equivalence_source
      (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) eC.symm ?_ ?_ ?_
    · intro K M f hf
      have : QuasiIso f := hf
      exact (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).le_isoClosure _
        (show QuasiIso (eC.inverse.map f) from
          (show QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            from inferInstance))
    · intro K M f hf
      have : QuasiIso f := hf
      have : QuasiIso (eC.functor.map f) :=
        (show QuasiIso ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          from inferInstance)
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (eC.functor.map f)))
    · exact (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  exact ⟨{ D := DerivedCategory D, L := L }⟩

set_option backward.isDefEq.respectTransparency false in
/-- Module restriction along inverse scheme isomorphisms gives an exact equivalence. -/
private noncomputable def restrictIsoEquivalence {Y Z : Scheme.{u}} (s : Y ≅ Z) :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) :=
  CategoryTheory.Equivalence.mk
    (Scheme.Modules.restrictFunctor s.inv) (Scheme.Modules.restrictFunctor s.hom)
    ((Scheme.Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr s.hom_inv_id ≪≫
        Scheme.Modules.restrictFunctorId).symm
    ((Scheme.Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr s.inv_hom_id ≪≫
        Scheme.Modules.restrictFunctorId)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper direct image of a finitely presented, relatively flat module is perfect.
This statement has no Čech cover, specified section model or base-change conclusion.
Source: Stacks Project, Tag 0B91(2), using Tag 0A1H.
(blueprint: lem-pc-proper-flat-single-derived-direct-image-perfect).

Proof: work locally on an affine base Spec A. Express A as a filtered colimit of
finitely generated Z-algebras. Finite presentation spreads out X and F to a
Noetherian stage; enlarge the stage so the morphism is proper and the module is
flat over that stage. On this Noetherian stage proper coherence gives bounded
coherent direct-image cohomology. Relative flatness gives finite relative Tor
amplitude for the single module, and proper pushforward preserves the resulting
finite Tor dimension. Bounded coherent cohomology and finite Tor dimension give
a perfect direct image there. The relatively flat cohomology-and-base-change
comparison identifies its derived pullback with the direct image over A. Pulling
back a local bounded finite-projective representative gives a strictly perfect
representative on the base. Glue the local witnesses. This is the specialization
E=O_X and G=F[0] of the argument of 0A1H used in 0B91(2), and requires no flatness
of f itself. Compute and transport the direct image by localization uniqueness
so these witnesses lie in the supplied source, base and open-site localizations;
no family of localizations for all schemes is assumed. Empty schemes and the
zero module give the zero strictly perfect representative. -/
theorem properFlat_single_derivedDirectImage_perfect
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens, HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f) :
    S.IsPerfect ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) := by
  classical
  intro x
  have hneigh : ∃ U : S.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hx⟩
  obtain ⟨U, hU, hx⟩ := hneigh
  let hD : HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    Classical.choice (hasDerivedCategory_of_equivalence (Scheme.Modules.overEquiv U).symm)
  have hopen (V : U.toScheme.Opens) : Nonempty (HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))) := by
    let A := U.ι ''ᵁ V
    let e := ((Scheme.Modules.overEquiv V).trans
      (restrictIsoEquivalence (U.ι.isoImage V))).trans (Scheme.Modules.overEquiv A).symm
    exact hasDerivedCategory_of_equivalence e
  let hO : ∀ V : U.toScheme.Opens, HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V)) :=
    fun V ↦ Classical.choice (hopen V)
  have hpc := properFlat_single_open_isPseudoCoherent f F hF U
  have hTor := properFlat_single_local_hasFiniteTorDimension f F hF U hU
  have hp := Scheme.isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension
    U.toScheme _ hpc hTor
  exact Scheme.open_restriction_perfect_local_models S U _ hp x hx

end AlgebraicGeometry
