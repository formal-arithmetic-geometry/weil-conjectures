/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.Paper.FiniteProjectiveTensorProducts
public import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
/-! # Ordinary finite reduction as tensor with the quotient complex

Source: finite reduction of reconstruction, order 1249, coefficient-comparison step;
Stacks Project, Modules on Sites, Tag 05V4, and Cohomology on Sites, Tag 06YU.
(blueprint: lem-weil-pbc-completed-reduction-ordinary-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)
private theorem completedReductionOrdinaryModuleComparison
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (E : completedConstantModules T R ⥤ completedConstantModules T S)
    (hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    Nonempty (E ⋙ SheafOfModules.restrictScalars ((adicLisseForget T).map φ) ≅
      tensorLeft ((SheafOfModules.restrictScalars ((adicLisseForget T).map φ)).obj
        (SheafOfModules.unit ((adicLisseForget T).obj S)))) := by
  let U := SheafOfModules.restrictScalars ((adicLisseForget T).map φ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory S
  obtain ⟨e, he⟩ := SheafOfModules.exists_changeOfRings_tensorCancellation φ
  have hu : (SheafOfModules.monoidalCategory S).tensorUnit =
      SheafOfModules.unit ((adicLisseForget T).obj S) := by rfl
  let j (M : completedConstantModules T R) :
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M ≅
        (SheafOfModules.monoidalCategory S).tensorObj
          (SheafOfModules.unit ((adicLisseForget T).obj S))
          (SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M) := by
    exact ((SheafOfModules.monoidalCategory S).leftUnitor _).symm
  let i (M : completedConstantModules T R) : U.obj (E.obj M) ≅
      (U.obj (SheafOfModules.unit ((adicLisseForget T).obj S))) ⊗ M :=
    U.mapIso (eqToIso (hobj M)) ≪≫
      U.mapIso (j M) ≪≫
        e (SheafOfModules.unit ((adicLisseForget T).obj S)) M
  refine ⟨NatIso.ofComponents i ?_⟩
  intro M N f
  change U.map (E.map f) ≫ (i N).hom = (i M).hom ≫ _
  have hEf : E.map f ≫ (eqToIso (hobj N)).hom =
      (eqToIso (hobj M)).hom ≫ SheafOfModules.changeOfRingsHom φ M f := by
    have hm : E.map f = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm := hmap f
    rw [hm]
    simp
  have hUf := congrArg U.map hEf
  simp only [Functor.map_comp] at hUf
  have hj : SheafOfModules.changeOfRingsHom φ M f ≫ (j N).hom =
      (j M).hom ≫ (SheafOfModules.monoidalCategory S).tensorHom (𝟙 _)
        (SheafOfModules.changeOfRingsHom φ M f) := by
    dsimp only [j, Iso.symm_hom]
    convert (@MonoidalCategory.leftUnitor_inv_naturality
      (SheafOfModules ((adicLisseForget T).obj S)) _
      (SheafOfModules.monoidalCategory S) _ _
      (SheafOfModules.changeOfRingsHom φ M f)) using 1 <;>
      (try simp only [id_tensorHom]) <;> rfl
  have hUj := congrArg U.map hj
  simp only [Functor.map_comp] at hUj
  dsimp only [i, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hUf, reassoc_of% hUj]
  have hc := he (𝟙 (SheafOfModules.unit ((adicLisseForget T).obj S))) f
  change U.map ((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _)
      (SheafOfModules.changeOfRingsHom φ M f)) ≫
      (e (SheafOfModules.unit ((adicLisseForget T).obj S)) N).hom =
      (e (SheafOfModules.unit ((adicLisseForget T).obj S)) M).hom ≫
        ((SheafOfModules.monoidalCategory R).tensorHom (U.map (𝟙 _)) f) at hc
  rw [U.map_id] at hc
  have hh := @MonoidalCategory.id_tensorHom
    (completedConstantModules T R) _ (SheafOfModules.monoidalCategory R)
    (U.obj (SheafOfModules.unit ((adicLisseForget T).obj S))) _ _ f
  rw [hh] at hc
  convert congrArg
    (fun a ↦ U.map (eqToIso (hobj M)).hom ≫ U.map (j M).hom ≫ a) hc using 1
  rfl
/-- Tensor with the quotient in degree zero computes ordinary scalar extension
followed by restriction, naturally on all complexes, before taking its left derived
functor. Localization in the codomain preserves this natural isomorphism.

Source: finite reduction of reconstruction, order 1249, coefficient-comparison step;
Stacks Project, Tags 05V4 and 06YU.
(blueprint: lem-weil-pbc-completed-reduction-ordinary-tensor-comparison).

Proof: apply change-of-rings tensor cancellation to the quotient unit module. The
left unitor identifies its scalar extension with the regular quotient module. Use
the object and morphism specifications of the chosen ordinary extension functor to
transport this to its actual composite with restriction. Cancellation naturality
and left-unitor naturality prove that the components form a natural isomorphism.
Symmetry places the quotient in the right tensor factor. Apply the natural
isomorphism for total tensor with a degree-zero complex, then the termwise lift of
the ordinary comparison, and finally postcompose with localization. There is only
one nonzero summand on every total diagonal, so this holds for unbounded input
complexes. No quotient-flatness, nonzero-ring, or nonempty-site assumption is used. -/
theorem completedReductionOrdinaryTensorComparison (n : ℕ) :
    ∃ h : (adicDatumOrdinaryReduction T d n).Additive,
      Nonempty (finiteProjectiveTensorComplexRight T d
        ((CochainComplex.singleFunctor (adicDatumModules T d) 0).obj
          (CompletedConstantReduction.residue T d.ideal n)) ≅
        completedConstantMapComplex (adicDatumOrdinaryReduction T d n) h ⋙
          completedConstantQ _) := by
  let R := adicDatumRing T d
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have h : (adicDatumOrdinaryReduction T d n).Additive := by
    dsimp only [adicDatumOrdinaryReduction]
    infer_instance
  let := h
  let φ := adicDatumProjection T d n
  let E := completedConstantExtension T φ
  have h := (SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ).choose_spec
  change ∃ (h : ∀ M, E.obj M = SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M), _ at h
  obtain ⟨hobj, hmap, _, _⟩ := h
  obtain ⟨e⟩ := completedReductionOrdinaryModuleComparison T φ E hobj hmap
  let e' := e ≪≫
    BraidedCategory.tensorLeftIsoTensorRight (CompletedConstantReduction.residue T d.ideal n)
  have : (tensorRight (CompletedConstantReduction.residue T d.ideal n)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso e'
  refine ⟨h, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight
    ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor _)
      (CompletedConstantReduction.residue T d.ideal n)) ≪≫
        (NatIso.mapHomologicalComplex e' (.up ℤ)).symm) (completedConstantQ _)

end AlgebraicGeometry.Scheme
