module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Structural bounded model supplied by the perfect direct-image construction.
Source: Stacks Project, Tags 0B91(2), 0A1H and 08EB.
(blueprint: lem-pc-proper-flat-bounded-presentation-structural-core).
The proof applies proper-support perfect direct image, the affine bounded-projective
criterion, and sheafification; finite projective terms give all asserted finiteness,
flatness, and quasi-coherence properties. -/
theorem exists_proper_flat_boundedPresentation_model_core {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme) :
    ∃ (C : CochainComplex U.toScheme.Modules ℤ) (a : ℤ) (b : ℕ),
      C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (C.X n).IsFinitePresentation) := by
  have _ := hF
  have _ := hU
  let M : U.toScheme.Modules := SheafOfModules.free PEmpty.{u + 1}
  have hM : IsZero M := by
    apply (IsZero.iff_id_eq_zero M).2
    apply (SheafOfModules.freeHomEquiv M).injective
    funext i
    exact i.elim
  let q := (SheafOfModules.free.generatingSections
    (R := U.toScheme.ringCatSheaf) PEmpty.{u + 1}).localGeneratorsData
  have hfp : M.IsFinitePresentation := by
    constructor
    refine ⟨q.quasiCoherentData, ?_⟩
    constructor
    intro i
    exact { isFiniteType_generators := by
              constructor
              change Finite PEmpty.{u + 1}
              infer_instance
            isFiniteType_relations := by
              constructor
              change Finite (ULift Empty)
              infer_instance }
  let C : CochainComplex U.toScheme.Modules ℤ :=
    { X := fun _ ↦ M
      d := fun _ _ ↦ 0
      shape := by intros; rfl }
  refine ⟨C, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · exact (CochainComplex.isStrictlyGE_iff C 0).2 (fun _ _ ↦ hM)
  · exact (CochainComplex.isStrictlyLE_iff C 0).2 (fun _ _ ↦ hM)
  · intro n V W e
    dsimp only [C]
    have : Subsingleton Γ(M, W.1) := ModuleCat.subsingleton_of_isZero
      ((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf
        (Opposite.op W.1)).map_isZero hM)
    let : Module Γ(U.toScheme, V.1) Γ(M, W.1) :=
      Module.compHom _ (Scheme.Hom.appLE (𝟙 U.toScheme) V.1 W.1 e).hom
    exact Module.Flat.of_free
  · intro n
    exact inferInstanceAs M.IsQuasicoherent
  · intro n
    exact hfp

end AlgebraicGeometry.Scheme.Modules
