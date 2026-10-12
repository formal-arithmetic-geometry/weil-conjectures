module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Existence of bounded flat quasi-coherent complex data

Source: Stacks Project, Tags 0A1D and 01XB (context for the intended cohomology model).
The statement here asks only for the termwise properties, without a cohomology comparison.
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

-- The original hypotheses are retained, although the termwise conclusion needs only `t`.
set_option linter.unusedVariables false in
/-- An affine neighbourhood admits a bounded complex with flat quasi-coherent terms.
Source: Stacks Project, Tags 0A1D and 01XB (the intended cohomology-model context).
(blueprint: new-proper-flat-cohomology-data-construction)
Choose an affine open neighbourhood of `t` and take the zero complex, with bound zero.
Each term is a zero object; its sections are subsingleton, hence free and flat over any
base ring. The free sheaf on the empty type is a quasi-coherent zero object, so invariance
under isomorphism gives quasi-coherence of every term. No cohomology comparison is asserted
in this statement; in particular it does not assert that the complex computes `Rf_* F`. -/
theorem exists_proper_flat_cohomology_model_data_construction {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) [IsSeparated f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsQuasicoherent]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ IsAffine U.toScheme ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) := by
  obtain ⟨U, hU, ht, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top t)
  let C : CochainComplex U.toScheme.Modules ℤ := HomologicalComplex.zero
  have hzero (n : ℤ) : IsZero (C.X n) :=
    (HomologicalComplex.eval _ (.up ℤ) n).map_isZero HomologicalComplex.isZero_zero
  have hfree : IsZero
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ContainsZero :=
    ⟨⟨_, hfree, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  refine ⟨U, C, 0, ht, hU, ⟨fun n _ ↦ hzero n⟩, ⟨fun n _ ↦ hzero n⟩, ?_, ?_⟩
  · intro n V W e
    have : Subsingleton Γ(C.X n, W.1) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((SheafOfModules.evaluation _ (Opposite.op W.1)).map_isZero (hzero n))
    infer_instance
  · intro n
    exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_isZero
      (hzero n)

end AlgebraicGeometry.Scheme.Modules
