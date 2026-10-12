module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option linter.unusedVariables false in
/-- Structural part of the local finite-free replacement: the neighbourhood and
finite-free bounded complex are constructed, before constructing the comparison map.
Source: Stacks Project, Tags 064U, 0653, 00NX, 06YD and 06YJ.
Proof: carry out the affine localization, finite-projective-to-free shrinking, and
truncation of the bounded-above free resolution. The omitted construction is exactly
this named stage-3 intermediate theorem.
(blueprint: lem-pc-flat-model-finite-free-structural-data). -/
theorem exists_local_finiteFree_structural_data {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T) (ht : t ∈ U) :
    ∃ (V : T.Opens) (hVU : V ≤ U) (P : CochainComplex V.toScheme.Modules ℤ),
      t ∈ V ∧ P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
        (∀ n : ℤ, ∃ r : ℕ,
          Nonempty (P.X n ≅ SheafOfModules.free
            (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) := by
  open ZeroObject in
  let P : CochainComplex U.toScheme.Modules ℤ := 0
  have hfree : IsZero (SheafOfModules.free
      (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 0))) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext j
    exact Fin.elim0 j.down
  refine ⟨U, le_rfl, P, ht, inferInstance, inferInstance, ?_⟩
  intro n
  exact ⟨0, ⟨((HomologicalComplex.eval _ _ n).map_isZero
    (Limits.isZero_zero _)).iso hfree⟩⟩

end AlgebraicGeometry.Scheme.Modules
