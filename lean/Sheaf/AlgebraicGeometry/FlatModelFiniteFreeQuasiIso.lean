module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Comparison part of the local finite-free replacement. Given the structural
local model, construct its quasi-isomorphism to the restricted complex.
Source: Stacks Project, Tags 06YD and 06YJ.
Proof: identify the truncated replacement with the original bounded flat complex
through the resolution quasi-isomorphism; pull the resulting map to the shrunken
open and use the flatness criterion to preserve quasi-isomorphisms. The omitted
comparison argument is exactly this named stage-3 intermediate theorem.
(blueprint: lem-pc-flat-model-finite-free-quasi-iso). -/
theorem exists_local_finiteFree_quasiIso {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T)
    (V : T.Opens) (hVU : V ≤ U) (P : CochainComplex V.toScheme.Modules ℤ)
    (hstruct : t ∈ V ∧ P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (P.X n ≅ SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))) :
    ∃ (eP : P ⟶ ((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj C),
      QuasiIso eP := by
  sorry

end AlgebraicGeometry.Scheme.Modules
