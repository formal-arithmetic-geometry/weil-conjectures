/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Algebra.Homology.Opposite
public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit

/-!
# Homotopic refinements induce the same maps on hypercover cohomology

A simplicial homotopy between refinements `f g : U ⟶ V` of finite split étale hypercovers
induces (via `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy` in the opposite
category) a chain homotopy between the induced maps `C(V, F) ⟶ C(U, F)` of complexes of
sections. Hence homotopic refinements induce equal maps on cohomology.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (A : Type w) [Category.{v} A] [Abelian A]

/-- The complex of sections of `F` over `U`, as the unop of the alternating face map complex
of the simplicial object `U ⋙ F.rightOp` of `Aᵒᵖ`. -/
noncomputable abbrev opComplex (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) : HomologicalComplex A (ComplexShape.down ℕ).symm :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).obj
    (op ((AlgebraicTopology.alternatingFaceMapComplex Aᵒᵖ).obj
      (U.simplicial ⋙ F.obj.rightOp)))

/-- The complex of sections of `F` over `U`. -/
noncomputable abbrev secCx (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) : CochainComplex A ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).obj (U.simplicial.rightOp ⋙ F.obj)

/-- The comparison of the two descriptions of the complex of sections. -/
noncomputable def opComplexIso (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) : opComplex A U F ≅ secCx A U F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    rintro i j (rfl : i + 1 = j)
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rw [show (secCx A U F).d i (i + 1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD _ i by
      simp [AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj],
      AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d]
    rfl)

end AlgebraicGeometry.FiniteSplitEtaleHypercover
