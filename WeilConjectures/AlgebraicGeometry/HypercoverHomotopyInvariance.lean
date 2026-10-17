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
    rw [show (secCx A U F).d i (i + 1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (U.simplicial.rightOp ⋙ F.obj) i by
      simp [secCx, AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj],
      AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d]
    rw [show (opComplex A U F).d i (i + 1) = (AlgebraicTopology.AlternatingFaceMapComplex.objD
        (U.simplicial ⋙ F.obj.rightOp) i).unop from
      congrArg Quiver.Hom.unop
        (AlgebraicTopology.alternatingFaceMapComplex_obj_d (U.simplicial ⋙ F.obj.rightOp) i)]
    rfl)

/-- The map of complexes of sections induced by a refinement. -/
noncomputable abbrev secCxMap {U V : FiniteSplitEtaleHypercover X} (f : U.Refinement V)
    (F : Sheaf X.smallEtaleTopology A) : secCx A V F ⟶ secCx A U F :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).map
    (Functor.whiskerRight (NatTrans.rightOp f) F.obj)

lemma secCxMap_eq {U V : FiniteSplitEtaleHypercover X} (f : U.Refinement V)
    (F : Sheaf X.smallEtaleTopology A) :
    secCxMap A f F = (opComplexIso A V F).inv ≫
      (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
        ((AlgebraicTopology.alternatingFaceMapComplex Aᵒᵖ).map
          (((SimplicialObject.whiskering _ _).obj F.obj.rightOp).map f)).op ≫
      (opComplexIso A U F).hom := by
  ext n
  simp [opComplexIso]
  erw [Category.id_comp, Category.comp_id]

variable [CategoryWithHomology A]

lemma homologyMap_secCxMap_eq {U V : FiniteSplitEtaleHypercover X} {f g : U.Refinement V}
    (H : SimplicialObject.Homotopy f g) (F : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    HomologicalComplex.homologyMap (secCxMap A f F) q =
      HomologicalComplex.homologyMap (secCxMap A g F) q := by
  have CH := ((H.whiskerRight F.obj.rightOp).toChainHomotopy).unop
  rw [secCxMap_eq, secCxMap_eq, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, CH.homologyMap_eq]

/-- Blueprint `thm-weil-pbc-hypercover-cohomology` (homotopy invariance): homotopic refinements
induce equal maps on hypercover cohomology. -/
lemma cohomologyRefinement_eq_of_isRefinementHomotopic {U V : FiniteSplitEtaleHypercover X}
    {f g : U.Refinement V} (h : isRefinementHomotopic f g) (q : ℕ) :
    cohomologyRefinement A f q = cohomologyRefinement A g q := by
  induction h with
  | rel a b hab =>
    obtain ⟨H⟩ := hab
    ext F
    exact homologyMap_secCxMap_eq A H F q
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end AlgebraicGeometry.FiniteSplitEtaleHypercover
