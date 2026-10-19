/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import Sheaf.AlgebraicGeometry.Modules.LocalBlockResidueRank
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Fibrewise vanishing of the complementary block -/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- At one point, the rank bound kills the complementary matrix in the residue field.
No reducedness assumption is needed.

Source: `thm-pc-semicontinuity-base-change`, proof (3), reduced-ring normal form,
rank calculation before the reducedness argument.
(blueprint: lem-pc-complementary-block-residue-vanishes)

Proof: Choose R and g in hrank and give R its field structure. The spectrum of R is a
singleton, and its image j(x) lies in the image of the composite open immersion U→Z→Y.
The universal property of an open immersion gives a lift h:Spec R→U with h≫U.ι≫j=g.
Pull back hform along h. Pullback commutes with biproducts, and the comparison between
restriction and pullback identifies the pulled-back left side with g*φ. The chosen
bases and their pullbacks are isomorphisms, so they preserve the image dimension.
The pulled-back f remains invertible on an a-dimensional free module. On global
sections over Spec R, the image of diag(f,δ) is the direct sum of the full first
summand and the image of δ. Therefore its dimension is a plus the dimension of the
image of δ. The upper bound a forces the latter dimension to be zero; finite
-dimensionality makes this linear map zero, so every pulled-back matrix entry is zero.
The residue-field naturality square identifies evaluation at x followed by the
residue-field map of h with pullback followed by evaluation at the unique point
of Spec R. The residue-field map is a unital homomorphism of fields and is injective.
Thus every entry already evaluates to zero in κ(x), proving the matrix equality.
The argument handles a=0 and empty complementary indices. There is no point x when
U is empty, so no nonemptiness assumption on U is needed. -/
theorem complementary_block_residue_eq_zero_of_rank_le
    {Y Z : Scheme.{u}} {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ) (U : Z.Opens)
    (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (m - a))))
    (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a))))
    (f : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin a)) ⟶
      free (ULift.{u} (Fin a))) [IsIso f]
    (δ : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (m - a))) ⟶
      free (ULift.{u} (Fin (n - a))))
    (hform : (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
      eS.hom ≫ biprod.map f δ ≫ eT.inv)
    (x : U.toScheme)
    (hrank : ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base x.1} ∧
      ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank ≤ a) :
    (freeMatrix δ).map (U.toScheme.Γevaluation x) = 0 := by
  classical
  obtain ⟨R, hR, g, himage, hbound⟩ := hrank
  let A := freeMatrix (eM.inv ≫ φ ≫ eN.hom)
  let B := (freeMatrix δ).map (U.toScheme.Γevaluation x)
  let := hR.toField
  let s : Spec R := IsLocalRing.closedPoint R
  have hs : g.base s = j.base x.1 := by
    have hm : g.base s ∈ Set.range g.base := ⟨s, rfl⟩
    rw [himage] at hm
    exact Set.mem_singleton_iff.mp hm
  have hres : (A.map (Y.Γevaluation (j.base x.1))).rank ≤ a := by
    apply le_trans _ hbound
    let r := (A.map (Y.Γevaluation (j.base x.1))).rank
    obtain ⟨i, k, hminor⟩ := (Matrix.le_rank_map_iff A
      (Y.Γevaluation (j.base x.1)).hom r).mp le_rfl
    let := (isField_Γ_Spec hR).toField
    apply (Matrix.le_rank_map_iff A g.appTop.hom r).mpr
    refine ⟨i, k, ?_⟩
    apply (g.appTop_ne_zero_iff_mem_basicOpen (isField_Γ_Spec hR) _ s).mpr
    rw [hs]
    exact (Y.evaluation_ne_zero_iff_mem_basicOpen _ _ _).mp hminor
  have hsum : a + B.rank ≤ a := by
    rw [← local_block_residue_rank eM eN φ j a U eS eT f δ hform x]
    exact hres
  have hzero : B.rank = 0 := by omega
  have hrange : LinearMap.range B.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  have hlin : B.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  ext i k
  change B i k = 0
  have hv := congrArg (fun l ↦ l (Pi.single k 1) i) hlin
  simpa using hv

end AlgebraicGeometry.Scheme.Modules
