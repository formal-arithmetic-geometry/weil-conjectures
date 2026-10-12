/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality

/-! # Affine supported zero detection

Source: Stacks Project, Tag 0A9A, affine case.
(blueprint: lem-pc-supported-perfect-detector-affine).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The affine Koszul argument, including the empty scheme, detects zero objects supported
on a closed subset when an affine cover has at most one member.
Source: Stacks Project, Tag 0A9A, affine paragraph, and Tag 09IR.
(blueprint: lem-pc-supported-perfect-detector-affine).

Proof:
1. If the cover is empty, its union is empty, so X has no points. Every module sheaf
   and every derived object is zero. Take the strictly perfect zero complex.
2. Otherwise the cover has one member, which equals X. Thus X is affine. Identify X
   with Spec A by the canonical affine presentation. Quasi-compactness of X minus T
   gives finitely many functions f_i whose principal opens cover that complement.
3. Sheafify the actual finite Koszul complex on these functions and localize it.
   It is perfect and has quasi-coherent cohomology. Each f_i acts null-homotopically,
   so its cohomology stalks vanish off their common zero locus T (Tag 0663).
4. For a quasi-coherent K supported on T and orthogonal to every shift of this complex,
   apply koszul_open_orthogonality with the affine chart equal to X and open X minus T.
   The restriction of K to this open is zero: its cohomology sheaves have zero stalks
   there. The canonical unit therefore identifies K with derived pushforward of zero.
   A right adjoint preserves zero, so K is zero. The same calculation handles T empty
   (the Koszul complex is acyclic) and T equal to X (the empty Koszul tuple). -/
theorem supported_perfect_detector_affine
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (s : Finset X.affineOpens) (hcover : (⨆ U ∈ s, (U : X.Opens)) = ⊤)
    (hcard : s.card ≤ 1) (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    ∃ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
        (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj := by
  sorry

end AlgebraicGeometry
