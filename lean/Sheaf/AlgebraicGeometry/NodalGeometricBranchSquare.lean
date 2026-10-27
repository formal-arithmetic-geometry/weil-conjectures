/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.AlgebraicGeometry.NodalLocalTangentData
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The cartesian square of normalization residues at a geometric node

Source: Stacks Project, curves.tex, Tags 0C4A, 0C4D, 0CBT, 0CBU, and 0CBW.
(blueprint: lem-sfb-nodal-geometric-branch-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NodalLocal

/-- Geometric completion splits the actual normalization residue algebra into its branches.

Source: Stacks Project, curves.tex, Tags 0C4A, 0C4D, 0CBT, 0CBU, and 0CBW.
(blueprint: lem-sfb-nodal-geometric-branch-square).

Proof:
Choose an affine neighbourhood Spec S of x. Its geometric inverse image is
Spec(S tensor_k Omega), and the chosen point corresponds to evaluation through an
embedding rho:kappa(x) → Omega. The residue field at this maximal point is Omega,
with inverse to the structural field map. The separable closed-point formal
presentation theorem identifies the completed geometric stalk with the power-series
presentation over extended coefficients of the original completed stalk. For a nodal
quadratic q, arrange its X² coefficient nonzero. The normalized completed ring is
L[[t]], L = kappa[Z]/q(Z,1), by the explicit quadratic integral-closure calculation;
after the specified scalar extension it is (L tensor_kappa Omega)[[t]]. The two distinct
roots identify L tensor_kappa Omega with Omega×Omega, so the completed branch residue
is Omega×Omega and its spectrum has two points. Normalization/completion identifies
the original normalization tensored with the original completion with L[[t]].
Extend coefficients on series and transport through these identifications to obtain
nu into the actual geometric completed normalization. This extends the geometric
completion map on the stalk, since all normalization maps extend fractions with their
original denominators. Its map on residues is r, and reduction of the tensor
comparison gives the canonical isomorphism E tensor_kappa Omega ≅ completedBranchAlgebra.
Consequently Spec of this algebra is the pullback of Spec E along Spec rho, with
projections Spec r and the structural Omega map. The residue-field and quotient
formulas follow on representatives from evaluation, tensor balancing, and the
normalization map. They fix all arrows and are independent of root order.
-/
theorem geometric_branch_square
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hpure : C.IsPureDimension 1)
    (x : C) (hx : x ∈ closedPoints C)
    (hfinite : (f.residueFieldAlgebraMap x).Finite)
    (hsep : @Algebra.IsSeparable k (C.residueField x) _ _
      (f.residueFieldAlgebraMap x).toAlgebra)
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (y : pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
    (hy : pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) y = x)
    (hnode : Nonempty (CompletedLocalRing
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) y ≃+*
      (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span
        {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) * MvPowerSeries.X 1}))) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    let g := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    ∃ (ω : Y.residueField y ≃+* Ω) (ρ : C.residueField x →+* Ω)
      (ν : Normalization (C.presheaf.stalk x) →+* Normalization (CompletedLocalRing Y y))
      (r : ResidueAlgebra (C.presheaf.stalk x) →+* CompletedBranchAlgebra Y y),
      (∀ c : Ω, ω (IsLocalRing.residue (Y.presheaf.stalk y) (stalkScalarMap g y c)) = c) ∧
      (∀ a : C.presheaf.stalk x,
        ρ (IsLocalRing.residue (C.presheaf.stalk x) a) =
          ω (IsLocalRing.residue (Y.presheaf.stalk y)
            (((C.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ p.stalkMap y).hom a))) ∧
      (∀ a : C.presheaf.stalk x,
        ν (algebraMap (C.presheaf.stalk x) (Normalization (C.presheaf.stalk x)) a) =
          algebraMap (CompletedLocalRing Y y) (Normalization (CompletedLocalRing Y y))
            (geometricCompletionMap p x y hy a)) ∧
      (∀ a : Normalization (C.presheaf.stalk x),
        r (Ideal.Quotient.mk (normalizationIdeal (C.presheaf.stalk x)) a) =
          Ideal.Quotient.mk (completedBranchIdeal Y y) (ν a)) ∧
      IsPullback (Spec.map (CommRingCat.ofHom r))
        (Spec.map (CommRingCat.ofHom (completedBranchScalars g y)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x)))))
        (Spec.map (CommRingCat.ofHom ρ)) ∧
      Nat.card (Spec (.of (CompletedBranchAlgebra Y y))) = 2 := by sorry

end AlgebraicGeometry.NodalLocal
