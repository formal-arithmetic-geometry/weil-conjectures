/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections

/-! # The canonical character of a complete flag variety

Source: Brion--Kumar, Frobenius Splitting Methods in Geometry and Representation Theory,
Section 2.1, equation (8), printed pp.63--64; Milne, Algebraic Groups (2017),
Sections 18c and 21a (blueprint: lem-sfb-flag-canonical-character).

The character rho is integral: its square is the product of the positive roots.
The extension rhoB is the unique extension trivial on the unipotent radical,
as in `exists_rho_section_modules`; it equals rho composed with the Borel projection.
With the quotient convention in `AssociatedCharacterLineBundle.Presentation`,
the square of rhoB gives L_(2 rhoB), also denoted M_(-2 rho).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The flag quotient is smooth of dimension the number of positive roots, and its
actual top exterior differential sheaf is invertible and isomorphic to the associated
line sheaf for twice the extended rho character. The last clause includes the empty
positive system: the quotient is the base point and both line sheaves are trivial.

Source: Brion--Kumar, Section 2.1, equation (8), printed pp.63--64; Milne,
Section 18c, pp.389--390, Section 21a, p.425, Theorem 21.11 and 21.29--21.35
(blueprint: lem-sfb-flag-canonical-character).

Proof:
1. By lem-sfb-reductive-borel-pair-structure, S is reductive and its quotient
   map is the right B-torsor. Apply lem-sfb-homogeneous-cotangent-associated-bundle
   to identify the actual differential sheaf with the bundle of (Lie S / Lie B)^dual,
   and its top wedge with the associated determinant representation.
2. By lem-sfb-reductive-rank-one-reflections and
   lem-sfb-regular-cocharacter-borel-description, Lie S / Lie B is the direct sum
   of the one-dimensional negative-root spaces. A nonzero vector in each is a basis.
   Thus its dual has dimension the length of the positive-root list, proving the
   smoothness and pure-dimension assertion.
3. The contragredient action on the dual basis has weights the positive roots.
   Its determinant character restricts to their product, namely rho squared by
   lem-sfb-rho-section-modules. By lem-sfb-unipotent-to-multiplicative-trivial,
   that determinant character is trivial on the unipotent radical. The semidirect
   product B = U semidirect T therefore identifies it with rhoB squared.
4. The top-wedge comparison and lem-sfb-homogeneous-line-bundle-sections give
   the indicated isomorphism of actual O_Q-modules, with quotient relation
   (g,z)b = (gb,rhoB(b)^(-2) z). This is L_(2 rhoB) = M_(-2 rho).
   For an empty root list the regular-cocharacter description gives S = T = B;
   the quotient is Spec F and the empty wedge and character product are the units.
   All weight calculations use characters on test algebras, so every characteristic,
   including two, is allowed. -/
theorem flag_canonical_character {F : Type u} [Field F] [IsAlgClosed F]
    (S : Grp (Over (Spec (.of F)))) (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F))))
    (iT : T ⟶ S) (iB : B ⟶ S) (j : T ⟶ B) (hTB : IsRhoBorelPair iT iB j)
    (a : ModObj T.X B.X)
    (ha : a.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φ : List (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hΦ : Φ.Nodup)
    (hroots : ∀ α : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      α ∈ Φ ↔ α.hom.hom ≠ 1 ∧ @TorusCharacterTangent.weightSpace F _ T B a α ≠ ⊥)
    (ρ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (ρB : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hρ : ρ.hom.hom ^ 2 = (Φ.map (fun α ↦ α.hom.hom)).prod)
    (hρB : j ≫ ρB = ρ)
    (hρU : ∀ (U : Grp (Over (Spec (.of F)))) (l : U ⟶ B),
      IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
      ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
        l.hom.hom ≫ ρB.hom.hom = 1)
    (Q : Over (Spec (.of F))) (π : S.X ⟶ Q)
    (hQ : IsProper Q.hom) (hQft : LocallyOfFiniteType Q.hom) (hQqc : QuasiCompact Q.hom)
    (hπf : Flat π.left) (hπs : Surjective π.left)
    (hπi : (fst S.X B.X * (snd S.X B.X ≫ iB.hom.hom)) ≫ π = fst S.X B.X ≫ π)
    (hπt : IsPullback (fst S.X B.X)
      (fst S.X B.X * (snd S.X B.X ≫ iB.hom.hom)) π π) :
    SmoothOfRelativeDimension Φ.length Q.hom ∧
    (Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials Φ.length).IsInvertible ∧
    ∃ χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      χ.hom.hom = ρB.hom.hom ^ 2 ∧
      ∃ P : AssociatedCharacterLineBundle.Presentation S B iB Q π χ,
        Nonempty (Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials Φ.length ≅ P.L) ∧
        (Φ.length = 0 → Nonempty (Q ≅ Over.mk (𝟙 (Spec (.of F)))) ∧
          Nonempty (Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials Φ.length ≅
            Scheme.Modules.unit Q.left) ∧ Nonempty (P.L ≅ Scheme.Modules.unit Q.left)) := by
  sorry

end AlgebraicGeometry
