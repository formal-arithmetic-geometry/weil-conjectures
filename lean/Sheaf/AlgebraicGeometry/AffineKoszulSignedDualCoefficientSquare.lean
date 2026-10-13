/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.SignedSheafDualCoefficientMap
public import Sheaf.RingTheory.KoszulQuotientCoefficientComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Finite-free affine signed dual coefficient square

Source: Stacks Project, Tag 0BQZ and Tag 01HV. -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The affine finite-free signed dual comparisons commute with quotient coefficients.
Source: Stacks Project, Tag 0BQZ, displayed Hom-complex map;
Tag 01HV, Lemma 26.5.4(4)-(5), localization of associated modules.
(blueprint: new-g3-affine-koszul-signed-dual-coefficient-square).

Proof: In nonnegative degree k use the exterior-power basis of the free
module A^n. On a principal open D(g), maps from its associated sheaf to
tilde(M), for M=A or A/I, are tuples of values in M_g on that finite basis.
Localization of Hom_A(K_k,M) gives exactly these tuples. Their coordinate
identifications commute with localization, so they define inverse sheaf
maps. Precomposition by the localized Koszul boundary has the same matrix
on either side; the integer sign -(-1)^k equals (-1)^(k+1). Thus the maps
commute with the signed differentials. In negative degree both terms are
zero; at the degree -1 boundary the source is zero. The degree comparisons
therefore assemble into complex isomorphisms. Postcomposition with A→A/I
reduces every basis value, which is precisely koszulCoefficientReduction.
This proves the coefficient square degreewise. The empty exterior bases,
zero ring, top ideal and empty charts are covered by the same formulas. -/
theorem affine_koszul_signed_dual_coefficient_square
    {Y : Scheme.{u}} (U : Y.affineOpens) (I : Ideal (Γ(Y, U.1)))
    (n : ℕ) (f : Fin n → Γ(Y, U.1)) :
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
    let E := TC.obj
      ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
    ∃ (bO : signedSheafDualComplex (R := U.1.toScheme.toRingedSpace.sheaf)
          E (T.obj (ModuleCat.of A A)) ≅
        TC.obj ((ExteriorAlgebra.koszulDualComplex A n f).extend
          ComplexShape.embeddingUpNat))
      (bQ : signedSheafDualComplex (R := U.1.toScheme.toRingedSpace.sheaf)
          E (T.obj (ModuleCat.of A (A ⧸ I))) ≅
        TC.obj ((ExteriorAlgebra.koszulQuotientDualComplex A I n f).extend
          ComplexShape.embeddingUpNat)),
      signedSheafDualCoefficientMap E (T.map (ModuleCat.ofHom I.mkQ)) ≫ bQ.hom =
        bO.hom ≫ TC.map (HomologicalComplex.extendMap
          (ExteriorAlgebra.koszulCoefficientReduction A I n f)
          ComplexShape.embeddingUpNat) := by
  sorry

end AlgebraicGeometry
