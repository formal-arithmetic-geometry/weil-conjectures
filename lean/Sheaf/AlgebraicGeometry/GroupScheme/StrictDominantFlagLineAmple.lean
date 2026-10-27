/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
import Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice
import Sheaf.AlgebraicGeometry.GroupScheme.BorelCharacteristicPicardSequence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Ampleness of strictly dominant flag line bundles

Source: Milne, Algebraic Groups (2017), Theorem 17.9, Theorem 21.73,
Remark 21.74, Theorem 22.48 and Remark 22.49, pp.479--480; Stacks Tag 01PS.
(blueprint: lem-sfb-strict-dominant-flag-line-ample)

The root datum is on the actual character lattice, with positive roots pinned to
Lie(B). The character p followed by -μ gives the quotient action with fibre scalar
μ(p(b)). The conclusion concerns every presentation of that associated bundle.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The flag scheme of a semisimple simply connected group is smooth, projective
and geometrically integral. Every strictly dominant character gives an ample
invertible associated sheaf with the specified quotient action.

Source: Milne, Theorem 17.9, Theorem 21.73, Remark 21.74, Theorem 22.48 and
Remark 22.49, pp.479--480; Stacks Properties Definition 01PS.
(blueprint: lem-sfb-strict-dominant-flag-line-ample)

Proof plan:
1. Apply lem-sfb-reductive-borel-pair-structure to deduce reductivity. The smooth
   projective clause is lem-sfb-flag-torus-fixed-geometry; projectivity includes
   quasi-compactness by def-pc-projective-morphism. By
   lem-sfb-bruhat-longest-cell-charts the quotient is geometrically integral and
   its open big cell C is affine space, with finitely many translates covering Q.
2. By lem-sfb-simply-connected-character-lattice, μ is the sum of fundamental
   characters with coefficients a_i equal to its simple-coroot pairings. Strict
   dominance makes all these integers positive, in every characteristic.
3. Apply lem-sfb-fundamental-flag-boundary-sections to obtain sections s_i of
   M_(ω_i) whose zero loci are precisely the boundary components of C.
4. By lem-sfb-borel-characteristic-picard-sequence the characteristic line map
   is a homomorphism, with M_ν = c_B(-ν composed with p). Tensor the a_i-th powers
   of s_i using def-pur-sheaf-tensor-product to obtain s in M_μ. In a local frame
   its coefficient is the product of f_i raised to a_i. A product in a local ring
   is a unit exactly when each factor is a unit. Since a_i > 0, Q_s is C.
   The associated sheaf is invertible by lem-sfb-homogeneous-line-bundle-sections.
5. The geometric left action of lem-sfb-homogeneous-line-bundle-sections commutes
   with the right quotient action and sends s to (hs)(x)=h(s(h⁻¹x)). Its fibre
   maps are invertible, so Q_(hs)=hC. The finite translating cover is therefore
   an affine nonvanishing cover by sections of M_μ itself. Apply
   def-weil-pbc-ample-invertible-module with exponent one. In rank zero, the
   character lattice is zero, the empty tensor section is 1, Q=Spec F and
   M_0=O_Q; that section gives the same affine cover, so this case is included. -/
theorem strictDominant_flagLine_ample
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (hsc : ∀ (G' : Over (Spec (.of F))) [GrpObj G'],
      IsSemisimpleGroupScheme G' → ∀ (f : G' ⟶ G.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F A ⟶ G'),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ G) (iB : B ⟶ G) (j : T ⟶ B)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ CategoryTheory.GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ CategoryTheory.GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpositive : ∀ α : Φ,
      b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (U : Grp (Over (Spec (.of F)))) (iU : U ⟶ B) (p : B ⟶ T)
    (hU : IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
      Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
      ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
        IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
        Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
        ∃ f : N ⟶ U, f ≫ iU = iN)
    (hp : j ≫ p = 𝟙 T)
    (hker : IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X])
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπtorsor : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π) :
    Smooth Q.hom ∧ IsProjective Q.hom ∧ GeometricallyIntegral Q.hom ∧
      ∀ mu : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        (∀ α : b.support, 0 < P.toLinearMap mu (P.coroot α)) →
        ∀ M : AssociatedCharacterLineBundle.Presentation G B iB Q π (p ≫ (-mu).toMul),
          ∃ hM : M.L.IsInvertible, @Scheme.Modules.IsAmple Q.left M.L hM := by
  sorry

end AlgebraicGeometry
