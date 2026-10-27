/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.LinearAlgebra.Quotient.Defs
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import Mathlib.RingTheory.KrullDimension.Polynomial
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer

/-! # Root power laws for an isogeny of reductive groups

Source: Milne, Algebraic Groups (2017), Definitions 23.1--23.2, pp.483--484,
and Proposition 23.5, pp.485--486, especially formula (146)
(blueprint: lem-sfb-isogeny-root-power-laws).

Character and cocharacter lattices are the actual group-scheme Hom groups.
The pairing is composition, the roots are the nonzero adjoint character weights,
and the coroot reflections are induced by actual normalizer representatives.
The latter normalization specifies the geometric coroots also in central torus
directions. Root subgroup images are expressed by faithfully flat factorizations,
not by surjectivity on points of a test algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- An isogeny restricts to an isogeny of maximal tori, induces an injective
character map with finite cokernel, and matches roots and coroots with the same
characteristic-power multiplier. Every prescribed pair of root parametrizations
has the power formula on all commutative algebras. The full scheme kernel is
central exactly when all root multipliers are one.

Source: Milne, Definitions 23.1--23.2 and Proposition 23.5, pp.483--486,
formulas (144)--(147) (blueprint: lem-sfb-isogeny-root-power-laws).

Proof plan:
1. By lem-sfb-quotient-borel-torus-images the image of TA is TD; its kernel is
   the intersection with the finite kernel of f. Character antiduality
   (lem-sfb-multiplicative-character-antiduality) and
   lem-sfb-split-torus-hom-matrices identify the kernel ring with F[coker f*].
   Faithful flatness makes f* injective, and finite dimension makes its cokernel finite.
2. Factor each root map by lem-sfb-algebraic-group-homomorphism-factorization.
   The finite additive kernel and lem-sfb-additive-subgroup-polynomial-quotient
   identify its image with Ga, with quotient a monic additive polynomial P.
   Its torus action descends along fT. Its nonzero tangent character beta pulls
   back to deg(P) alpha, so lem-sfb-reductive-root-subgroup-parametrizations
   identifies the image with U_beta.
3. Compare coefficients in P(alpha(t)Z)=alpha(t)^deg(P) P(Z) over the universal
   torus. Torsion freeness makes P a monomial. Two Ga parametrizations differ
   by a nonzero scalar, since a polynomial automorphism fixing zero is linear.
   These polynomial identities specialize to every algebra, including nonreduced ones.
4. Additivity of Z^n forces n=1 in characteristic zero. In characteristic p,
   write n=p^r m with p not dividing m and compare the coefficient of U^(m-1)V
   after the injective substitution U=X^(p^r), V=Y^(p^r), to obtain m=1.
5. Reducedness from lem-sfb-reductive-rank-one-reflections gives injectivity of
   the root correspondence. The orbit dimension formula
   (lem-sfb-smooth-group-orbit-geometry) gives dim A=dim D. Bruhat charts and
   root product coordinates (lem-sfb-bruhat-longest-cell-charts,
   lem-sfb-borel-root-product-coordinates, lem-sfb-reductive-borel-pair-structure)
   give dim G=rank T+number of roots, using
   lem-weil-pbc-dense-open-dimension-comparison and lem-sf-noetherian-polynomial-dimension.
   Thus the finite root sets have equal size and the injection is bijective.
6. The rank-one centralizers and normalizer representatives of
   lem-sfb-reductive-rank-one-reflections show f* s_beta=s_alpha f*; the image
   representative is nontrivial because f* becomes an isomorphism over Q.
7. Expand these reflections, cancel the nonzero alpha in the free lattice,
   and use the composition pairing and its perfectness from
   lem-sfb-reductive-borel-pair-structure to get f_* alpha^vee=q(alpha) beta^vee.
8. The orbit of each geometric kernel point under connected A is smooth,
   connected and zero-dimensional, hence a point. The point is central, and
   lem-sfb-reductive-torus-self-centralizer puts it in TA. All points of the
   finite kernel have residue field F, so its entire support lies in TA.
9. Choose compatible Borels by lem-sfb-quotient-borel-torus-images. The root
   bijection matches positive systems and their negatives. Bruhat and root
   product coordinates give the open cell U^- times T times U^+ containing T.
   When all q=1, the two radical maps are isomorphisms in these coordinates.
10. The kernel factors through that open cell by step 8. Uniqueness of its
   product coordinates identifies it scheme-theoretically with ker fT.
   Every root is trivial on it; lem-sfb-reductive-centre-root-quotient gives centrality.
11. Conversely a central kernel lies in TA by the self-centralizer theorem.
   Root product coordinates give TA intersect U_alpha=1 as schemes. The
   additive root kernel has ring F[Z]/(Z^q), of dimension q, so it is trivial
   exactly for q=1. This retains infinitesimal kernels and proves the equivalence. -/
theorem isogeny_root_power_laws
    {F : Type u} [Field F] [IsAlgClosed F]
    (A D TA TD : Grp (Over (Spec (.of F))))
    (hA : ReductiveTorusCentralizer.IsReductive A)
    (hD : ReductiveTorusCentralizer.IsReductive D)
    (iA : TA ⟶ A) (iD : TD ⟶ D)
    (hTA : ReductiveTorusCentralizer.IsMaximalTorus iA)
    (hTD : ReductiveTorusCentralizer.IsMaximalTorus iD)
    (hsplitA : ∃ r : ℕ, Nonempty (TA ≅ MultiplicativeType.splitTorus F r))
    (hsplitD : ∃ r : ℕ, Nonempty (TD ≅ MultiplicativeType.splitTorus F r))
    [IsCommMonObj TA.X] [IsCommMonObj TD.X]
    [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aA : ModObj TA.X A.X) (aD : ModObj TD.X D.X)
    (hconjA : aA.smul = (iA.hom.hom ⊗ₘ 𝟙 A.X) ≫ GrpObj.conj A.X)
    (hconjD : aD.smul = (iD.hom.hom ⊗ₘ 𝟙 D.X) ≫ GrpObj.conj D.X)
    (ΦA : Finset (Additive (TA ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (ΦD : Finset (Additive (TD ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (PA : RootDatum ΦA
      (Additive (TA ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TA)))
    (PD : RootDatum ΦD
      (Additive (TD ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TD)))
    (hrootA : ∀ α : ΦA, PA.root α = α.val)
    (hrootD : ∀ β : ΦD, PD.root β = β.val)
    (hpairA : ∀ (χ : Additive (TA ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TA)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (PA.toLinearMap χ ν))
    (hpairD : ∀ (χ : Additive (TD ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TD)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (PD.toLinearMap χ ν))
    (hweightsA : ∀ χ : Additive (TA ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ ΦA ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ TA A aA χ.toMul ≠ ⊥)
    (hweightsD : ∀ χ : Additive (TD ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ ΦD ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ TD D aD χ.toMul ≠ ⊥)
    (hcorootA : ∀ α : ΦA, ∃ (n : 𝟙_ (Over (Spec (.of F))) ⟶ A.X) (s : TA ≅ TA),
      s.hom.hom.hom ≫ iA.hom.hom =
        (toUnit TA.X ≫ n)⁻¹ * iA.hom.hom * (toUnit TA.X ≫ n) ∧
      ∀ χ : Additive (TA ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        s.hom.hom.hom ≫ χ.toMul.hom.hom =
          χ.toMul.hom.hom / (PA.root α).toMul.hom.hom ^ (PA.toLinearMap χ (PA.coroot α)))
    (hcorootD : ∀ β : ΦD, ∃ (n : 𝟙_ (Over (Spec (.of F))) ⟶ D.X) (s : TD ≅ TD),
      s.hom.hom.hom ≫ iD.hom.hom =
        (toUnit TD.X ≫ n)⁻¹ * iD.hom.hom * (toUnit TD.X ≫ n) ∧
      ∀ χ : Additive (TD ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        s.hom.hom.hom ≫ χ.toMul.hom.hom =
          χ.toMul.hom.hom / (PD.root β).toMul.hom.hom ^ (PD.toLinearMap χ (PD.coroot β)))
    (UA : ΦA → Grp (Over (Spec (.of F)))) (UD : ΦD → Grp (Over (Spec (.of F))))
    (jA : ∀ α : ΦA, UA α ⟶ A) (jD : ∀ β : ΦD, UD β ⟶ D)
    (hUA : ∀ α : ΦA, IsClosedSubgroupScheme (jA α).hom.hom ∧
      @TorusCharacterTangent.IsStable F _ TA A aA _ (jA α) ∧
      (GrpObj.differential (jA α).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ TA A aA (PA.root α).toMul)
    (hUD : ∀ β : ΦD, IsClosedSubgroupScheme (jD β).hom.hom ∧
      @TorusCharacterTangent.IsStable F _ TD D aD _ (jD β) ∧
      (GrpObj.differential (jD β).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ TD D aD (PD.root β).toMul)
    (uA : ∀ α : ΦA, Grp.mk (StandardGroupSchemes.additive F) ≅ UA α)
    (uD : ∀ β : ΦD, Grp.mk (StandardGroupSchemes.additive F) ≅ UD β)
    (f : A ⟶ D) (hff : f.hom.hom.left.appTop.hom.FaithfullyFlat)
    (hfinite : IsFinite (GrpObj.ker f.hom.hom).hom)
    (fT : TA ⟶ TD) (hfT : fT ≫ iD = iA ≫ f) :
    fT.hom.hom.left.appTop.hom.FaithfullyFlat ∧
    IsFinite (GrpObj.ker fT.hom.hom).hom ∧
    Function.Injective (fun χ : TD ⟶ Grp.mk (StandardGroupSchemes.multiplicative F) ↦
      fT ≫ χ) ∧
    Finite (Additive (TA ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) ⧸
      Submodule.span ℤ (Set.range
        (fun χ : Additive (TD ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) ↦
          Additive.ofMul (fT ≫ χ.toMul)))) ∧
    ∃ (b : ΦA ≃ ΦD) (q : ΦA → ℕ) (c : ΦA → Fˣ),
      (∀ α : ΦA, ∃ m : ℕ, q α = ringExpChar F ^ m) ∧
      (∀ α : ΦA,
        Additive.ofMul (fT ≫ (PD.root (b α)).toMul) = q α • PA.root α) ∧
      (∀ α : ΦA,
        Additive.ofMul ((PA.coroot α).toMul ≫ fT) = q α • PD.coroot (b α)) ∧
      (∀ (α : ΦA) (R : Type u) [CommRing R] [Algebra F R] (x : R),
        TorusCharacterTangent.additiveParameterPoint F x ≫
            (uA α).hom.hom.hom ≫ (jA α).hom.hom ≫ f.hom.hom =
          TorusCharacterTangent.additiveParameterPoint F
              (algebraMap F R (c α : F) * x ^ q α) ≫
            (uD (b α)).hom.hom.hom ≫ (jD (b α)).hom.hom) ∧
      (∀ α : ΦA, ∃ g : UA α ⟶ UD (b α),
        g ≫ jD (b α) = jA α ≫ f ∧ g.hom.hom.left.appTop.hom.FaithfullyFlat) ∧
      ((∀ (R : Type u) [CommRing R] [Algebra F R]
          (x : StandardGroupSchemes.affine F R ⟶ GrpObj.ker f.hom.hom)
          (g : StandardGroupSchemes.affine F R ⟶ A.X),
          (x ≫ GrpObj.kerι f.hom.hom) * g = g * (x ≫ GrpObj.kerι f.hom.hom)) ↔
        ∀ α : ΦA, q α = 1) := by
  sorry

end AlgebraicGeometry
