/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
import Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Weyl dimension of the actual dominant induced module

Source: Jantzen, Representations of Algebraic Groups (2003), II.5.10--5.12;
Milne, Algebraic Groups (2017), Section 22d, pp.479--480, with the inverse-character
line-bundle convention of Section 18c and 22.48.
(blueprint: lem-sfb-induced-weyl-dimension-formula)

All dimensions, pairings, and fractions below are ordinary integers or rationals.
The characteristic is unrestricted, and the empty product is one.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

open Classical in
/-- The actual functions satisfying f(gb) = lambda(b) f(g) form a finite-dimensional
rational left-translation module. Its dimension is the Weyl product in Q, with
positive integer denominators. No simplicity assertion is made.

Source: Jantzen (2003), II.5.10--5.12; Milne (2017), Section 22d, pp.479--480,
with the signs of Section 18c and 22.48.
(blueprint: lem-sfb-induced-weyl-dimension-formula)

Proof plan:
1. By lem-sfb-reductive-borel-pair-structure, G is reductive and G/B is proper
   of finite type. Apply lem-sfb-homogeneous-line-bundle-sections to the negative
   of lambda extended by p. The inverse-character equation identifies its H0
   with precisely sectionModule G B iB (p composed with lambda) 1, equivariantly
   for (sf)(g) = f(s inverse g), over every F-algebra. The associated line is
   coherent. The degree-zero affine-base clause of lem-pc-coherent-hi proves
   finite dimensionality. The regular left coaction restricts to this subspace:
   right semi-invariance commutes with left translation, and tensoring over F
   preserves its kernel. This yields HasRationalLeftTranslation.
2. Dominance and this negative fibre character are exactly the hypotheses of
   lem-sfb-dominant-flag-line-kempf-vanishing, so all positive cohomology vanishes.
3. Apply lem-sfb-flag-line-euler-alternant. Its integral character q satisfies
   q A(-rho) = A(-lambda-rho). With positive cohomology zero, augmentation of q
   is the ordinary integer dimension of H0, by its finite weight decomposition.
4. By lem-sfb-simply-connected-character-lattice the simple roots and coroots
   span the rational character and cocharacter spaces. The actual root datum
   and its perfect pairing meet lem-sfb-weyl-alternant-augmentation. Apply that
   lemma with sigma = -rho and nu = -lambda-rho. It gives positive integral
   rho-coroot pairings; the two minus signs cancel in each ratio. Augmentation
   gives exactly the displayed formula in Q. In rank zero it is the empty
   product one. Every input holds in every characteristic. -/
theorem induced_weyl_dimension_formula
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
    (p : B ⟶ T) (hp : j ≫ p = 𝟙 T)
    (ρ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hρ : 2 • ρ = ∑ α : Φ with b.IsPos α, P.root α)
    (lam : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hlam : ∀ α : b.support, 0 ≤ P.toLinearMap lam (P.coroot α)) :
    Module.Finite F (RhoSection.sectionModule G B iB (p ≫ lam.toMul) 1) ∧
    RhoSection.HasRationalLeftTranslation G
      (RhoSection.sectionModule G B iB (p ≫ lam.toMul) 1) ∧
    (∀ α : Φ, b.IsPos α → 0 < P.toLinearMap ρ (P.coroot α)) ∧
    (Module.finrank F (RhoSection.sectionModule G B iB (p ≫ lam.toMul) 1) : ℚ) =
      ∏ α : Φ with b.IsPos α,
        (P.toLinearMap (lam + ρ) (P.coroot α) : ℚ) /
          (P.toLinearMap ρ (P.coroot α) : ℚ) := by
  sorry

end AlgebraicGeometry
