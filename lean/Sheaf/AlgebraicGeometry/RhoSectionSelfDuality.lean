/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.RhoCoordinateComparison
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
import Sheaf.AlgebraicGeometry.GroupScheme.CharacteristicZeroCompleteReducibility
import Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight

/-! # Self-duality of rho section modules

Source: Alper, Adequate moduli spaces, Lemma 9.7.4(1),(2), printed pp.49--50;
Milne, Algebraic Groups (2017), Section 22.
(blueprint: lem-sfb-rho-section-self-duality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj
namespace AlgebraicGeometry.RhoSection

/-- Self-duality of the actual regular-function subspace with its left-translation
coaction. The evaluation identity determines the coaction: contracting its function
factor at g and its group factor at s gives f(s inverse g), over every F-algebra.
The dual is the actual linear dual with its antipode-characterized contragredient.
Source: Alper, Lemma 9.7.4(1),(2); Milne, Sections 4a and 22.
(blueprint: lem-sfb-rho-section-self-duality). -/
def IsSelfDualLeftTranslation {F : Type u} [Field F]
    (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left]
    (W : Submodule F (Coordinate S.X)) : Prop :=
  ∃ (c : W →ₗ[F] W ⊗[F] RationalHighestWeight.coordinateAlgebra S)
    (d : Module.Dual F W →ₗ[F]
      Module.Dual F W ⊗[F] RationalHighestWeight.coordinateAlgebra S),
    HopfAction.Coassociative F (RationalHighestWeight.coordinateAlgebra S) W c ∧
    HopfAction.Counital F (RationalHighestWeight.coordinateAlgebra S) W c ∧
    (∀ (A : Type u) [CommRing A] [Algebra F A]
      (s g : StandardGroupSchemes.affine F A ⟶ S.X) (f : W),
      TensorProduct.lift (LinearMap.mul F A)
        (TensorProduct.map ((evaluate g).toLinearMap ∘ₗ W.subtype)
          ((evaluate s).comp (coordinateComparison S).toAlgHom).toLinearMap (c f)) =
        evaluate (s⁻¹ * g) f.val) ∧
    HopfAction.Coassociative F (RationalHighestWeight.coordinateAlgebra S)
      (Module.Dual F W) d ∧
    HopfAction.Counital F (RationalHighestWeight.coordinateAlgebra S)
      (Module.Dual F W) d ∧
    RationalHighestWeight.IsContragredient c d ∧
    ∃ e : W ≃ₗ[F] Module.Dual F W,
      e.toLinearMap.rTensor (RationalHighestWeight.coordinateAlgebra S) ∘ₗ c =
        d ∘ₗ e.toLinearMap

/-- The rho sections are self-dual at every positive weight in characteristic zero,
and at the weights p^nu - 1, nu positive, in characteristic p positive.
No assertion is made at other positive-characteristic weights.
Source: Alper, Lemma 9.7.4(1),(2), printed pp.49--50 (field specialization);
Milne, Theorems 22.18--22.19, Proposition 22.41, and the paragraph after 22.31.
(blueprint: lem-sfb-rho-section-self-duality).

Proof:
1. By lem-sfb-rho-section-modules W is nonzero finite-dimensional and rational.
   Its semi-invariance equation identifies it with E_B(-m rho). Apply
   lem-sfb-induced-module-primitive-line: its U-invariants form the line of
   weight w0(-m rho) = m rho. Indeed w0 permutes positive roots onto their
   negatives, so w0 rho = -rho in the rational character lattice, also in
   characteristic two; this calculation never divides in F.
2. In characteristic zero, lem-sfb-characteristic-zero-complete-reducibility
   decomposes W into simple summands. By lem-sfb-simple-module-dual-highest-weight
   each contributes a one-dimensional invariant line. Invariants commute with
   finite direct sums, so step 1 forces exactly one summand, making W simple.
3. In characteristic p, at m = p^nu - 1 with nu positive, the defining equations
   identify W with the module of lem-sfb-steinberg-induced-module-irreducible.
   Thus W is simple at precisely the indices required here.
4. By lem-sfb-simple-module-dual-highest-weight the contragredient is simple
   of highest weight -w0(m rho) = m rho. Its equal-highest-weight clause gives
   the desired equivariant linear equivalence. The coaction square asserts
   equivariance over every algebra, including nonreduced algebras.
-/
theorem rho_section_self_duality {F : Type u} [Field F] [IsAlgClosed F]
    (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left]
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F))))
    (i : T ⟶ S) (j : B ⟶ S) (k : T ⟶ B) (hpair : IsRhoBorelPair i j k)
    (a : ModObj T.X B.X)
    (hconj : ∀ (Z : Over (Spec (.of F))) (t : Z ⟶ T.X) (b : Z ⟶ B.X),
      lift t b ≫ a.smul = (t ≫ k.hom.hom) * b * (t ≫ k.hom.hom)⁻¹)
    (Φ : List (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (ρ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (ρB : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hΦnodup : Φ.Nodup)
    (hΦ : ∀ α, α ∈ Φ ↔ α.hom.hom ≠ 1 ∧
      @TorusCharacterTangent.weightSpace F _ T B a α ≠ ⊥)
    (hρ : ρ.hom.hom ^ 2 = (Φ.map (fun α ↦ α.hom.hom)).prod)
    (hρB : k ≫ ρB = ρ)
    (hU : ∀ (U : Grp (Over (Spec (.of F)))) (l : U ⟶ B),
      IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
      ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
        l.hom.hom ≫ ρB.hom.hom = 1) :
    ∀ (m : ℕ),
      (CharZero F ∧ 0 < m) ∨
        (∃ (p ν : ℕ), 0 < p ∧ CharP F p ∧ 0 < ν ∧ m = p ^ ν - 1) →
      IsSelfDualLeftTranslation S (sectionModule S B j ρB m) := by
  sorry

end AlgebraicGeometry.RhoSection
