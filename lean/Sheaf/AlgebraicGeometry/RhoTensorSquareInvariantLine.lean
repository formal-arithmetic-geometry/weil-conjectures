module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Mathlib.Algebra.Algebra.Bilinear

/-! # The invariant line in the tensor square of rho sections

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemma 9.7.2(1) and Remark 9.7.3; Milne, Algebraic Groups (2017), 22.21--22.22
and 22.29--22.30 (blueprint: lem-sfb-rho-tensor-square-invariant-line).

The invariant subspace is written as an intersection of linear kernels. Its equations
are simultaneous left translation on the two factors, tested over every algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RhoSection

/-- Evaluate a tensor of actual rho sections at two algebra-valued points:
`f tensor f'` maps to `f(g) * f'(h)`. This is the canonical bilinear evaluation map,
constructed from the recorded evaluations and the inclusions of the actual section subspace.
Source: Alper, Section 9.7 and Lemma 9.7.2(1); Milne, 22.21
(blueprint: lem-sfb-rho-tensor-square-invariant-line). -/
def tensorSquareEvaluation {F : Type u} [Field F]
    (S B : Grp (Over (Spec (.of F)))) (j : B ⟶ S)
    (ρB : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) (m : ℕ)
    {A : Type u} [CommRing A] [Algebra F A]
    (g h : StandardGroupSchemes.affine F A ⟶ S.X) :
    sectionModule S B j ρB m ⊗[F] sectionModule S B j ρB m →ₗ[F] A :=
  TensorProduct.lift ((LinearMap.mul F A).compl₁₂
    ((evaluate g).toLinearMap ∘ₗ (sectionModule S B j ρB m).subtype)
    ((evaluate h).toLinearMap ∘ₗ (sectionModule S B j ρB m).subtype))

/-- The rational group-scheme invariant space of the tensor square of W_m has dimension one.
The intersection of kernels is precisely the coaction equalizer: on a pure tensor its
translated evaluation is f(s inverse g) f'(s inverse h). Since S is affine, evaluation
at the universal triple of points in F[S] tensor F[S] tensor F[S] detects equality.
The tensor inclusion from W_m into F[S] is injective over the field F. Thus these equations
retain invariance after every scalar extension, including nonreduced algebras.
The root, extension and conjugation hypotheses specify exactly the rho data supplied by
exists_rho_section_modules, without choosing an arbitrary rational action on W_m.

Source: Alper, Lemma 9.7.2(1), Remark 9.7.3; Milne, 22.21--22.22, 22.29--22.30
(blueprint: lem-sfb-rho-tensor-square-invariant-line).

Proof plan:
1. By lem-sfb-rho-section-modules, W = W_m is nonzero, finite-dimensional and rational,
   with W = E_B(chi) for chi = -m rho. Its dual has the rational contragredient action:
   the inverse-transpose matrix is regular, by composing matrix coefficients with inversion.
2. Send u tensor v to the map ell mapping to ell(v)u, identifying W tensor W with
   Hom(W dual, W). A basis and its dual give the inverse A mapping to sum A(e_i dual) tensor e_i.
   The dual-basis identities verify both composites. Simultaneous left translation becomes
   conjugation on Hom over every algebra, so invariant tensors are exactly equivariant maps.
3. By lem-sfb-rational-induction-character-reciprocity, evaluation at the identity identifies
   Hom_S(W dual, W) with Hom_B(W dual, F_chi). Every functional on W dual is evaluation
   at a unique w in W. Equivariance says b w = chi(b) inverse w, so this Hom space is the
   B-eigenvector subspace of character m rho.
4. By lem-sfb-induced-module-primitive-line, W fixed by U is a line of weight w_0 chi.
   The longest Weyl element permutes positive roots to their negatives, giving w_0 rho = -rho
   in the torsion-free character lattice, hence w_0 chi = m rho. Since B = T semidirect U
   and rhoB kills U, this line equals the B-eigenvector subspace in step 3. The linear
   identifications in steps 2--3 give the displayed dimension. -/
theorem tensorSquareInvariantLine {F : Type u} [Field F] [IsAlgClosed F]
    (S : Grp (Over (Spec (.of F)))) (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F)))) (i : T ⟶ S) (j : B ⟶ S) (k : T ⟶ B)
    (hTB : IsRhoBorelPair i j k) (a : ModObj T.X B.X)
    (ha : ∀ (Z : Over (Spec (.of F))) (t : Z ⟶ T.X) (b : Z ⟶ B.X),
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
        l.hom.hom ≫ ρB.hom.hom = 1)
    (m : ℕ) (hm : 0 < m) :
    Module.finrank F
      ↥(⨅ (A : Type u) (_ : CommRing A) (_ : Algebra F A)
        (s : StandardGroupSchemes.affine F A ⟶ S.X)
        (g : StandardGroupSchemes.affine F A ⟶ S.X)
        (h : StandardGroupSchemes.affine F A ⟶ S.X),
        LinearMap.ker (tensorSquareEvaluation S B j ρB m (s⁻¹ * g) (s⁻¹ * h) -
          tensorSquareEvaluation S B j ρB m g h) :
        Submodule F (sectionModule S B j ρB m ⊗[F] sectionModule S B j ρB m)) = 1 := by
  sorry

end AlgebraicGeometry.RhoSection
