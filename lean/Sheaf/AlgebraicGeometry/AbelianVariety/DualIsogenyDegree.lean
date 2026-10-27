module

public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Degree of the dual isogeny

Source: Milne, Abelian Varieties, I §9, Theorem 9.1, printed p.41.
(blueprint: lem-sfb-dual-isogeny-degree)

The classifying isomorphism respects the specified identity-axis rigidifications.
Degree is the order of the scheme-theoretic kernel, including its nilpotents.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The identity-axis rigidification after pulling a family back in its abelian-variety
coordinate along a homomorphism. This is the composite of pullback composition, the equality
expressing preservation of the identity, and the original rigidification; it makes no choice.
Source: Milne AV I §9 opening paragraph, p.41 (blueprint: lem-sfb-dual-isogeny-degree). -/
def abelianSourceRigidificationPullback {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    (u : A ⟶ B) [IsMonHom u] (T : Over (Spec (.of k)))
    (P : (B ⊗ T).left.Modules)
    (r : (Scheme.Modules.pullback (abelianIdentityAxis B T).left).obj P ≅
      𝟙_ T.left.Modules) :
    (Scheme.Modules.pullback (abelianIdentityAxis A T).left).obj
      ((Scheme.Modules.pullback (u ▷ T).left).obj P) ≅ 𝟙_ T.left.Modules :=
  (Scheme.Modules.pullbackComp (abelianIdentityAxis A T).left (u ▷ T).left).app P ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      ((lift_whiskerRight (toUnit T ≫ η[A]) (𝟙 T) u).trans
        (congrArg₂ lift
          ((Category.assoc (toUnit T) η[A] u).trans
            (congrArg (fun h ↦ toUnit T ≫ h) (IsMonHom.one_hom u))) rfl)))).app P ≪≫ r

/-- The homomorphism classifying pullback of the normalized Poincare family along an
isogeny is an isogeny of the same scheme-theoretic degree over any field.
Source: Milne AV I Theorem 9.1, p.41 (blueprint: lem-sfb-dual-isogeny-degree).

Proof plan:
1. Put N = ker u and H = Γ(N, O_N). The kernel is finite and commutative. By
[lem-sc-isogeny-degree], u is finite flat and surjective, hence fpqc. Geometric integrality
[lem-sc-abelian-variety-characterization] and [lem-pc-h0-proper-variety] give Γ(A, O_A) = k.
Flat coherent base change [lem-sc-flat-base-change-coherent], followed by affine gluing,
gives Γ(A × S, O) = Γ(S, O) for arbitrary S, including nonreduced parameter schemes.
2. The maps (a,n) ↦ (a,a+n) and (a,a') ↦ (a,a'-a) identify A × N with A ×_B A.
Apply [lem-sfb-pointed-torsor-line-character-descent] with the zero sections: characters
of N_T are precisely rigidified lines on B_T whose pullback to A_T is trivial.
3. Such lines are fibrewise algebraically trivial: over an algebraically closed geometric
field, lift each point of B to A (a nonempty finite fibre has a point by
[lem-pc-finite-extension-alg-closed]). Translation by a lift leaves the character multiplier
unchanged. Full faithfulness of [lem-pc-fpqc-descent] then makes the descended line homogeneous;
[lem-sfb-abelian-homogeneous-line-algebraic-triviality] makes it algebraically trivial.
4. The normalized Poincare universal property identifies ker uDual on every test scheme
with these lines, naturally and compatibly with tensor product. By
[lem-sfb-finite-commutative-cartier-representability], ker uDual is the Cartier dual of N,
with coordinate algebra the linear dual of H. In particular this kernel is finite.
5. By [lem-sfb-abelian-isogeny-quasi-inverse] choose n ≥ 1 and v with vu = [n] and uv = [n].
Pulling back Poincare families defines vDual. Uniqueness of classification and
[lem-pc-module-pullback-identity-composition] reverse composition under duality.
[lem-sfb-algebraically-trivial-line-multiplicativity] gives [n]*M ≅ M tensor-powered n,
normalized at zero by rescaling by a unit on the parameter scheme. Thus the tensor law
in [def-sfb-abelian-dual-poincare-datum] gives vDual ≫ uDual = [n] on A's dual.
6. Multiplication by n is surjective by [lem-sc-mult-n-isogeny]. Its factorization through
uDual makes uDual surjective. Together with the given homomorphism condition and the finite
kernel from step 4 this is [def-sc-isogeny].
7. The degree of uDual is dim_k H*. A basis of H and its coefficient functionals give a
basis of H*, so dim_k H* = dim_k H = deg u. This retains nonreduced kernel length and uses
no perfection, separability or characteristic hypothesis.
-/
theorem IsIsogeny.dual_isogenyDegree_eq
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] [IsAbelianVariety A] [IsAbelianVariety B]
    (DA : AbelianDualPoincareDatum A) (DB : AbelianDualPoincareDatum B)
    (u : A ⟶ B) [IsIsogeny u] (uDual : DB.dual ⟶ DA.dual) [IsMonHom uDual]
    (hDual : ∃ i : (Scheme.Modules.pullback (A ◁ uDual).left).obj DA.poincare ≅
        (Scheme.Modules.pullback (u ▷ DB.dual).left).obj DB.poincare,
      (Scheme.Modules.pullback (abelianIdentityAxis A DB.dual).left).map i.hom ≫
          (abelianSourceRigidificationPullback u DB.dual DB.poincare DB.rigidification).hom =
        (abelianRigidificationPullback A DA.dual DB.dual DA.poincare
          DA.rigidification uDual).hom) :
    IsIsogeny uDual ∧ isogenyDegree uDual = isogenyDegree u := by
  sorry

end AlgebraicGeometry
