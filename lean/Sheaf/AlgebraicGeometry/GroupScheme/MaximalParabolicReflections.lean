/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Proper subgroups containing the other simple reflections

Source: Milne, Algebraic Groups (2017), Proposition 21.88 and proof, p.452;
application in Lemma 22.24, p.469 (blueprint: lem-sfb-maximal-parabolic-reflections).

The simple roots are indexed by the support of the given root-datum base.
A normalizer point represents their reflection precisely when its conjugation
on the torus induces the displayed reflection on all characters. This avoids
choosing representatives or a separate action of an abstract Weyl group.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- For each simple root there is a smooth connected proper closed subgroup
containing the Borel and every representative of each other simple reflection.
The root datum, pairing, and positivity are those of the given split Borel pair.
Strictness means that the inclusion is not an isomorphism.

Source: Milne, Proposition 21.88 and proof, p.452; Lemma 22.24, p.469.
(blueprint: lem-sfb-maximal-parabolic-reflections)

Proof plan:
1. By lem-sfb-reductive-borel-pair-structure the group is reductive and the
   character pairing is perfect. By lem-sfb-semisimple-roots-span and
   lem-sfb-root-base-rational-integral-spans the simple roots form a rational
   basis. Take the dual fundamental cocharacter and clear its finitely many
   denominators in split torus coordinates. This gives an integral cocharacter
   lambda with pairing d > 0 against the selected root and zero against the
   others. Its pairing with every positive root is nonnegative.
2. By lem-sfb-cocharacter-limit-smooth-structure the limit functor P_lambda
   is a smooth connected closed subgroup scheme: membership on every algebra
   means that lambda(t) g lambda(t)⁻¹ extends across t = 0.
3. Conjugation on T is constant. On a positive root group the formula from
   lem-sfb-reductive-root-subgroup-parametrizations has a nonnegative exponent,
   hence extends across zero on every test algebra. Thus these groups lie in P.
   By lem-sfb-borel-root-product-coordinates their product is the unipotent
   radical; the splitting from lem-sfb-reductive-borel-pair-structure gives B ⊆ P.
4. By lem-sfb-reductive-rank-one-reflections the negative selected root has
   a nonzero one-dimensional tangent weight space, of integer weight -d.
   The tangent formula of lem-sfb-cocharacter-limit-smooth-structure excludes
   it from Lie(P), proving the inclusion P → G is not an isomorphism. Integer
   character weights make this valid even when the characteristic divides d.
5. For another simple root the reflection fixes lambda: its pairing with
   lambda is zero, and perfection of the pairing gives equality of cocharacters.
   Every normalizer representative therefore commutes with lambda, so its
   conjugation orbit is constant and it belongs to P(F). The reflection formula
   squares to the identity since the root-coroot pairing is two, so using
   conjugation rather than inverse conjugation gives the same condition.
   If the base is empty there is no selected root, and the assertion is vacuous. -/
theorem maximal_parabolic_reflections
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ m : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F m))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
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
    (hΦ : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ,
      b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥) :
    ∀ i : b.support, ∃ (H : Grp (Over (Spec (.of F)))) (k : H ⟶ G),
      IsClosedSubgroupScheme k.hom.hom ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
      (∃ f : B ⟶ H, f ≫ k = iB) ∧ ¬ IsIso k ∧
      ∀ (l : b.support), l ≠ i → ∀ n : RankOneRoots.normalizer iT,
        (∃ e : T ≅ T,
          e.hom.hom.hom ≫ iT.hom.hom =
            (toUnit T.X ≫ n.val) * iT.hom.hom * (toUnit T.X ≫ n.val)⁻¹ ∧
          ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
            e.hom.hom.hom ≫ χ.toMul.hom.hom =
              (χ - (P.toLinearMap χ (P.coroot l.val)) • P.root l.val).toMul.hom.hom) →
        n.val ∈ RankOneRoots.pointImage k (𝟙_ (Over (Spec (.of F)))) := by
  sorry

end AlgebraicGeometry
