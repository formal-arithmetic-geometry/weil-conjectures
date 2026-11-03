/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernClassAssembly
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernCupComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernComponentCoordinates
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernTwistInvertible

/-! # The cohomological projective-bundle coefficient map

Source: Stacks Project, Tag 0FI5, proposition-chern-class and equation-chern-classes;
ordinary splitting-principle definition in localized-top-Chern Step 4 (L4).
(blueprint: lem-pur-chern-coefficient-bijective).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The actual unsigned coefficient map is a sum of pullbacks followed by fixed
coefficient morphisms, with exactly the published degree transports.
Source: Stacks Tag 0FI5, the coefficient expansion before equation-chern-classes.
Proof: apply the proved arbitrary-input postcomposition formula to each summand
on the projective scheme over the original base field. Keep the final equality
transport, so the formula also covers the last coefficient and rank zero.
(blueprint: lem-pur-chern-coefficient-bijective). -/
theorem ordinaryFiniteProjectiveUnsignedCoefficientMap_postcompose
    (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (c : ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1)) :
    P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a D hL r c =
      ∑ i : Fin r,
        (P.ordinaryFiniteCohomologyPullback t D.A.data.relProjHom
          (P.diagonalExponent_isUnit a) (i.val + 1) (c i) ≫
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) D.A.data.relProj).mapDerivedCategory.map
              (P.ordinaryFiniteEtaleHyperplaneProductMap D.A.data.relProj
                (P.projectiveBundleChern a D hL) (i.val + 1) (r - (i.val + 1)))) ≫
          eqToHom (congrArg (P.diagonalTwist D.A.data.relProj)
            (Nat.add_sub_of_le (Nat.succ_le_of_lt i.isLt))) := by
  unfold ordinaryFiniteProjectiveUnsignedCoefficientMap
  apply Finset.sum_congr rfl
  intro i _
  rw [P.ordinaryFiniteHyperplaneProduct_postcompose (D.A.data.relProjHom ≫ a)]

/-- For a rank-one bundle the unsigned coefficient map is simply normalized
pullback along P(F) ≅ T. This proves the first positive-rank basis case directly.
Source: Stacks Tag 01OB, projective bundle of a line, and Tag 0FI5, degree-one relation.
Proof: the geometry system identifies the projective projection as an isomorphism.
There is one coordinate and the hyperplane exponent is zero, so the coefficient
map is evaluation at that coordinate followed by normalized pullback. Both maps
are bijective; the second is the proved equivalence-induced Hom bijection.
(blueprint: lem-pur-chern-coefficient-bijective). -/
theorem ordinaryFiniteProjectiveUnsignedCoefficientMap_rank_one
    (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) (G : ProjectiveBundleTautologicalSystem.{u} 0)
    (T : Scheme.{u}) (F : T.Modules) (hF : projectiveBundleRank T 0 F)
    (a : T ⟶ Spec (.of P.field.k)) :
    Function.Bijective (P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a
      (G.bundle T F hF) (G.invertible T F hF) 1) := by
  obtain ⟨_, hIso⟩ := G.rank_zero T F hF rfl
  have := hIso
  have heval : Function.Bijective
      (fun c : ∀ i : Fin 1, ordinaryFiniteCohomology P T (i.val + 1) ↦ c 0) := by
    constructor
    · intro c d h
      funext i
      have hi := Fin.eq_zero i
      subst i
      exact h
    · intro d
      refine ⟨fun i ↦ ?_, ?_⟩
      · have hi := Fin.eq_zero i
        subst i
        exact d
      · rfl
  have heq : P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a
      (G.bundle T F hF) (G.invertible T F hF) 1 =
      P.ordinaryFiniteCohomologyPullback t (G.bundle T F hF).A.data.relProjHom
        (P.diagonalExponent_isUnit a) 1 ∘
          (fun c : ∀ i : Fin 1, ordinaryFiniteCohomology P T (i.val + 1) ↦ c 0) := by
    funext c
    simp only [ordinaryFiniteProjectiveUnsignedCoefficientMap, Fin.sum_univ_one,
      Fin.val_zero, eqToHom_refl, Category.comp_id, Function.comp_apply]
    rfl
  rw [heq]
  exact (P.ordinaryFiniteCohomologyPullback_bijective t
    (G.bundle T F hF).A.data.relProjHom (P.diagonalExponent_isUnit a) 1).comp heval

/-- The unsigned, reverse-ordered coefficient map is bijective for the normalized
projective bundle of a bundle of rank at least two. The conclusion holds for every class
in H^(2r)(P(F),A(r)), not only for the specific class h^r.
Source: Stacks Tag 0FI5, proposition-chern-class, proof before equation-chern-classes;
blueprint localized-top-Chern Step 4, ordinary splitting-principle definition.
(blueprint: lem-pur-chern-coefficient-bijective).

Proof:
1. Apply projectiveBundleFormula to G, n+1, F, and the given normalized transport.
The proved projectiveBundleComponentSum_bijective identifies Hom into its target
with the sum of the specified components, retaining their actual formula.
2. Apply Hom(A(-r)[-2r],-) to this isomorphism, where r=n+2. Finite
biproducts identify the source with the product of Hom(A(-r)[-2r],A(-j)[-2j]).
The proved ordinaryFinitePositiveTwistEtale_isInvertible supplies invertibility
of every positive ordered power. The proved ordinaryFiniteCohomologyComparison_bijective
lifts every pro-etale input coordinate to its unique etale arrow. Tate duality
identifies each factor with H^(2(r-j))(T,A(r-j)),
using evaluation and tensor-Hom adjunction. The ordinary pullback/direct-image
adjunction and the same Tate duality identify the target with H^(2r)(P(F),A(r)).
3. Use the proved ordinaryFiniteProjectiveUnsignedCoefficientMap_postcompose
to write the actual target map using fixed coefficient arrows. Evaluate the
Hom-coordinate composite on each coproduct injection. The defining adjunct of
the injection is cup evaluation against h^j. Naturality of evaluation and the
triangle identities identify its transpose with pullback of a coefficient cup
h^j. Exact monoidal site comparison gives the same ordered recursive product
as ordinaryFiniteHyperplaneProduct. All shifted degrees are even, so the
symmetry introduces no sign. This identifies the actual map, not just its source
and target, with the unsigned coefficient sum.
4. Reindex by j=r-i, for 1<=i<=r. This gives the displayed unsigned map;
the alternating signs are handled separately by the proved sign involution in
PurityChernClassAssembly.
The finite coproduct and adjunction arguments also hold over the empty base. -/
theorem ordinaryFiniteProjectiveUnsignedCoefficientMap_bijective (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) (n : ℕ) (G : ProjectiveBundleTautologicalSystem.{u} (n + 1))
    (T : Scheme.{u}) (F : T.Modules) (hF : projectiveBundleRank T (n + 1) F)
    (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    Function.Bijective (P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a
      (G.bundle T F hF) (G.invertible T F hF) (n + 2)) := by sorry

end WeilConjectures.PurityFiniteSetting
