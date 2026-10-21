/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q118 and A6
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerBaseChange

/-! # The ordinary etale projective-line decomposition

Source: main-20261015, thm-amb-p1-decomposition.md and its proof
(blueprint: thm-amb-p1-decomposition).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize


private theorem biprodMap_isIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (X Y : C) {X' Y' : D} (e : F.obj X ≅ X')
    (e' : F.obj Y ≅ Y') :
    IsIso (biprod.lift (F.map biprod.fst ≫ e.hom) (F.map biprod.snd ≫ e'.hom)) := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let q := Functor.mapBiprod F X Y ≪≫ biprod.mapIso e e'
  have h : q.hom = biprod.lift (F.map biprod.fst ≫ e.hom)
      (F.map biprod.snd ≫ e'.hom) := by
    ext <;> simp [q]
  rw [← h]
  infer_instance

private theorem biprodMap_desc {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} {X' Y' Z' : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) (a' : X' ⟶ Z') (b' : Y' ⟶ Z')
    (e : F.obj X ≅ X') (e' : F.obj Y ≅ Y') (v : F.obj Z ⟶ Z')
    (ha : F.map a ≫ v = e.hom ≫ a') (hb : F.map b ≫ v = e'.hom ≫ b') :
    F.map (biprod.desc a b) ≫ v =
      p1DecompositionBiprodMap F X Y X' Y' e e' ≫ biprod.desc a' b' := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  apply (cancel_epi (F.mapBiprod X Y).inv).mp
  apply biprod.hom_ext' <;>
    simp [p1DecompositionBiprodMap, ← Functor.map_comp_assoc, ha, hb]

/-- The Kummer-normalized projective-line decomposition and its compatibility with
every change of base, including non-Noetherian S'. The existential Chern morphisms
are fixed by `ordinaryFiniteP1ChernSpec`, the actual scalar-extended Kummer boundary.
Source: main-20261015, thm-amb-p1-decomposition.md and its proof
(blueprint: thm-amb-p1-decomposition).

Proof:
1. Use lem-asd-ordinary-finite-p1-adjunction for the twisted decomposition b_q.
   Projective space is proper (lemma-nagata-projective-space-base-change-proper),
   and its source is Noetherian by pqf-lem-locnoeth-lft and quasi-compactness.
   Tensor b_q with A_S(-1)[-2], and apply lem-amb-proper-coproducts-projection.
   The normalized twist pullback and evaluation of lem-asd-etale-finite-twist-pullback
   identify the two summands with A_S and A_S(-1)[-2], and the target with Rq_*A_P.
   Counit naturality and the adjunction triangle identities identify the components:
   the first has identity adjoint, and the second has adjoint 1 tensor c followed by
   evaluation. More explicitly, put L=A_S(1)[2] and L_P=A_P(1)[2]. The first
   component before projection is 1_K tensor eta_L. Its adjoint is the identity by
   epsilon_(q,q^-1 L) composed with q^-1(eta_L) = 1. The second component is
   1_K tensor (Rq_*(c) composed with eta_A). Counit naturality and the same triangle
   identity give epsilon_LP composed with q^-1(Rq_*(c) composed with eta_A) = c.
   Tensoring by q^-1 K and evaluating is precisely the defining adjoint of h.
   Thus this map is exactly (1,h). No coefficient flatness is assumed.
2. For arbitrary g:S'->S, proper torsion-ring exchange is invertible by
   lem-kun-proper-base-change-torsion-ring. The infinity divisor has ideal (s) on
   its affine chart and unit ideal on the other; multiplication by s is injective
   over any ring and after every base change. Its dual ideal is the specified O(1).
   Hence lem-asd-ordinary-supported-kummer identifies the pulled-back class with
   the class over S'. The mate formula in def-kun-unbounded-exchange identifies
   the pulled-back closed-immersion unit with the new unit, so this also compares
   the unsupported Chern classes: for the divisor inclusion i, exchange composed
   with the pulled-back unit u_D equals u_D', since both have identity adjoint.
   Combining this with the supported-class exchange equation gives c_1'=g'^-1 c_1.
   Taking q' inverse-image adjoints then compares
   both components of (1,h). This gives the displayed commuting square. Its upper
   and exchange arrows are invertible, so (1,h') is invertible without requiring
   S' to be Noetherian or applying the projection theorem over S'. -/
theorem ordinaryFiniteP1Decomposition (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
        (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
      ordinaryFiniteP1ChernSpec A N hA S
        ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom) c ∧
      IsIso (p1DecompositionMap A N hN hA S hS c) ∧
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        ∃ c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
            (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧,
          ordinaryFiniteP1ChernSpec A N hA S'
            ((map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
              (((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom).map
                (ProjectiveLine S' ↘ S').appTop.hom)) c' ∧
          IsIso (p1DecompositionMap A N hN hA S'
            ((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom) c') ∧
          (ordinaryFinitePullback A g).map (p1DecompositionMap A N hN hA S hS c) ≫
              ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
              (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
                (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
            p1DecompositionSourceMap A N hN hA g hS ≫
              p1DecompositionMap A N hN hA S'
                ((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom) c' := by
  obtain ⟨t, d, _⟩ := exists_ordinaryFiniteP1Adjunction N hN A hA
  let c := (d S hS).chern
  have hc := (d S hS).chern_spec
  have hi : IsIso (p1DecompositionMap A N hN hA S hS c) := by
    apply isIso_p1DecompositionMap_of_twisted A N hN hA t S hS
    rw [← (d S hS).decomposition_hom]
    infer_instance
  refine ⟨c, hc, hi, ?_⟩
  intro S' g
  have : (ordinaryFinitePullback A g).Additive :=
    additive_leftDerivedUpperStar (ModuleCat.{u + 1} A) g
  let hS' : IsUnit (N : Γ(S', ⊤)) :=
    (map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom
  obtain ⟨c', hc', hu, hh⟩ :=
    ordinaryFiniteP1_components_baseChange A N hN hA g hS hS' c hc
  have he :
      (ordinaryFinitePullback A g).map (p1DecompositionMap A N hN hA S hS c) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
      p1DecompositionSourceMap A N hN hA g hS ≫
        p1DecompositionMap A N hN hA S' hS' c' := by
    exact biprodMap_desc (ordinaryFinitePullback A g)
      (p1DecompositionUnit A S) (p1DecompositionChernAdjoint A N hN hA S hS c)
      (p1DecompositionUnit A S') (p1DecompositionChernAdjoint A N hN hA S' hS' c')
      (ordinaryFiniteUnitPullback A g)
      (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)) _ hu hh
  have : IsIso (p1DecompositionSourceMap A N hN hA g hS) := by
    unfold p1DecompositionSourceMap p1DecompositionBiprodMap
    exact biprodMap_isIso (ordinaryFinitePullback A g) _ _ _ _
  have := isIso_ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S))
  have hi' : IsIso (p1DecompositionSourceMap A N hN hA g hS ≫
      p1DecompositionMap A N hN hA S' hS' c') := by
    rw [← he]
    infer_instance
  refine ⟨c', hc', ?_, he⟩
  simpa only [isIso_comp_left_iff] using hi'

end AlgebraicGeometry.Etale
