/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections

/-! # Compatible SL₂ parametrizations of opposite root subgroups

Source: Milne, Algebraic Groups (2017), Theorem 21.11(b)--(e), pp.429--430,
and paragraph 21.24, p.432 (blueprint: lem-sfb-opposite-root-sl2-parametrizations).

The root datum lives on the actual character and cocharacter Hom groups. Its coroot
is identified with the geometric coroot by the normalizer reflection identity from
21.11(e). The two given root subgroups are identified by their character tangent spaces,
as in the recorded root-subgroup theorem. `RankOneRoots.SL2Hom` is the natural family
on determinant-one matrices over every commutative algebra, hence a group-scheme map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Opposite root subgroups admit simultaneous rank-one parametrizations, with the
prescribed canonical coroot as diagonal restriction. The reflection compatibility
specifies the word "canonical": an abstract root datum with the same roots and pairing
but an unrelated coroot is not substituted for the root datum of the group.

Source: Milne, Theorem 21.11(b)--(e), pp.429--430, and 21.24, p.432
(blueprint: lem-sfb-opposite-root-sl2-parametrizations).

Proof plan:
1. Apply lem-sfb-reductive-rank-one-reflections to the centralizer of the largest
   subtorus of ker(alpha). It is reductive of semisimple rank one, and contains
   the alpha tangent weight. Apply lem-sfb-split-rank-one-classification to identify
   it, with its torus, with Z times SL2, PGL2, or GL2.
2. In these models use M ↦ (1,M), M ↦ (1,[M]), or M ↦ (1,M). The upper and lower
   unitriangular groups are closed copies of Ga. For PGL2 use
   lem-sfb-projective-frames-pgl: in determinant-open projective matrix coordinates,
   the equations a=d,c=0 or a=d,b=0 imply d is invertible, giving the coordinates
   [1,b/d,0,1] and [1,0,c/d,1] over every test algebra.
3. Conjugation by the diagonal torus has nonzero tangent characters chi and -chi,
   also in characteristic two. The root alpha is one of these two characters.
   The one-dimensional tangent spaces and uniqueness in
   lem-sfb-reductive-root-subgroup-parametrizations identify the two subgroups
   with the given U_alpha and U_(-alpha), in the appropriate order.
4. For w = [[0,-1],[1,0]], the normalizer reflection on T satisfies
   n⁻¹tn = t nu(chi(t)⁻¹), where nu is the model diagonal cocharacter.
   Applying every character gives x ↦ x - <x,nu>chi. Uniqueness of the coroot
   in lem-sfb-reductive-rank-one-reflections identifies the given canonical
   alpha coroot with nu or -nu. This is an equality of cocharacters.
5. If alpha=chi use the displayed model map. If alpha=-chi precompose with
   conjugation by w. It exchanges upper and lower parameters by a ↦ -a and
   replaces diag(s,s⁻¹) by diag(s⁻¹,s). Compose with the model isomorphism and
   inclusion in G. Both restrictions are isomorphisms, and the diagonal is the
   prescribed coroot. The formulas hold for nonreduced algebras and in every
   characteristic. The assertion is vacuous if the root set is empty. -/
theorem opposite_root_sl2_parametrizations
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (i : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    [aG : ModObj T.X G.X]
    (hconj : aG.smul = RankOneRoots.adjointMap i)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (hroot : ∀ β : Φ, P.root β = β.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ TorusCharacterTangent.weightSpace T G χ.toMul ≠ ⊥)
    (α : Φ)
    (hcanonical : ∃ n : RankOneRoots.normalizer i,
      (𝟙 T.X / ((P.root α).toMul.hom.hom ≫ (P.coroot α).toMul.hom.hom)) ≫
          i.hom.hom =
        (toUnit T.X ≫ n.val)⁻¹ * i.hom.hom * (toUnit T.X ≫ n.val))
    (Uplus Uminus : Grp (Over (Spec (.of F))))
    (jplus : Uplus ⟶ G) (jminus : Uminus ⟶ G)
    (hplus : IsClosedSubgroupScheme jplus.hom.hom ∧ Smooth Uplus.X.hom ∧
      ConnectedSpace Uplus.X.left ∧ TorusCharacterTangent.IsStable T G jplus ∧
      (GrpObj.differential jplus.hom.hom).toLinearMap.range =
        TorusCharacterTangent.weightSpace T G α.val.toMul)
    (hminus : IsClosedSubgroupScheme jminus.hom.hom ∧ Smooth Uminus.X.hom ∧
      ConnectedSpace Uminus.X.left ∧ TorusCharacterTangent.IsStable T G jminus ∧
      (GrpObj.differential jminus.hom.hom).toLinearMap.range =
        TorusCharacterTangent.weightSpace T G (-α.val).toMul) :
    ∃ (v : RankOneRoots.SL2Hom G)
      (eplus : Grp.mk (StandardGroupSchemes.additive F) ≅ Uplus)
      (eminus : Grp.mk (StandardGroupSchemes.additive F) ≅ Uminus),
      (∀ (A : CommAlgCat.{u} F) (a : A) (g : Matrix.SpecialLinearGroup (Fin 2) A),
        g.val = !![1, a; 0, 1] →
          v.app A g = TorusCharacterTangent.additiveParameterPoint F a ≫
            eplus.hom.hom.hom ≫ jplus.hom.hom) ∧
      (∀ (A : CommAlgCat.{u} F) (a : A) (g : Matrix.SpecialLinearGroup (Fin 2) A),
        g.val = !![1, 0; a, 1] →
          v.app A g = TorusCharacterTangent.additiveParameterPoint F a ≫
            eminus.hom.hom.hom ≫ jminus.hom.hom) ∧
      (∀ (A : CommAlgCat.{u} F)
        (s : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F)
        (g : Matrix.SpecialLinearGroup (Fin 2) A),
        g.val = !![RankOneRoots.multiplicativeValue A s, 0;
          0, RankOneRoots.multiplicativeValue A s⁻¹] →
          v.app A g = s ≫ (P.coroot α).toMul.hom.hom ≫ i.hom.hom) := by
  sorry

end AlgebraicGeometry
