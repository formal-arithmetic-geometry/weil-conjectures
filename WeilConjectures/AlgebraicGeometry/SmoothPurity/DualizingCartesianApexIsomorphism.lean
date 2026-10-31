/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedExceptionalExchangeApexPasting
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Exceptional base change after replacing a Cartesian apex

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, proof (1)
(blueprint: lem-pur-dualizing-cartesian-apex-isomorphism).

The statement is on ordinary unbounded small-etale derived categories with finite
constant coefficients.  The comparison of right adjoints is the mate of the
canonical compact-support comparison supplied by
`unboundedEtaleApexSupportIso`; the two equalities below retain the canonical
inverse-image compositor and the coefficient-unit constraint.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The counit-normalized right-adjoint comparison for an isomorphic source.
It is the mate of the compact-support comparison, transported from termwise pullback
using the canonical comparison with left derived pullback. The identity functor and
its unitors are explicit, fixing the conjugation convention.
Source: latest blueprint base-change factors, proof (1)
(blueprint: lem-pur-dualizing-cartesian-apex-isomorphism). -/
noncomputable def cartesianApexExceptionalComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P T : Scheme.{u}} (e : Z ≅ P) (r : P ⟶ T)
    [HasCompactification r] [HasCompactification (e.hom ≫ r)]
    [QuasiCompact (e.hom ≫ r)] :
    rightDerivedUpperShriek A r ⋙ L((e.hom)^*[ModuleCat.{u + 1} A]) ⟶
      rightDerivedUpperShriek A (e.hom ≫ r) :=
  (mateEquiv (rightDerivedUpperShriekAdjunction A r)
    (rightDerivedUpperShriekAdjunction A (e.hom ≫ r))
    (TwoSquare.mk L((e.hom)^*[ModuleCat.{u + 1} A])
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) r)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r))
      (𝟭 (DerivedCategoryModule A T))
      ((Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e.hom)
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)) ≪≫
        unboundedEtaleApexSupportIso A e r).hom ≫
        (Functor.rightUnitor _).inv))).natTrans ≫
    (Functor.leftUnitor _).hom

/-- Exceptional exchange and its dualizing component after replacing a Cartesian apex.
The comparison is the prescribed counit mate; both displayed compositions are left
to right. Cartesian proof witnesses are arbitrary.
Source: latest blueprint base-change factors, proof (1)
(blueprint: lem-pur-dualizing-cartesian-apex-isomorphism).

Proof:
1. Compactify r by (j,s), and h by (je,s). The unbounded compact-support comparison
   identifies these with the chosen compactifications. Its compositor inverse followed
   by the invertible isomorphism extension/restriction counit is precisely
   unboundedEtaleApexSupportIso. Refinement cocycles remove the computational choices.
2. Take its mate under the fixed compact-support adjunctions, using
   def-weil-pbc-adjunction-mate and def-weil-pbc-adjunction-conjugate. This gives the
   comparison defined above. Applying the same construction to e inverse and the
   canonical pullback unit/compositors gives its inverse by mate-pasting.
3. Invert the left-adjoint identity of
   lem-pur-unbounded-exceptional-exchange-apex-pasting. Mate-pasting gives Pe(beta_q)
   followed by J at PvK, and naturality in the source functor inserts m at EfK.
   The comparison between exact and left derived pullback gives the displayed formula.
4. Evaluate at A_Y. Naturality of J against the canonical unit identification
   Pv(A_Y) ≅ A_T moves that identification before J(A_T). This is exactly the
   dualizing formula below, where J(A_T) is B_e.
5. The unbounded refinement cocycle gives compactification independence. The supplied
   pullback identification determines the open leg uniquely, and proof irrelevance
   removes Cartesian proof witnesses. These arguments include identity e, empty schemes,
   the zero ring, zero objects, and arbitrary unbounded complexes. -/
theorem dualizing_cartesian_apex_isomorphism
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y T P Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian T]
    [IsNoetherian P] [IsNoetherian Z]
    {f : X ⟶ Y} {v : T ⟶ Y} {p : P ⟶ X} {r : P ⟶ T}
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [IsSeparated r] [QuasiCompact r] [HasCompactification r]
    (q : ChosenCartesianSquare p r f v) (e : Z ≅ P)
    [IsSeparated (e.hom ≫ r)] [QuasiCompact (e.hom ≫ r)]
    [HasCompactification (e.hom ≫ r)]
    (q_e : IsPullback (e.hom ≫ p) (e.hom ≫ r) f v) :
    IsIso (cartesianApexExceptionalComparison A e r) ∧
    (∀ K : DerivedCategoryModule A Y,
      (rightDerivedUpperShriekBaseChangeMap A q_e).app K =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
            ((rightDerivedUpperShriek A f).obj K) ≫
          L((e.hom)^*[ModuleCat.{u + 1} A]).map
            ((rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_iso_pullback q.toCommSq q.isoPullback q.hom_fst q.hom_snd)).app K) ≫
          (cartesianApexExceptionalComparison A e r).app
            (L((v)^*[ModuleCat.{u + 1} A]).obj K)) ∧
    dualizingComplexBaseChangeMap A q_e =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
          (dualizingComplex A f) ≫
        L((e.hom)^*[ModuleCat.{u + 1} A]).map
          (dualizingComplexBaseChangeMap A
            (IsPullback.of_iso_pullback q.toCommSq q.isoPullback q.hom_fst q.hom_snd)) ≫
        (cartesianApexExceptionalComparison A e r).app
          (𝟙_ (DerivedCategoryModule A T)) := by
  let α := TwoSquare.mk
      (L((e.hom)^*[ModuleCat.{u + 1} A]))
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) r)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r))
      (𝟭 (DerivedCategoryModule A T))
      ((Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e.hom)
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)) ≪≫
        unboundedEtaleApexSupportIso A e r).hom ≫
        (Functor.rightUnitor _).inv)
  have hα : IsIso α.natTrans := by
    dsimp [α]
    infer_instance
  have hm : IsIso (mateEquiv (rightDerivedUpperShriekAdjunction A r)
      (rightDerivedUpperShriekAdjunction A (e.hom ≫ r)) α).natTrans := by
    exact isIso_mateEquiv_of_isEquivalence
      (rightDerivedUpperShriekAdjunction A r)
      (rightDerivedUpperShriekAdjunction A (e.hom ≫ r)) α
  let : IsIso (mateEquiv (rightDerivedUpperShriekAdjunction A r)
      (rightDerivedUpperShriekAdjunction A (e.hom ≫ r)) α).natTrans := hm
  let sq := IsPullback.of_iso_pullback q.toCommSq q.isoPullback q.hom_fst q.hom_snd
  let τ := Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e.hom)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)) ≪≫
    unboundedEtaleApexSupportIso A e r
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e.hom p
  have hex (M : DerivedCategoryModule A X) :
      (rightDerivedLowerShriekBaseChangeMap A q_e).app M =
        (rightDerivedLowerShriekBaseChangeMap A sq).app M ≫
          τ.inv.app ((L((p)^*[ModuleCat.{u + 1} A])).obj M) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)).map
            (c.inv.app M) := by
    have h := congr_app (unboundedEtaleCompactSupportExchange_apex_pasting A q e q_e) M
    simp only [unboundedEtaleCompactSupportBaseChange, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.assoc] at h
    apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) v).inv.app _)).mp
    apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) (e.hom ≫ p)).hom.app M))).mp
    simp only [τ, c, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    simp only [leftDerivedUpperStarIsoMapDerivedCategory, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Category.comp_id] at h ⊢
    simp only [unboundedEtaleUpperStarCompIso, Iso.trans_inv, NatTrans.comp_app,
      Functor.map_comp, Category.id_comp] at h ⊢
    have hn := (unboundedEtaleApexSupportIso A e r).inv.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).hom.app M)
    dsimp only [leftDerivedUpperStarIsoMapDerivedCategory,
      Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn]
    exact h
  have hβ (K : DerivedCategoryModule A Y) :
      (rightDerivedUpperShriekBaseChangeMap A q_e).app K =
        c.hom.app ((rightDerivedUpperShriek A f).obj K) ≫
          L((e.hom)^*[ModuleCat.{u + 1} A]).map
            ((rightDerivedUpperShriekBaseChangeMap A sq).app K) ≫
          (cartesianApexExceptionalComparison A e r).app
            (L((v)^*[ModuleCat.{u + 1} A]).obj K) := by
    let := isIso_rightDerivedLowerShriekBaseChangeMap A sq
    let := isIso_rightDerivedLowerShriekBaseChangeMap A q_e
    have hi (M : DerivedCategoryModule A X) :
        inv ((rightDerivedLowerShriekBaseChangeMap A q_e).app M) =
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)).map
              (c.hom.app M) ≫
            τ.hom.app ((L((p)^*[ModuleCat.{u + 1} A])).obj M) ≫
            inv ((rightDerivedLowerShriekBaseChangeMap A sq).app M) := by
      have he : (asIso (rightDerivedLowerShriekBaseChangeMap A q_e)).app M =
          (asIso (rightDerivedLowerShriekBaseChangeMap A sq)).app M ≪≫
            τ.symm.app _ ≪≫
            (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)).mapIso
              (c.symm.app M) := by
        apply Iso.ext
        exact hex M
      simpa only [Iso.app_inv, asIso_inv, Iso.trans_inv, Functor.mapIso_inv,
        Iso.symm_inv, Category.assoc, NatIso.isIso_inv_app] using congrArg Iso.inv he
    have hJ (N : DerivedCategoryModule A T) :
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)).map
            ((cartesianApexExceptionalComparison A e r).app N) ≫
          (rightDerivedUpperShriekAdjunction A (e.hom ≫ r)).counit.app N =
        τ.hom.app ((rightDerivedUpperShriek A r).obj N) ≫
          (rightDerivedUpperShriekAdjunction A r).counit.app N := by
      have hc := mateEquiv_counit (rightDerivedUpperShriekAdjunction A r)
        (rightDerivedUpperShriekAdjunction A (e.hom ≫ r)) α N
      have hαapp : α.app ((rightDerivedUpperShriek A r).obj N) =
          τ.hom.app ((rightDerivedUpperShriek A r).obj N) := by
        change τ.hom.app _ ≫ 𝟙 _ = _
        exact Category.comp_id _
      dsimp only [Functor.id_map, Functor.id_obj] at hc
      rw [hαapp] at hc
      dsimp only [cartesianApexExceptionalComparison, NatTrans.comp_app,
        Functor.leftUnitor_hom_app]
      erw [Category.comp_id]
      set_option maxRecDepth 4096 in
        exact hc
    have hb (sq' : IsPullback (e.hom ≫ p) (e.hom ≫ r) f v) :
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)).map
            ((rightDerivedUpperShriekBaseChangeMap A sq').app K) ≫
          (rightDerivedUpperShriekAdjunction A (e.hom ≫ r)).counit.app
            (L((v)^*[ModuleCat.{u + 1} A]).obj K) =
        inv ((rightDerivedLowerShriekBaseChangeMap A sq').app
            ((rightDerivedUpperShriek A f).obj K)) ≫
          (L((v)^*[ModuleCat.{u + 1} A])).map
            ((rightDerivedUpperShriekAdjunction A f).counit.app K) := by
      simpa only [rightDerivedUpperShriekBaseChangeMap, NatIso.isIso_inv_app] using
        mateEquiv_counit (rightDerivedUpperShriekAdjunction A f)
          (rightDerivedUpperShriekAdjunction A (e.hom ≫ r))
          (inv (rightDerivedLowerShriekBaseChangeMap A sq')) K
    have hbq := mateEquiv_counit (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction A r)
      (inv (rightDerivedLowerShriekBaseChangeMap A sq)) K
    change (rightDerivedLowerShriek (ModuleCat.{u + 1} A) r).map
        ((rightDerivedUpperShriekBaseChangeMap A sq).app K) ≫ _ = _ at hbq
    apply ((rightDerivedUpperShriekAdjunction A (e.hom ≫ r)).homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [hb q_e, hJ]
    have hn := τ.hom.naturality ((rightDerivedUpperShriekBaseChangeMap A sq).app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [reassoc_of% hn, hbq, hi]
    simp only [Category.assoc, NatIso.isIso_inv_app]
  refine ⟨?_, hβ, ?_⟩
  · change IsIso ((mateEquiv (rightDerivedUpperShriekAdjunction A r)
        (rightDerivedUpperShriekAdjunction A (e.hom ≫ r)) α).natTrans ≫
      (Functor.leftUnitor _).hom)
    infer_instance
  · have hn := (cartesianApexExceptionalComparison A e r).naturality
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom
    dsimp only [Functor.comp_map] at hn
    simp only [dualizingComplexBaseChangeMap, hβ, Functor.map_comp, Category.assoc]
    dsimp only [dualizingComplex] at *
    rw [← hn]

end AlgebraicGeometry.Etale
