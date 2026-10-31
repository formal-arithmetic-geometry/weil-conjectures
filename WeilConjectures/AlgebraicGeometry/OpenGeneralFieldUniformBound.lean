/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimensionSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.Sites.HigherDirectImageAffineEtaleBound
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension

/-!
# Uniform higher direct-image bound over a general field

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md,
“(1') at the finite stage”, the general-field bound in returned step 16.
(blueprint: lem-sf-open-general-field-uniform-bound)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem empty_cohomology (Y : Scheme.{u}) [IsEmpty Y]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} Y q).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  have : (cohomology AddCommGrpCat.{u + 1} Y q).Additive := by
    dsimp [cohomology, rightDerivedGlobalSections]
    infer_instance
  exact Functor.map_isZero _ (Functor.map_isZero _
    (Scheme.Etale.isZero_sheaf_of_isEmpty F))

private theorem finiteType_cd_le
    (k : Type u) [Field k] (c d : ℕ)
    (hc : Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c)
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a]
    (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) :
    Scheme.HasTorsionEtaleCohomologicalDimensionLE Y (2 * d + c) := by
  classical
  cases isEmpty_or_nonempty Y with
  | inl h =>
    let := h
    intro F _ q _
    exact AddCommGrpCat.isZero_iff_subsingleton.mp (empty_cohomology Y F q)
  | inr h =>
    have hnonneg : 0 ≤ topologicalKrullDim Y := by
      apply Order.krullDim_nonneg_iff.mpr
      obtain ⟨x⟩ := h
      exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have hnat : ∃ e : ℕ, topologicalKrullDim Y = (e : WithBot ℕ∞) := by
      generalize topologicalKrullDim Y = n at *
      induction n using WithBot.recBotCoe with
      | bot => exact False.elim (not_le_of_gt
          (by decide : (⊥ : WithBot ℕ∞) < 0) hnonneg)
      | coe n =>
        induction n using ENat.recTopCoe with
        | top => exact False.elim (not_le_of_gt
            (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d)) hd)
        | coe n => exact ⟨n, rfl⟩
    obtain ⟨e, he⟩ := hnat
    have hed : e ≤ d := by exact_mod_cast he ▸ hd
    let : Y.Over (Spec (.of k)) := ⟨a⟩
    have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType a)
    have : QuasiCompact (Y ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact a)
    intro F hF q hq
    exact Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType k c e hc Y he
      F hF q (by omega)

private noncomputable def higher_comparison
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (j : U ⟶ X)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ) :
    (moduleAbelianForget A X).obj (higherDirectImage A j q M) ≅
      (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlus.obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((moduleAbelianForget A U).obj M))) := by
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M
  exact ((moduleAbelianForget A X).mapDerivedCategoryPlusHomologyFunctorIso q).app
      ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlus.obj K) ≪≫
    (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((moduleAbelianDerivedLowerStarIso A j).app K) ≪≫
    (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlus.mapIso
        (((moduleAbelianForget A U).mapDerivedCategoryPlusSingleFunctor 0).app M))

/-- For an open immersion into a separated finite-type scheme over a field of torsion
cohomological dimension at most `c`, the bound `2d+c` holds for every module sheaf over
any finite commutative ring killed by a power of the invertible prime `ℓ`. Here
`d = ((topologicalKrullDim U).unbotD 0).toNat` is the dimension of the nonempty finite-type
scheme `U`, and is zero for the empty scheme. Affine étale test pullbacks are finite type
of dimension at most `d`, and every primary torsion sheaf on them has the same vanishing
bound. Abelian sheaves in this clause are represented as modules over lifted integers,
which have exactly their canonical integer action. The third clause records agreement
of higher module and abelian direct images after forgetting coefficients. The last
clause includes every integer degree when the open is empty.

Source: main-20261015 blueprint, sec-smooth-purity/sk-prop-sf-localization/
prop-sf-localization-all-stages.proof.md, “(1') at the finite stage”, returned step 16.
(blueprint: lem-sf-open-general-field-uniform-bound)

Proof:
1. Finite type over the field makes X locally Noetherian. Every open immersion into X
   is quasi-compact, so U is finite type over k. Its finite dimension agrees with the
   natural-number conversion used in the statement, with dimension zero for empty U.
2. For affine etale V over X, quasi-compactness of V and quasi-separatedness of X
   make V -> X quasi-compact. Thus W = V x_X U is finite type over k. The etale
   projection W -> U does not increase dimension: it sends strict specialization
   chains to strict chains, since its fibres are discrete.
3. Apply the finite-type torsion cohomological bound to nonempty W of dimension e <= d.
   Its bound 2e+c implies 2d+c. For empty W every abelian sheaf is zero. A primary
   torsion module sheaf has torsion stalks, hence its underlying abelian sheaf is locally
   torsion; this gives the affine-test cohomology clause in every requested degree.
4. Every sheaf of modules over the finite ring A has torsion underlying abelian sheaf.
   Apply the existing affine-etale-test higher-direct-image vanishing criterion using
   the bound of step 3. This criterion supplies the sheafification and affine-cover
   argument for abelian higher direct images.
5. Apply the canonical module/abelian derived direct-image isomorphism to M[0]. Exact
   forgetting commutes with homology and single complexes, yielding the comparison
   clause. Faithfulness of forgetting reflects zero objects and gives module vanishing.
6. If U is empty every sheaf on U is zero, so additive single, derived direct-image,
   cohomology, and homology functors send it to zero in all integer degrees. Every
   pullback W is empty as well, via its projection to U. -/
theorem openImmersion_generalField_uniformBound
    (k : Type u) [Field k] (c : ℕ)
    (hc : Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))
    {U X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ℓ : A) ^ r = 0) :
    (∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
      (2 * ((topologicalKrullDim U).unbotD 0).toNat + c : ℕ) < q →
        IsZero (higherDirectImage A j q M)) ∧
    (∀ (V : X.Etale) [IsAffine V.left],
      LocallyOfFiniteType (pullback.fst V.hom j ≫ V.hom ≫ aX) ∧
      QuasiCompact (pullback.fst V.hom j ≫ V.hom ≫ aX) ∧
      topologicalKrullDim (pullback V.hom j : Scheme.{u}) ≤
        (((topologicalKrullDim U).unbotD 0).toNat : WithBot ℕ∞) ∧
      ∀ (F : Sheaf (pullback V.hom j).smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F ℓ →
        ∀ q : ℤ, (2 * ((topologicalKrullDim U).unbotD 0).toNat + c : ℕ) < q →
          IsZero ((cohomology AddCommGrpCat.{u + 1} (pullback V.hom j) q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((moduleAbelianForget (ULift.{u + 1} ℤ) (pullback V.hom j)).obj F)))) ∧
    (∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
      Nonempty ((moduleAbelianForget A X).obj (higherDirectImage A j q M) ≅
        (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlus.obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((moduleAbelianForget A U).obj M))))) ∧
    (IsEmpty U →
      (∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
        IsZero (higherDirectImage A j q M)) ∧
      (∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ),
        IsZero ((cohomology AddCommGrpCat.{u + 1} U q).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
      (∀ (V : X.Etale) [IsAffine V.left]
          (F : Sheaf (pullback V.hom j).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ),
        IsZero ((cohomology AddCommGrpCat.{u + 1} (pullback V.hom j) q).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
      (∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ),
        IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlus.obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))))) := by
  classical
  have _ := hℓk
  have _ := hA
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : QuasiCompact j := inferInstance
  have : LocallyOfFiniteType (j ≫ aX) := inferInstance
  have : QuasiCompact (j ≫ aX) := inferInstance
  let d := ((topologicalKrullDim U).unbotD 0).toNat
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le (j ≫ aX)
  have hfinite : (topologicalKrullDim U).unbotD 0 ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (n : ℕ∞) ≠ ⊤ by simp)
    exact (WithBot.unbotD_le_iff (by simp)).2 hn
  have hdimU : topologicalKrullDim U ≤ (d : WithBot ℕ∞) := by
    change topologicalKrullDim U ≤
      ((((topologicalKrullDim U).unbotD 0).toNat : ℕ∞) : WithBot ℕ∞)
    rw [ENat.natCast_toNat hfinite]
    exact WithBot.le_coe_unbotD _ _
  have hgeom (V : X.Etale) [IsAffine V.left] :
      LocallyOfFiniteType (pullback.fst V.hom j ≫ V.hom ≫ aX) ∧
      QuasiCompact (pullback.fst V.hom j ≫ V.hom ≫ aX) ∧
      topologicalKrullDim (pullback V.hom j : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
    have : AlgebraicGeometry.Etale V.hom := V.prop
    have : IsAffine ((𝟭 Scheme.{u}).obj V.left) := ‹IsAffine V.left›
    have : CompactSpace V.left := Scheme.compactSpace_of_isAffine V.left
    have : QuasiCompact V.hom :=
      @quasiCompact_of_compactSpace V.left X V.hom inferInstance inferInstance
    refine ⟨inferInstance, inferInstance, ?_⟩
    exact (pullback.snd V.hom j).topologicalKrullDim_le_of_etale.trans hdimU
  have hcd : ∀ {W : Scheme.{u}} (w : W ⟶ X) [AlgebraicGeometry.Etale w] [IsAffine W],
      Scheme.HasTorsionEtaleCohomologicalDimensionLE (pullback w j) (2 * d + c) := by
    intro W w _ _
    let V : X.Etale := Scheme.Etale.mk w
    have : IsAffine V.left := inferInstanceAs (IsAffine W)
    obtain ⟨ht, hq, hd⟩ := hgeom V
    exact finiteType_cd_le k c d hc (pullback.fst w j ≫ w ≫ aX) hd
  refine ⟨?_, ?_, fun M q ↦ ⟨higher_comparison A j M q⟩, ?_⟩
  · intro M q hq
    have htor : ((moduleAbelianForget A U).obj M).IsTorsion :=
      (Scheme.isTorsionModuleSheaf_iff_isTorsion M).mp
        (Scheme.IsTorsionModuleSheaf.of_isTorsion isAddTorsion_of_finite M)
    have hz := isZero_higherDirectImage_of_affineEtale_cd j (2 * d + c) hcd
      ((moduleAbelianForget A U).obj M) htor q hq
    have hz' := hz.of_iso (higher_comparison A j M q)
    rw [IsZero.iff_id_eq_zero] at hz' ⊢
    apply (moduleAbelianForget A X).map_injective
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact hz'
  · intro V _
    obtain ⟨ht, hq, hd⟩ := hgeom V
    refine ⟨ht, hq, hd, ?_⟩
    intro F hF q hq
    have htor : ((moduleAbelianForget (ULift.{u + 1} ℤ) (pullback V.hom j)).obj F).IsTorsion := by
      apply (Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp
      constructor
      intro Ω _ _ s x
      obtain ⟨r, hr⟩ := hF Ω s x
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨ℓ ^ r, pow_pos hℓ.pos r, hr⟩
    have : AlgebraicGeometry.Etale V.hom := V.prop
    have : IsAffine ((𝟭 Scheme.{u}).obj V.left) := ‹IsAffine V.left›
    have hq' : q = (q.toNat : ℤ) := by omega
    rw [hq']
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr
      (hcd V.hom _ htor q.toNat (by omega))
  · intro hU
    let := hU
    refine ⟨?_, empty_cohomology U, ?_, ?_⟩
    · intro M q
      exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _
        (Scheme.Etale.isZero_sheaf_of_isEmpty M)))
    · intro V _ F q
      have : IsEmpty (pullback V.hom j : Scheme.{u}) :=
        ⟨fun x ↦ isEmptyElim ((pullback.snd V.hom j).base x)⟩
      exact empty_cohomology _ F q
    · intro F q
      exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _
        (Scheme.Etale.isZero_sheaf_of_isEmpty F)))

end AlgebraicGeometry.Etale
