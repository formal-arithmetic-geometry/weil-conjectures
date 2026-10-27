/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
import Sheaf.AlgebraicGeometry.ModuleObjectPostnikovRoos
import Sheaf.Paper.QcqsProperSerreHeartBound
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
import Sheaf.Paper.PadicAlgClConstructibleScalarRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-!
# Uniform lower-tail bounds on the constructible finite-Tor localizing hull

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-qcqs-proper-hull-tail-bound).

The categories, truncation, and total direct image are the ordinary ambient module-object
constructions. Membership in the localizing hull is required only of the original object.
-/

@[expose] public section

set_option autoImplicit false

universe u uC vC uI

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem smallSupport
    {C : Type uC} [Category.{vC} C] [Preadditive C] [LocallySmall.{vC} C]
    {I : Type uI} (K : I → C) (t : Cofan K) (ht : IsColimit t) :
    Small.{vC} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : t.pt ⟶ K i := ht.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : t.inj j ≫ p i =
      Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    ht.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

private theorem closedUnderExistingCofan
    {C : Type uC} [Category.{vC} C] [Preadditive C] [LocallySmall.{vC} C]
    (S : ObjectProperty C)
    (hsmall : ∀ (J : Type vC) (K : J → C) (c : Cofan K),
      IsColimit c → (∀ j, S (K j)) → S c.pt)
    {I : Type uI} (K : I → C) (hK : ∀ i, S (K i)) (t : Cofan K) (ht : IsColimit t) :
    S t.pt := by
  classical
  have := smallSupport K t ht
  let J := {i // ¬ IsZero (K i)}
  let U : J → C := fun i ↦ K i.val
  let r : Cofan U := Cofan.mk t.pt (fun i ↦ t.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ ht.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change t.ι.app (Discrete.mk i) ≫ _ = _
      rw [ht.fac]
      simp only [Cofan.mk_ι_app, dif_pos hi]
    · intro s m hm
      apply ht.hom_ext
      intro ⟨i⟩
      rw [ht.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let e := (equivShrink.{vC} J).symm
  let V : Shrink.{vC} J → C := fun j ↦ U (e j)
  let r' : Cofan V := Cofan.mk t.pt (fun j ↦ r.inj (e j))
  have hr' : IsColimit r' := (Cofan.isColimitEquivOfEquiv e r) hr
  exact hsmall _ V r' hr' (fun j ↦ hK (e j).val)

/-- Proper direct image has a uniform upper bound on every lower truncation tail of an
object in the constructible finite-Tor localizing hull, over a qcqs base.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md, (2), first paragraph,
relative cohomological estimate (blueprint: lem-sfb-qcqs-proper-hull-tail-bound).

Proof plan:
1. The sheaf tensor theorem (lem-weil-pbc-sheaf-tensor-closed) and the module-object
   Grothendieck theorem (lem-sfb-modobj-grothendieck) make the source and target module
   categories Grothendieck abelian (def-sp-grothendieck-abelian). Exact coproducts and
   the source homology coproduct-preservation instance identify cohomology of a sum
   with the sum of cohomologies. Shrinking the nonzero support handles larger existing sums.
2. Use the weak Serre coproduct class P of lem-sfb-qcqs-proper-serre-heart-bound.
   Complexes whose cohomology lies in P are replete and shift stable. The long exact
   cohomology sequence (lem-sf-derived-homology-long-exact) expresses a triangle's middle
   cohomology as an extension of a cokernel by a kernel, so this class is triangulated.
   Step 1 makes it closed under sums. It contains the finite constant-model constructible
   finite-Tor generators (sk-def-sfb-constructible), hence their intersection-defined
   localizing hull (sk-def-localizing-closure). Good truncations (def-kun-truncations)
   retain cohomology in P, since the other cohomology objects are zero.
3. Choose d in N from the heart bound. The underived full module pushforward is additive
   and left exact (sk-def-sfb-module-pushforward-pullback); K-injective resolutions exist
   by lem-sfb-grothendieck-k-injective, and its total right derived functor is triangulated
   by lem-pc-right-derived-functor-triangulated. For L = tau_(le a-1) K, each bounded
   truncation L_n = tau_(ge -n) L has cohomology in P and no cohomology above a-1.
   Lemma lem-sfb-bounded-heart-amplitude-devissage gives vanishing of Rf_* L_n above
   a-1+d, uniformly in n. When -n > a-1 this truncation is zero.
4. Lemma lem-module-object-postnikov-roos gives the triangle Rf_* L -> P -> P ->
   (Rf_* L)[1], where P is the product of the Rf_* L_n and the middle arrow is 1-shift.
   Its product-cohomology assertion makes H^j(P) zero for j > a-1+d. For r > a+d,
   both H^(r-1)(P) and H^r(P) vanish, so the exact segment from
   lem-sf-derived-homology-long-exact gives H^r(Rf_* L) = 0. This applies to the ordinary
   unbounded L without membership in the hull or derived completeness.
5. Set c = d+1. Then r >= a+c implies r > a+d. This choice depends only on the fixed
   morphisms and coefficients. The zero object, empty schemes, and empty fibres are
   covered by the same argument.
-/
theorem exists_uniform_lowerTail_bound_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {S Y X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f] :
    ∃ c : ℕ, ∀ (a : ℤ)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingClosureProEtale Λ X K → ∀ r : ℤ, a + (c : ℤ) ≤ r →
        IsZero ((DerivedCategory.homologyFunctor _ r).obj
          ((moduleObjectDerivedPushforward Λ f).obj
            ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj K))) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let D := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  let P := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstantModelConstructible Λ X)
  let H := DerivedCategory.homologyProperty P
  let F := moduleObjectDerivedPushforward Λ f
  let : F.CommShift ℤ := by dsimp [F, moduleObjectDerivedPushforward]; infer_instance
  let : F.IsTriangulated := by dsimp [F, moduleObjectDerivedPushforward]; infer_instance
  let : IsGrothendieckAbelian.{u + 1} C := inferInstance
  let : HasColimitsOfSize.{u + 1, u + 1} C := IsGrothendieckAbelian.hasColimits C
  let : HasCoproducts.{u + 1} C := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  have hsum (I : Type (u + 1)) (K : I → DerivedCategory C)
      (c : Cofan K) (hc : IsColimit c) (hK : ∀ i, H (K i)) : H c.pt := by
    intro n
    let : HasColimitsOfShape (Discrete I) C :=
      HasColimitsOfSize.has_colimits_of_shape _
    let : HasExactColimitsOfShape (Discrete I) C := inferInstance
    let : PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor C n) :=
      DerivedCategory.preservesColimitsOfShape_homologyFunctor n
    exact P.prop_of_isColimit
      (isColimitOfPreserves (DerivedCategory.homologyFunctor C n) hc)
      (fun i ↦ hK i.as n)
  have hlocal : IsLocalizingSubcategory H := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I G hG hGP
    let := hG
    let K : I → DerivedCategory C := fun i ↦ G.obj ⟨i⟩
    let e : G ≅ Discrete.functor K := Discrete.natIsoFunctor
    let c : Cofan K := (Cocone.precompose e.inv).obj (colimit.cocone G)
    have hc : IsColimit c :=
      (IsColimit.precomposeInvEquiv e _).symm (colimit.isColimit G)
    exact closedUnderExistingCofan H hsum K (fun i ↦ hGP i) c hc
  have hclosure (K : DerivedCategory C) (hK : localizingClosureProEtale Λ X K) : H K :=
    hK H hlocal (fun L hL n ↦ ObjectProperty.le_weakSerreCoproductClosure _ _
      (hL.1.2 n))
  have hheart : ∃ d : ℕ, ∀ M : C, P M →
      (F.obj ((DerivedCategory.singleFunctor C 0).obj M)).IsLE (d : ℤ) := by
    have hold (h :
        (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
            (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
          Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
        (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
        (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)))) :
        ∃ d : ℕ, ∀ M : C, P M →
          (F.obj ((DerivedCategory.singleFunctor C 0).obj M)).IsLE (d : ℤ) := by
      obtain ⟨d, hd⟩ := exists_uniform_serreHeart_bound_of_isProper ℓ Λ h q f
      exact ⟨d, fun M hM ↦ (DerivedCategory.isLE_iff _ _).mpr (hd M hM)⟩
    rcases hΛ with h | h | h | h | h | h
    · exact hold (Or.inl h)
    · exact hold (Or.inr (Or.inl h))
    · exact hold (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact hold (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact hold (Or.inr (Or.inr (Or.inl h)))
    · obtain ⟨e⟩ := h
      let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
      let B := Profinite.continuousMapRingObj.{u} E
      let a := Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E ≫ e.inv.hom
      have hflat (Z : Scheme.{u}) :
          PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z)) := by
        have : IsIso (coefficientMap e.inv.hom Z) := by
          dsimp only [coefficientMap]
          infer_instance
        have : PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom Z)) :=
          preservesFiniteLimits_of_natIso
            (Mod.extendScalarsIsoComapInv (coefficientMap e.inv.hom Z)).symm
        have : PreservesFiniteLimits (Mod.extendScalars
            (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)) :=
          preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
            (ℓ := ℓ) (X := Z) E
        have : PreservesFiniteLimits (Mod.extendScalars
            (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z) ⋙
              Mod.extendScalars (coefficientMap e.inv.hom Z)) := inferInstance
        exact preservesFiniteLimits_of_natIso
          ((Mod.extendScalarsComp _ _).symm ≪≫
            Mod.extendScalarsIsoOfEq (coefficientMap_comp _ _ _).symm)
      let Q := ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible B X)
      let R : C ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj B X) := Mod.comap (coefficientMap a X)
      have hrestrict (M : C) (hM : P M) : Q (R.obj M) := by
        exact hM (Q.inverseImage R)
          (fun N hN ↦ constantModelConstructible_padicAlgCl_comap ℓ E Λ e X N hN)
          inferInstance inferInstance inferInstance inferInstance (fun _ ↦ inferInstance)
      obtain ⟨d, hd⟩ := exists_uniform_serreHeart_bound_of_isProper ℓ B
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨E, ⟨Iso.refl _⟩⟩)))) q f
      refine ⟨d, fun M hM ↦ (DerivedCategory.isLE_iff _ _).mpr (fun r hr ↦ ?_)⟩
      let RY : D ⥤ Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj B Y) := Mod.comap (coefficientMap a Y)
      apply RY.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      let es := (R.mapDerivedCategorySingleFunctor 0).app M
      let ep := (derivedComapLowerStarIso a f).app
        ((DerivedCategory.singleFunctor C 0).obj M)
      exact (hd (R.obj M) (hrestrict M hM) r hr).of_iso
        ((DerivedCategory.homologyFunctor _ r).mapIso
          (ep ≪≫ (moduleObjectDerivedPushforward B f).mapIso es))
  obtain ⟨d, hd⟩ := hheart
  refine ⟨d + 1, fun a K hK r hr ↦ ?_⟩
  let L := (DerivedCategory.TStructure.t.truncLE (a - 1)).obj K
  have hL : DerivedCategory.homologyProperty P L :=
    DerivedCategory.homologyProperty_truncLE (hclosure K hK) (a - 1)
  have hbound (n : ℕ) :
      (F.obj ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj L)).IsLE
        (a - 1 + (d : ℤ)) := by
    exact DerivedCategory.isLE_obj_of_isLE_of_homologyProperty F (d : ℤ) P hd _
      ⟨⟨-(n : ℤ), inferInstance⟩, ⟨a - 1, inferInstance⟩⟩
      (DerivedCategory.homologyProperty_truncGE hL _) (a - 1)
  obtain ⟨hroos, hprod⟩ := moduleObjectDerivedPushforward_postnikov_roos Λ f L
  obtain ⟨T, hT, δ, hdist⟩ := hroos
  have hzero (j : ℤ) (hj : a - 1 + (d : ℤ) < j) :
      IsZero ((DerivedCategory.homologyFunctor D j).obj T.pt) := by
    let : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor D j) :=
      hprod j
    have ht := isLimitOfPreserves (DerivedCategory.homologyFunctor D j) hT
    apply ht.isZero_pt
    apply Functor.isZero
    intro n
    exact DerivedCategory.isZero_of_isLE _ (a - 1 + (d : ℤ)) j hj
      (hX := hbound n.as)
  have hz₁ := hzero (r - 1) (by omega)
  have hz₂ := hzero r (by omega)
  exact (DerivedCategory.HomologySequence.exact₁ _ hdist (r - 1) r (by omega)).isZero_of_both_isZero
    hz₁ hz₂

end AlgebraicGeometry.ProEtale.CondensedRing
