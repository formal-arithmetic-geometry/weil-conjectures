/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
import Sheaf.Paper.StrictCompletionRestrictionComparison
import all Sheaf.Paper.CompletionTriangleComparison
import Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization

/-! # Completeness under open/closed support and site restriction
Source: Stacks Tags 09AA, 09AH, 09BM, 09BN; Bhatt--Scholze, Sections 3.4--3.5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
namespace SupportedCompletion
open StrictCompletionRestriction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem complete_iso {X : Scheme.{u}}
    {K L : DerivedCategory (AdicCompletion.Modules l E X)} (e : K ≅ L)
    (hK : IsDerivedComplete l E X K) : IsDerivedComplete l E X L := by
  obtain ⟨P, hP, ⟨i⟩, hc⟩ := hK
  exact ⟨P, hP, ⟨i ≪≫ e⟩, hc⟩

private theorem complete_zero {X : Scheme.{u}}
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (hK : IsZero K) :
    IsDerivedComplete l E X K := by
  obtain ⟨data, hd, a, F, c, κ, sF, hadd, ha, hc, hrep, hcomplete, hrest⟩ :=
    CompletionTriangle.completion_triangle_comparison l E X
  let := hadd
  apply (hcomplete K).mpr
  exact isIso_of_source_target_iso_zero _ hK.isoZero (F.map_isZero hK).isoZero

private theorem complete_iff {X : Scheme.{u}}
    (S : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E X))
    (hS : StrictCompletionRestriction.IsIntegral l E X S)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    IsDerivedComplete l E X K ↔ IsIso (S.unit.app K) := by
  obtain ⟨data, hd, ht, hs, hr, hu, hc⟩ := hS
  exact CompletionTriangle.complete_iff_from_comparison l E X S.completion S.unit hc K

private theorem restriction_complete_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E Y))
    (T : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E X))
    (hT : StrictCompletionRestriction.IsIntegral l E X T)
    (c : Comparison (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) S T)
    (K : DerivedCategory (AdicCompletion.Modules l E Y)) :
    IsDerivedComplete l E X
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapDerivedCategory.obj K) ↔
      IsIso ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapDerivedCategory.map
        (S.unit.app K)) := by
  rw [complete_iff l E T hT, ← c.unit]
  constructor
  · intro h
    have := h
    exact IsIso.of_isIso_comp_right _ (c.derived.hom.app K)
  · intro h
    have := h
    infer_instance

private theorem complete_support {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hi : IsDerivedComplete l E Z
      ((CondensedRing.supportPullback (DerivedNakayama.integerRing l E)
        i).mapDerivedCategory.obj K))
    (hj : IsDerivedComplete l E U
      ((CondensedRing.supportPullback (DerivedNakayama.integerRing l E)
        j).mapDerivedCategory.obj K)) :
    IsDerivedComplete l E X K := by
  obtain ⟨S, hS, hmodels, hsections, hrestrict⟩ :=
    strict_completion_restriction_comparison l E
  apply (complete_iff l E (S X) (hS X) K).mpr
  have hmap {V : Scheme.{u}} (f : V ⟶ X) [IsImmersion f]
      (h : IsDerivedComplete l E V
        ((CondensedRing.supportPullback (DerivedNakayama.integerRing l E) f).mapDerivedCategory.obj
          K)) :
      IsIso ((CondensedRing.supportPullback (DerivedNakayama.integerRing l E)
        f).mapDerivedCategory.map ((S X).unit.app K)) := by
    let e := Functor.mapDerivedCategoryNatIso
      (CondensedRing.supportPullbackIsoUpperStar (DerivedNakayama.integerRing l E) f)
    have h' := complete_iso l E (e.app K) h
    obtain ⟨_, ⟨c⟩⟩ := hrestrict f
      (MorphismProperty.le_multiplicativeClosure _ _ (Or.inl inferInstance))
    have h'' := (restriction_complete_iff l E f (S X) (S V) (hS V) c K).mp h'
    exact (NatIso.isIso_map_iff e ((S X).unit.app K)).mpr h''
  exact (CondensedRing.condensedSupportDerivedLocalization
    (DerivedNakayama.integerRing l E) i j hij).2.2.2.2.2 _ (hmap i hi) (hmap j hj)

private theorem complete_extensions {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    letI := CondensedRing.closedSupport_lowerStarExact (DerivedNakayama.integerRing l E) i j hij
    (∀ K : DerivedCategory (AdicCompletion.Modules l E U), IsDerivedComplete l E U K →
      IsDerivedComplete l E X
        ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E)
          j).mapDerivedCategory.obj K)) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E Z), IsDerivedComplete l E Z K →
      IsDerivedComplete l E X
        ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E)
          i).mapDerivedCategory.obj K)) := by
  let := CondensedRing.closedSupport_lowerStarExact (DerivedNakayama.integerRing l E) i j hij
  obtain ⟨hu, hc, hs, hzeroOpen, hzeroClosed, hjoint⟩ :=
    CondensedRing.condensedSupportDerivedLocalization (DerivedNakayama.integerRing l E) i j hij
  constructor
  · intro K hK
    apply complete_support l E i j hij
    · exact complete_zero l E _ (hzeroOpen K)
    · have := hu K
      exact complete_iso l E
        (asIso ((CondensedRing.openSupportDerivedAdjunction
          (DerivedNakayama.integerRing l E) j).unit.app K)) hK
  · intro K hK
    apply complete_support l E i j hij
    · have := hc K
      exact complete_iso l E
        (asIso ((CondensedRing.closedPullbackDerivedAdjunction
          (DerivedNakayama.integerRing l E) i).counit.app K)).symm hK
    · exact complete_zero l E _ (hzeroClosed K)

private theorem complete_path {X S : Scheme.{u}}
    {tree : QcqsOpenClosedTree X} (p : tree.Path S)
    (N : AdicCompletion.Modules l E S)
    (hN : IsDerivedComplete l E S ((DerivedCategory.singleFunctor _ 0).obj N)) :
    IsDerivedComplete l E X ((DerivedCategory.singleFunctor _ 0).obj
      ((p.extension (DerivedNakayama.integerRing l E)).obj N)) := by
  induction p with
  | root tree => exact hN
  | openBranch j i h a b p ih =>
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by rw [h, compl_compl]
    have hc := (complete_extensions l E i j hij).1 _ (ih N hN)
    exact complete_iso l E
      (((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E)
        j).mapDerivedCategorySingleFunctor 0).app _) hc
  | closedBranch j i h a b p ih =>
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by rw [h, compl_compl]
    let := CondensedRing.closedSupport_lowerStarExact (DerivedNakayama.integerRing l E) i j hij
    have hc := (complete_extensions l E i j hij).2 _ (ih N hN)
    exact complete_iso l E
      (((CondensedRing.lowerStar (DerivedNakayama.integerRing l E)
        i).mapDerivedCategorySingleFunctor 0).app _) hc

end SupportedCompletion

/-- A complete integral module remains complete after a finite open/closed support path
and a pro-etale site restriction.

Source: Stacks Tags 09AA, 09AH, 09BM, 09BN; Bhatt--Scholze, Sections 3.4--3.5.
(blueprint: lem-sfb-supported-extension-derived-complete)

Proof: Complementary inverse images identify an open extension with (N,0), and a closed
extension with (0,N). The strict completion comparison identifies their completion units
with the restrictions of the ambient unit. Both restricted units are invertible, including
on zero objects. Joint detection of isomorphisms therefore gives completeness of either
extension. Induct on the finite path. Finally weakly etale restriction commutes with the
specified completion and its unit. Exactness identifies termwise images of degree-zero
complexes with the ordinary module operations in degree zero. -/
theorem supported_extension_derived_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} {tree : QcqsOpenClosedTree X} (p : tree.Path S)
    (N : AdicCompletion.Modules l E S)
    (hN : IsDerivedComplete l E S ((DerivedCategory.singleFunctor _ 0).obj N))
    (U : X.ProEt) :
    IsDerivedComplete l E U.left ((DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) U.hom).obj
        ((p.extension (DerivedNakayama.integerRing l E)).obj N))) := by
  obtain ⟨S, hS, hmodels, hsections, hrestrict⟩ :=
    StrictCompletionRestriction.strict_completion_restriction_comparison l E
  let K := (DerivedCategory.singleFunctor _ 0).obj
    ((p.extension (DerivedNakayama.integerRing l E)).obj N)
  have hc := SupportedCompletion.complete_path l E p N hN
  have := (SupportedCompletion.complete_iff l E (S X) (hS X) _).mp hc
  obtain ⟨_, ⟨c⟩⟩ := hrestrict U.hom
    (MorphismProperty.le_multiplicativeClosure _ _ (Or.inr inferInstance))
  have hi : IsIso ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
      U.hom).mapDerivedCategory.map ((S X).unit.app K)) := by infer_instance
  have hc' := (SupportedCompletion.restriction_complete_iff l E U.hom (S X) (S U.left)
    (hS U.left) c K).mpr hi
  exact SupportedCompletion.complete_iso l E
    (((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
      U.hom).mapDerivedCategorySingleFunctor 0).app _) hc'
end AlgebraicGeometry.ProEtale
