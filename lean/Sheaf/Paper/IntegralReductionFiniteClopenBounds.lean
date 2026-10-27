/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.ClopenIntegralRestriction
import Sheaf.Paper.IntegralReductionClopenComparison
import Sheaf.Paper.FiniteClopenConstructibilityBounds
import all Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-! # Finite-level bounds for restricted integral reductions

Source: Bhatt--Scholze, Definition 3.5.2 and Proposition 3.5.1(1), p. 24
(blueprint: lem-pur-integral-reduction-finite-clopen-bounds).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

private theorem supportIso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) :
    proEtaleCohomologicalSupport K = proEtaleCohomologicalSupport L := by
  ext m
  exact not_congr ((DerivedCategory.homologyFunctor _ m).mapIso e).isZero_iff

private theorem torIso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ) :
    HasProEtaleTorAmplitude Y A K a b ↔ HasProEtaleTorAmplitude Y A L a b := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro T Q ht f hf hQ M m hm
    exact h.2 T Q ⟨ht.some ≪≫ e.symm⟩ f hf hQ M m hm
  · intro h
    refine ⟨h.1, ?_⟩
    intro T Q ht f hf hQ M m hm
    exact h.2 T Q ⟨ht.some ≪≫ e⟩ f hf hQ M m hm

/-- At a single positive quotient exponent, ordinary completed restriction detects
constructibility and any prescribed ordered support or Tor interval of the reduction.
No completeness or bound uniform in the exponent is asserted here.

Source: Bhatt--Scholze, Definition 3.5.2, p. 24; finite-clopen application of
`lem-pur-clopen-finite-constructibility-bounds`, step 5 of
`lem-pur-clopen-augmented-integral-descent`
(blueprint: lem-pur-integral-reduction-finite-clopen-bounds).

Proof: apply finite_clopen_constructibility_bounds to the same purity setting with
level n+1. Restriction to an open is the inverse image for the localized site.
The canonical constant-section coefficient map identifies this ordinary restriction
with proEtaleConstantRingPullback. Exactness descends the identification to derived
categories. The scalar-extension restriction comparison identifies the restriction
of the n-th reduction with the reduction of the ordinary completed restriction.
Transport the finite-level constructibility, support and Tor assertions along this
isomorphism. Constructibility is invariant under the homology isomorphisms; support
uses the same zero homology tests; Tor uses the same isomorphism class of every
resolution test. Empty components contribute only zero objects, and for an empty
partition the finite-level local-global assertions have vacuous right-hand sides. -/
theorem integralReductionFiniteClopenBounds
    (P : PurityFiniteSetting.{u})
    (X : Over (Spec (CommRingCat.of P.field.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {I : Type w} [Finite I]
    (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hdisjoint : ∀ i i', i ≠ i' →
      Disjoint (Set.range (j i).left) (Set.range (j i').left))
    (hcover : (⋃ i, Set.range (j i).left) = Set.univ)
    (K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))
    (n : ℕ) :
    (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.left
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ↔
      ∀ i, intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K))) ∧
    (∀ a b : ℤ, a ≤ b →
      (proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
            Set.Icc a b ↔
        ∀ i, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ⊆
              Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      (HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) a b ↔
        ∀ i, HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K))
          a b)) := by
  classical
  let Pn : PurityFiniteSetting.{u} := { P with
    level := n + 1
    level_pos := Nat.succ_pos n }
  let : X.left.Over (Spec (CommRingCat.of Pn.field.k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := by
    change QuasiCompact X.hom
    infer_instance
  let L := (scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K
  have H := finite_clopen_constructibility_bounds Pn X.left (fun i ↦ (Xi i).left)
    (fun i ↦ (j i).left) hdisjoint hcover
  let e (i : I) := (integralReductionClopenComparison P.coefficients.l P.extension
    (j i).left n).some.app K
  have hsupport (i : I) := supportIso (e i)
  have hbound : ∀ a b : ℤ, a ≤ b →
      (proEtaleCohomologicalSupport L ⊆ Set.Icc a b ↔
        ∀ i, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ⊆
              Set.Icc a b) := by
    intro a b hab
    exact (H.2.2.2.2.1 L a b hab).trans (forall_congr' (fun i ↦
      iff_of_eq (congrArg (fun S : Set ℤ ↦ S ⊆ Set.Icc a b) (hsupport i))))
  refine ⟨?_, hbound, ?_⟩
  · have hcoh :
        (∀ m : ℤ, IsConstructibleProEtaleModuleSheaf X.left Pn.Ring
          ((DerivedCategory.homologyFunctor _ m).obj L)) ↔
        ∀ (i : I) (m : ℤ), IsConstructibleProEtaleModuleSheaf (Xi i).left Pn.Ring
          ((DerivedCategory.homologyFunctor _ m).obj
            ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).obj K))) := by
      refine (H.2.2.2.1 L).trans ⟨?_, ?_⟩
      · intro h i m
        exact constructibleProEtale_of_iso _ _
          ((DerivedCategory.homologyFunctor _ m).mapIso (e i)) (h i m)
      · intro h i m
        exact constructibleProEtale_of_iso _ _
          ((DerivedCategory.homologyFunctor _ m).mapIso (e i)).symm (h i m)
    change (_ ∧ _) ↔ ∀ i, _ ∧ _
    constructor
    · rintro ⟨hb, hc⟩
      obtain ⟨a, ha⟩ := hb.bddBelow
      obtain ⟨b, hb⟩ := hb.bddAbove
      have hs : proEtaleCohomologicalSupport L ⊆ Set.Icc (min a b) (max a b) :=
        fun q hq ↦ ⟨(min_le_left a b).trans (ha hq), (hb hq).trans (le_max_right a b)⟩
      intro i
      exact ⟨(Set.finite_Icc _ _).subset ((hbound _ _
        ((min_le_left a b).trans (le_max_left a b))).mp hs i), hcoh.mp hc i⟩
    · intro h
      have hs := Set.finite_iUnion (fun i ↦ (h i).1)
      obtain ⟨a, ha⟩ := hs.bddBelow
      obtain ⟨b, hb⟩ := hs.bddAbove
      refine ⟨(Set.finite_Icc (min a b) (max a b)).subset
        ((hbound _ _ ((min_le_left a b).trans (le_max_left a b))).mpr ?_),
        hcoh.mpr (fun i ↦ (h i).2)⟩
      intro i q hq
      exact ⟨(min_le_left a b).trans (ha (Set.mem_iUnion.mpr ⟨i, hq⟩)),
        (hb (Set.mem_iUnion.mpr ⟨i, hq⟩)).trans (le_max_right a b)⟩
  · intro a b hab
    exact (H.2.2.2.2.2.1 L a b hab).trans (forall_congr' (fun i ↦ torIso (e i) a b))

end WeilConjectures.PurityFiniteSetting
