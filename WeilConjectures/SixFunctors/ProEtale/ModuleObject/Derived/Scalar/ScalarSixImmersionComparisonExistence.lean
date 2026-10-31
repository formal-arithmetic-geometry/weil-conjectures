/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixOpenScalarRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionScalarEssentialImage

/-! # Normalized scalar comparisons for individual immersions

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md, (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem supportedMap_injective
    {A B : Type*} [Category A] [Category B] (H : A ⥤ B) [H.Full]
    (R : B ⥤ A) (rho : H ⋙ R ≅ 𝟭 A) {M N : A} {Z : B}
    (e : H.obj M ≅ Z) {f g : Z ⟶ H.obj N} (h : R.map f = R.map g) : f = g := by
  apply (cancel_epi e.hom).mp
  let f' := H.preimage (e.hom ≫ f)
  let g' := H.preimage (e.hom ≫ g)
  have hh : R.map (H.map f') = R.map (H.map g') := by
    simp only [f', g', H.map_preimage, Functor.map_comp, h]
  have hn := rho.hom.naturality f'
  have hm := rho.hom.naturality g'
  simp only [Functor.comp_map, Functor.id_map] at hn hm
  have hfg : f' = g' := by
    apply (cancel_epi (rho.hom.app M)).mp
    exact hn.symm.trans ((congrArg (fun z ↦ z ≫ rho.hom.app N) hh).trans hm)
  simpa only [f', g', H.map_preimage] using congrArg H.map hfg

private theorem normalizedObject_exists
    {A B : Type*} [Category A] [Category B] (H : A ⥤ B) (R : B ⥤ A)
    (rho : H ⋙ R ≅ 𝟭 A) {Z : B} {M : A} (t : R.obj Z ≅ M)
    (h : H.essImage Z) :
    ∃ e : Z ≅ H.obj M, R.map e.hom ≫ rho.hom.app M = t.hom := by
  obtain ⟨N, ⟨e⟩⟩ := h
  let g : N ≅ M := (rho.app N).symm ≪≫ R.mapIso e ≪≫ t
  refine ⟨e.symm ≪≫ H.mapIso g, ?_⟩
  change R.map (e.inv ≫ H.map g.hom) ≫ rho.hom.app M = t.hom
  rw [R.map_comp, Category.assoc]
  have hn : R.map (H.map g.hom) ≫ rho.hom.app M = rho.hom.app N ≫ g.hom :=
    rho.hom.naturality g.hom
  rw [hn]
  simp [g]

private theorem normalizedComparison_exists
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ C) (S : A ⥤ B) (H : B ⥤ C) [H.Full]
    (R : C ⥤ B) (rho : H ⋙ R ≅ 𝟭 B) (t : F ⋙ R ≅ S)
    (hs : ∀ M, H.essImage (F.obj M)) :
    ∃ e : F ≅ S ⋙ H,
      ∀ M, R.map (e.hom.app M) ≫ rho.hom.app (S.obj M) = t.hom.app M := by
  classical
  have h (M : A) := normalizedObject_exists H R rho (t.app M) (hs M)
  let e (M : A) := (h M).choose
  have he (M : A) : R.map (e M).hom ≫ rho.hom.app (S.obj M) = t.hom.app M :=
    (h M).choose_spec
  refine ⟨NatIso.ofComponents e ?_, he⟩
  intro M N f
  apply supportedMap_injective H R rho (e M).symm
  apply (cancel_mono (rho.hom.app (S.obj N))).mp
  simp only [Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map]
  have nr := rho.hom.naturality (S.map f)
  simp only [Functor.comp_map, Functor.id_map] at nr
  rw [he, nr]
  rw [← Category.assoc, he]
  exact t.hom.naturality f

private theorem extension_full (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] : (scalarSixExtension E G Λ f).Full := by
  have hD := D.full (scalarSixImmersion G Λ f)
  have hF := (scalarSixEquivalence Λ S.left).fullyFaithfulFunctor.full
  have hB := (scalarSixEquivalence Λ X.left).symm.fullyFaithfulFunctor.full
  unfold scalarSixExtension
  exact @Functor.Full.comp _ _ _ _ _ _ _ _ hF
    (@Functor.Full.comp _ _ _ _ _ _ _ _ hD hB)

private def restrictionScalarIso
    (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {k : Type u} [Field k] {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] :
    (scalarSixExtension E G Λ f ⋙ scalarSixChange a X.left) ⋙
      scalarSixPull Λ' f.left ≅ scalarSixChange a S.left :=
  Functor.isoWhiskerLeft (scalarSixExtension E G Λ f) (C.theta a f.left).symm ≪≫
    Functor.isoWhiskerRight (scalarSixRestriction E D G Λ f) (scalarSixChange a S.left) ≪≫
    Functor.leftUnitor _

set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
-- Preserve the original coherence binder and check the concrete coefficient functors.
/-- A normalized comparison for each immersion, retaining the specified open value.
Geometric composition is not part of this assertion.

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md, (2), open and closed
construction; Stacks Tags 03DI, 03DJ, 09AA, 09BM and 09AH.
(blueprint: lem-sfb-scalar-six-individual-immersion-comparisons).

Proof: a full extension H with an invertible restriction H R has the following
normalization property. If Z lies in its essential image and R Z is identified with M,
there is a unique isomorphism Z to H M inducing that identification. Construct it from
an essential-image witness and correct its restriction with the given H R isomorphism.
Fullness and naturality of H R show that restriction detects supported maps; this proves
naturality of the normalized components.

For a closed immersion scalar extension preserves closed support: its complementary
open restriction is zero by the pullback/scalar comparison and preservation of zero by
the scalar left adjoint. The exact unbounded localization unit therefore exhibits the
scalar extension in the essential image of the new closed extension. For an arbitrary
immersion, use its canonical image factorization into an open immersion followed by a
closed immersion. The published open scalar isomorphism and the closed comparison,
conjugated by the fixed extension compositor, establish essential-image membership.
Apply the general normalization property with inverse C.theta followed by the scalar
image of the old restriction, obtaining beta with exactly the required normalization.
Finally the mate unit equation and localization show that the specified open comparison
has the same restriction. Detection of supported maps proves its equality with beta.
No binary restriction-composition or scalar-tower equation is needed. -/
theorem scalarSixIndividualImmersionComparisons_exists
    (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k) :
    ∃ beta : ScalarSixImmersionComparisons E G k,
      ScalarSixImmersionNormalization E D G C k O beta ∧
        ScalarSixImmersionOpenValue E D G C k O beta := by
  classical
  have h {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
      {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : S ⟶ X) [IsImmersion f.left] := by
    have := extension_full E D G Λ' f
    exact normalizedComparison_exists
      (scalarSixExtension E G Λ f ⋙ scalarSixChange a X.left)
      (scalarSixChange a S.left) (scalarSixExtension E G Λ' f)
      (scalarSixPull Λ' f.left) (scalarSixRestriction E D G Λ' f)
      (restrictionScalarIso E D G C a f) (scalarSixImmersionScalar_mem_essImage E D G C O a f)
  let beta : ScalarSixImmersionComparisons E G k :=
    fun {Λ Λ'} a {S X} _ _ _ _ _ _ f _ ↦ (h a f).choose
  have hn : ScalarSixImmersionNormalization E D G C k O beta := by
    intro Λ Λ' a S X _ _ _ _ _ _ f _ M
    have hm := (h a f).choose_spec M
    simp only [restrictionScalarIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hm
    erw [Category.comp_id] at hm
    exact hm
  refine ⟨beta, hn, ?_⟩
  intro Λ Λ' a S X _ _ _ _ _ _ j _ M
  have := extension_full E D G Λ' j
  apply (cancel_mono ((scalarSixOpenIso E G O Λ' j).inv.app
    ((scalarSixChange a S.left).obj M))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  apply supportedMap_injective (scalarSixExtension E G Λ' j)
    (scalarSixPull Λ' j.left) (scalarSixRestriction E D G Λ' j)
    ((beta a j).app M).symm
  apply (cancel_mono ((scalarSixRestriction E D G Λ' j).hom.app
    ((scalarSixChange a S.left).obj M))).mp
  exact (scalarSixOpenScalar_restriction E D G C O a j M).trans (hn a j M).symm

end AlgebraicGeometry.ProEtale.CondensedRing
