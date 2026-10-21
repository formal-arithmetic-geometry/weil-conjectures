/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.Paper.ContinuousIntegralLocalization
public import Sheaf.CategoryTheory.HomColimitExtension
import all Sheaf.CategoryTheory.HomColimitExtension
import Sheaf.CategoryTheory.DerivedCategory.BoundedCohomologyConeWitness
import Sheaf.Paper.IntegralConstructibleSheafHom
import Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport
import Sheaf.Paper.ContinuousIntegralLocalizationModel

/-! # Shifted Hom continuity for the integral localization unit telescope

Source: Bhatt--Scholze, Lemma 6.8.12 and the full-faithfulness argument in
Proposition 6.8.14(2); Hemo--Richarz--Scholbach, Lemma 5.3.
(blueprint: lem-sfb-integral-localization-hom-colimit)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Shifted additive Hom from an integral bounded constructible object preserves the
canonical scalar-localization unit telescope, indexed by ℕ or by ULift ℕ.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), full faithfulness.
(blueprint: lem-sfb-integral-localization-hom-colimit)

Proof:
1. For any complex C strictly zero below a, every stage of its scalar sequence is C.
   Good truncation at a is naturally isomorphic to this diagram. Precomposing the
   canonical truncated colimit by this isomorphism proves that the indicated
   good-truncated telescope cocone is colimiting.
2. Reindex along AsSmall ℕ ≌ ℕ. The common lower bound and colimit property persist.
   Apply integralConstructible_sheaf_hom_colimit
   (lem-weil-pbc-integral-constructible-sheaf-hom) to every constructible module M:
   M in degree zero satisfies homColimitProperty for this derived cocone.
3. For this fixed cocone, homColimitProperty is invariant under isomorphisms and
   shifts. Precomposition gives the isomorphism comparison; the
   shift identity Hom(T[m],D[q]) = Hom(T,D[q-m]) gives shift invariance.
4. Apply bounded_cohomology_cone_witness (lem-sfb-bounded-cohomology-cone-witness)
   to K. Its cohomology sheaves are constructible by integralConstructible. Induct
   on the finite witness. Shifted cohomology leaves satisfy the property by 2--3.
   Rotate each witness triangle F_i → F_j → F_r[n] to put the two known objects
   at its ends (def-weil-triangulated-category), then apply
   homColimitProperty_extensions (lem-weil-pbc-hom-colimit-extension). Shift back
   to F_r. This also covers zero and acyclic K.
5. B is bounded below. Use exists_integralLocalization_complex_model
   (lem-weil-pbc-integral-localization-complex-model), then apply
   localizationCocone_isColimit_of_model
   (lem-weil-pbc-integral-localization-colimit-transport) to each shifted additive
   Hom functor from K. Steps 1--4 supply its continuity premise for every strictly
   bounded-below complex telescope. Thus the lifted canonical Hom cocone is colimiting.
6. The model identifies every leg with the specified unit followed by the restricted
   inverse scalar power (def-weil-pbc-integral-localization-telescope). Hence the
   colimit comparison is precisely the canonical map in the statement. The order
   equivalence ULift ℕ ≌ ℕ transports this conclusion to the ordinary index as well.
   No colimit in the derived category is assumed. -/
theorem integralLocalization_hom_colimit (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (K B : integralConstructible ℓ E X) :
    (∀ q : ℤ, IsIso (colimit.desc _
      ((shiftFunctor _ q ⋙ preadditiveCoyoneda.obj (op K.obj)).mapCocone
        (integralLocalizationCocone ℓ E X B.obj)))) ∧
    homColimitProperty (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ B.obj)
      (integralLocalizationLiftedCocone.{u, u + 1} ℓ E X B.obj) K.obj := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) X)
  have iso_transfer {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
      (D : I ⥤ DerivedCategory A) (c : Cocone D)
      {S T : DerivedCategory A} (e : S ≅ T)
      (hT : homColimitProperty D c T) : homColimitProperty D c S := by
    intro n
    let eF := Functor.isoWhiskerLeft (shiftFunctor _ n)
      (preadditiveCoyoneda.mapIso e.symm.op)
    apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
    obtain ⟨hc⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (hT n)
    exact ⟨IsColimit.mapCoconeEquiv eF.symm hc⟩
  have : HasColimitsOfShape (ULift.{u + 1} ℕ) A := inferInstance
  have : HasColimitsOfShape (ULift.{u + 1} ℕ) (CochainComplex A ℤ) := inferInstance
  have hasTruncatedColimit (C : CochainComplex A ℤ) (a : ℤ) :
      HasColimit (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C ⋙
        (ComplexShape.embeddingUpIntGE a).truncGEFunctor A) :=
    HasColimitsOfShape.has_colimit _
  have continuity (C : CochainComplex A ℤ) (a : ℤ) (hC : C.IsStrictlyGE a) :
      homColimitProperty
        (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.mapCocone (condensedContinuityCocone
          (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C) a)) K.obj := by
    let D := integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C
    let c := condensedContinuityCocone D a
    let π := Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
    have : ∀ i, IsIso (π.app i) := fun i ↦
      (HomologicalComplex.isIso_πTruncGE_iff C _).2 hC
    have : IsIso π := NatIso.isIso_of_isIso_app π
    have hc : IsColimit c :=
      (IsColimit.precomposeHomEquiv (asIso π) _).symm (colimit.isColimit _)
    let e : AsSmall.{u + 1} ℕ ≌ ULift.{u + 1} ℕ :=
      AsSmall.equiv.symm.trans (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
    have sheaf (M : A) (hM : IsConstructibleModuleObject
        (condensedRingObj (integralCoeff ℓ E) X) M) :
        homColimitProperty (D ⋙ DerivedCategory.Q) (DerivedCategory.Q.mapCocone c)
          ((DerivedCategory.singleFunctor A 0).obj M) := by
      have hD : ∃ b : ℤ, ∀ n,
          (DerivedCategory.Q.obj ((e.functor ⋙ D).obj n)).IsGE b := by
        refine ⟨a, fun n ↦ ?_⟩
        change (DerivedCategory.Q.obj C).IsGE a
        have : C.IsStrictlyGE a := hC
        infer_instance
      have h := integralConstructible_sheaf_hom_colimit ℓ E X M hM
        (e.functor ⋙ D) (c.whisker e.functor) ⟨hc.whiskerEquivalence e⟩ hD
      intro n
      obtain ⟨hn⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (h n)
      apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
      exact ⟨IsColimit.ofWhiskerEquivalence e hn⟩
    let P := homColimitProperty (D ⋙ DerivedCategory.Q) (DerivedCategory.Q.mapCocone c)
    obtain ⟨N, F, hF, hw⟩ := DerivedCategory.bounded_cohomology_cone_witness A K.obj
      K.property.1
    have hP : ∀ r : Fin (N + 1), P (F r) := by
      intro r
      induction r using WellFoundedLT.induction with
      | ind r ih =>
        rcases hw r with ⟨q, n, ⟨eF⟩⟩ | ⟨i, j, hi, hj, n, f, g, h, ht⟩
        · exact iso_transfer _ _ eF
            (homColimitProperty_shift _ _ _ (sheaf _ (K.property.2 q)) n)
        · let T := Pretriangulated.Triangle.mk f g h
          have hmid : P ((F r) ⟦n⟧) := homColimitProperty_extensions _ _ T.rotate
            (Pretriangulated.rot_of_distTriang T ht) (ih j hj)
            (homColimitProperty_shift _ _ _ (ih i hi) 1)
          have hback := homColimitProperty_shift _ _ _ hmid (-n)
          let ei : ((F r) ⟦n⟧) ⟦-n⟧ ≅ F r :=
            (shiftFunctorAdd' _ n (-n) 0 (by omega)).symm.app _ ≪≫
              (shiftFunctorZero _ ℤ).app _
          exact iso_transfer _ _ ei.symm hback
    rw [← hF]
    exact hP (Fin.last N)
  obtain ⟨m⟩ := exists_integralLocalization_complex_model ℓ E X B.obj B.property.1.1
  have hlift : homColimitProperty
      (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ B.obj)
      (integralLocalizationLiftedCocone.{u, u + 1} ℓ E X B.obj) K.obj := by
    intro q
    apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
    apply localizationCocone_isColimit_of_model ℓ B.obj
      (integralLocalizationCocone ℓ E X B.obj) m
      (shiftFunctor _ q ⋙ preadditiveCoyoneda.obj (op K.obj))
    intro C a hC
    exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (continuity C a hC q)
  refine ⟨?_, hlift⟩
  intro q
  obtain ⟨hq⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (hlift q)
  apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
  exact ⟨IsColimit.ofWhiskerEquivalence
    (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence hq⟩

end AlgebraicGeometry.ProEtale.CondensedRing
