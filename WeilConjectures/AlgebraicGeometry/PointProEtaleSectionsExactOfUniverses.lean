/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExact
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement


import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import WeilConjectures.AlgebraicGeometry.WContractibleAffineEvaluation
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Exact point sections with independent coefficient universes

Source: Stacks 03CW, 0946; the affine weakly contractible point argument
(blueprint: lem-weil-point-proetale-sections-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 3000] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
universe t u w w'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

/-- Final-object module evaluation in a universe containing site and coefficients.
Source: Stacks 03CW (blueprint: lem-weil-point-proetale-sections-exact). -/
abbrev pointModuleSectionsOfUniverses (k : Type t) [Field k]
    (A : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)}) :
    ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A) ⥤
      ModuleCat.{max u (t + 1)}
        (((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A).obj.obj
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) :=
  SheafOfModules.forget.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A) ⋙
    PresheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

/-- Exact final-object sections, including preservation of quasi-isomorphisms and the
unbounded derived comparison, with no equality between field and coefficient universes.
Source: Stacks 03CW, 0946 (blueprint: lem-weil-point-proetale-sections-exact).
Proof: Spec k is affine and weakly contractible: every weakly etale faithfully flat
k-algebra has a retraction, since k is algebraically closed. A locally surjective map
of sheaves is therefore surjective at the final object. The same lifting argument
works in any universe containing the site and coefficients. Kernels are sectionwise;
cokernels are locally computed, so evaluation on module sheaves is exact. Applying
this to cycles and boundaries proves preservation of quasi-isomorphisms. Localization
of the termwise additive functor gives the canonical comparison, commutes with shifts
and cone triangles, and commutes with homology. This is the proof of
point_proEtale_sections_exact with the coefficient universe kept independent. -/
theorem point_proEtale_sections_exact_of_universes (k : Type t) [Field k] [IsAlgClosed k] :
    (∀ (F G : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
        AddCommGrpCat.{max u (t + 1)}) (f : F ⟶ G), Epi f →
      Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))) ∧
    (∀ A : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)},
      PreservesFiniteLimits (pointModuleSectionsOfUniverses.{t, u} k A) ∧
      PreservesFiniteColimits (pointModuleSectionsOfUniverses.{t, u} k A) ∧
      (∀ (K L : CochainComplex (ringedSiteModules.{max u (t + 1)}
          ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A)) ℤ) (f : K ⟶ L),
        QuasiIso f → QuasiIso
          (((pointModuleSectionsOfUniverses.{t, u} k A).mapHomologicalComplex (.up ℤ)).map f)) ∧
      (∀ [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)}
          ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A))]
        [HasDerivedCategory.{w'} (ModuleCat.{max u (t + 1)}
          (((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A).obj.obj
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))))]
        [PreservesFiniteLimits (pointModuleSectionsOfUniverses.{t, u} k A)]
        [PreservesFiniteColimits (pointModuleSectionsOfUniverses.{t, u} k A)],
        Nonempty (Functor.CommShift
          (pointModuleSectionsOfUniverses.{t, u} k A).mapDerivedCategory ℤ) ∧
        Functor.IsTriangulated (pointModuleSectionsOfUniverses.{t, u} k A).mapDerivedCategory ∧
        Nonempty (DerivedCategory.Q ⋙
          (pointModuleSectionsOfUniverses.{t, u} k A).mapDerivedCategory ≅
          (pointModuleSectionsOfUniverses.{t, u} k A).mapHomologicalComplex (.up ℤ) ⋙
            DerivedCategory.Q) ∧
        ∀ i : ℤ, Nonempty
          ((pointModuleSectionsOfUniverses.{t, u} k A).mapDerivedCategory ⋙
              DerivedCategory.homologyFunctor _ i ≅
            DerivedCategory.homologyFunctor _ i ⋙ pointModuleSectionsOfUniverses.{t, u} k A))) := by
  classical
  have : WLocalSpace (PrimeSpectrum k) :=
    { eq_of_specializes := fun _ _ _ _ ↦ Subsingleton.elim _ _
      isClosed_closedPoints := by
        have : closedPoints (PrimeSpectrum k) = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact mem_closedPoints_iff.mpr isClosed_singleton
        rw [this]
        exact isClosed_univ }
  have : IsWLocalRing k := ⟨inferInstance⟩
  have : IsAlgClosed (IsLocalRing.ResidueField k) :=
    IsAlgClosed.of_ringEquiv k _
      (RingEquiv.ofBijective (IsLocalRing.residue k)
        ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩)
  have : IsStrictlyHenselianLocalRing k := ⟨inferInstance⟩
  have hstrict (m : Ideal k) [m.IsMaximal] :
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
    apply IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.atUnits k m.primeCompl (S := Localization.AtPrime m) ?_).toRingEquiv
    intro x hx
    exact isUnit_iff_ne_zero.mpr (fun he ↦ hx (he ▸ m.zero_mem))
  have hretract (B : Type t) [CommRing B] (φ : k →+* B)
      (hf : φ.FaithfullyFlat) (hw : φ.WeaklyEtale) :
      ∃ r : B →+* k, r.comp φ = RingHom.id k :=
    RingHom.exists_retraction_of_wlocal_geometric_criterion hstrict φ hf hw
  have hW (F G : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (max u (t + 1))))
      (f : F ⟶ G) (hf : Epi f) :
      Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
    exact Scheme.ProEt.surjective_app_of_affine_ring_retractions.{t, u}
      (Spec (.of k)) k (𝟙 _) hretract F G f
  constructor
  · intro F G f hf
    have : Epi f := hf
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)} f).mpr hf
    let g := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).map f
    exact hW _ _ g inferInstance
  · intro A
    let R := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A
    let ev := pointModuleSectionsOfUniverses.{t, u} k A
    have : ev.PreservesEpimorphisms := by
      constructor
      intro M N f hf
      let g := (SheafOfModules.toSheaf R).map f
      have : Epi g := inferInstance
      have : Sheaf.IsLocallySurjective g :=
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)} g).mpr
          inferInstance
      let g' := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).map g
      have : Epi g' := inferInstance
      exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr (hW _ _ g' inferInstance)
    have : ev.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels ev
    have hlim : PreservesFiniteLimits ev :=
      Functor.preservesFiniteLimits_of_preservesHomology ev
    have hcol : PreservesFiniteColimits ev :=
      Functor.preservesFiniteColimits_of_preservesHomology ev
    refine ⟨hlim, hcol, ?_, ?_⟩
    · intro K L f hf
      have : QuasiIso f := hf
      infer_instance
    · intro _ _ _ _
      refine ⟨⟨inferInstance⟩, inferInstance,
        ⟨(pointModuleSectionsOfUniverses.{t, u} k A).mapDerivedCategoryFactors⟩, ?_⟩
      intro i
      exact ⟨((pointModuleSectionsOfUniverses.{t, u} k A).mapDerivedCategoryHomologyFunctorIso
        i).symm⟩

end AlgebraicGeometry.ProEtale
