/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.SiteInverseImageModuleFlat.SiteInverseImageModuleFlat
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentTensorNormalization

/-! # Flatness of component module pullback

Source: Hemo--Richarz--Scholbach, Construction (4.1) and Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v₁ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem preservesFlat_transport
    {C D : Type*} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C]
    [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D] [HasCoequalizers D]
    {F G : C ⥤ D} [bF : F.Braided] [bG : G.Braided]
    (e : F ≅ G) [NatTrans.IsMonoidal e.hom]
    (R : C) [MonObj R] [IsCommMonObj R]
    (S : D) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ F.obj R) [IsMonHom ρ] [IsIso ρ]
    (h : ∀ (σ : S ⟶ G.obj R) [IsMonHom σ] [IsIso σ],
      (G.mapMod R ⋙ Mod.comap σ).PreservesFlat) :
    (F.mapMod R ⋙ Mod.comap ρ).PreservesFlat := by
  let i : F.mapMod R ⋙ Mod.comap ρ ≅
      G.mapMod R ⋙ Mod.comap (ρ ≫ e.hom.app R) :=
    Functor.isoWhiskerRight (Functor.mapModNatIso e R) (Mod.comap ρ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (G.mapMod R) (Mod.comapComp ρ (e.hom.app R)).symm
  have hG := h (ρ ≫ e.hom.app R)
  exact ⟨fun {M} hM ↦ ObjectProperty.prop_of_iso _ (i.app M).symm (hG.flat_obj hM)⟩

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

-- Preserve the existing hypotheses although the general site theorem needs fewer of them.
set_option linter.unusedSectionVars false in
/-- Component inverse image preserves flat internal modules.
Source: Hemo--Richarz--Scholbach, Construction (4.1), Proposition 4.3(3);
Stacks Project, Tag 05VD, lemma-pullback-flat
(blueprint: lem-zl-component-pullback-flat).

Proof: take the section ring and section module under the internal/sectionwise
module equivalences. The relative-test universal property says that componentTests
preserves finite limits. Its comma categories are filtered, so left Kan extension
and sheafification give a left exact inverse image on sets. The abelian and ring
lifts apply this same inverse image to the algebraic operations. Comparison of the
adjunctions with precomposition identifies their ring and module lifts, including
the scalar action, with the algebraic inverse image on section modules. The tensor
comparison is determined by the universal bilinear pairing; hence this identification
is compatible with the monoidal lift used by componentModules.

Use the local equational criterion for flatness. For a finite relation in the
inverse image module, first pass to a covering on which all its coefficients and
sections lift to the left Kan extension. After a further covering their relation
is zero there. Filteredness gives one source object on which all the lifted terms
and their relation are represented. Source flatness supplies locally a finite
factorization of the lifted sections whose coefficient matrix kills the relation.
Pull that covering and its factorization back to obtain the required factorization
of the original relation. Thus algebraic inverse image preserves site-flatness.
The coefficient isomorphism transports each relation and its factorization in both
directions, so restriction along its inverse preserves site-flatness. Finally use
the balanced tensor comparison to recover internal flatness. Empty finite lists,
the zero ring and the empty scheme satisfy the same argument. -/
theorem component_pullback_preservesFlat
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T)) :
    (componentModules Λ.X T α).PreservesFlat := by
  let : PreservesFiniteLimits (componentTests T) :=
    (Classical.choose_spec (component_relative_profinite_site T)).2.2.2.2.2.1
  let : RepresentablyFlat (componentTests T) := flat_of_preservesFiniteLimits _
  let b := (inferInstance : (componentInverse T).Braided)
  let e := componentUnitCorrection T
  let b₀ : (componentInverse T).Braided := by
    let m₀ := componentCanonicalMonoidal T
    exact { toMonoidal := m₀
            braided := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (componentTests T) Ab.{u + 1}
              ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
              (Scheme.ProEt.topology T)).μ_comp_map_braiding }
  let he : @NatTrans.IsMonoidal _ _ _ _ _ _
      (componentInverse T) (componentInverse T) e.hom
      b.toMonoidal.toLaxMonoidal b₀.toMonoidal.toLaxMonoidal := by
    let := b
    exact @NatTrans.IsMonoidal.mk _ _ _ _ _ _
      (componentInverse T) (componentInverse T) e.hom
      b.toMonoidal.toLaxMonoidal b₀.toMonoidal.toLaxMonoidal
      (correction_unit T) (component_unit_normalized_tensor T)
  apply preservesFlat_transport (bF := b) (bG := b₀) e
    (profiniteCoefficient Λ.X (affineComponentSpace T)) (condensedRingObj Λ.X T) α.inv.hom
  intro σ _ _
  exact CategoryTheory.SiteInverseImageModuleFlat.siteInverseImageModule_preservesFlat
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T) (componentTests T)
    (profiniteCoefficient Λ.X (affineComponentSpace T)) (condensedRingObj Λ.X T)
    σ

end AlgebraicGeometry.ProEtale.CondensedRing
