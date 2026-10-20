/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.CategoryTheory.RingedPresentationData
import Sheaf.CategoryTheory.RingedEquivalenceModuleHom
import Sheaf.CategoryTheory.ElementRestrictionHom
import Sheaf.CategoryTheory.RingedEquivalenceSlices
import Sheaf.CategoryTheory.RingedEquivalenceLocalTests
import Sheaf.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem sequence_colimit_transport
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [PreservesColimitsOfShape ℕ F]
    {X : A} {Y : B} (f : X ⟶ X) (g : Y ⟶ Y)
    (i : F.obj X ≅ Y) (h : F.map f ≫ i.hom = i.hom ≫ g)
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f)))
    (d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ g)))
    (hc : IsColimit c) (hd : IsColimit d) :
    ∃ q : F.obj c.pt ≅ d.pt,
      F.map (c.ι.app 0) ≫ q.hom = i.hom ≫ d.ι.app 0 := by
  let α : Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f) ⋙ F ⟶
      Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ g) :=
    NatTrans.ofSequence (fun _ ↦ i.hom) (by
      intro n
      dsimp only [Functor.comp_map]
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
      exact h)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    change IsIso i.hom
    infer_instance
  exact ⟨(isColimitOfPreserves F hc).coconePointsIsoOfNatIso hd (asIso α),
    IsColimit.comp_coconePointsIsoOfNatIso_hom
      (isColimitOfPreserves F hc) hd (asIso α) 0⟩

private theorem localization_transport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S)
    [PreservesColimitsOfShape ℕ F]
    (i : F.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
      SheafOfModules.unit (localCoefficientRings S))
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (t : (S.obj ⋙ forget CommRingCat).sections)
    (h : F.map (presentationScalar R s) ≫ i.hom = i.hom ≫ presentationScalar S t) :
    ∃ l : F.obj (ringedSectionLocalizationOfUniverses R s) ≅
        ringedSectionLocalizationOfUniverses S t,
      F.map (ringedSectionLocalizationUnit R s) ≫ l.hom =
        i.hom ≫ ringedSectionLocalizationUnitOfUniverses S t := by
  change ∃ l : F.obj (ringedSectionLocalization R s) ≅ ringedSectionLocalization S t,
    F.map (ringedSectionLocalizationUnit R s) ≫ l.hom =
      i.hom ≫ ringedSectionLocalizationUnit S t
  have scalar_eq {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
      (T : Sheaf L CommRingCat.{u}) (a : (T.obj ⋙ forget CommRingCat).sections) :
      presentationScalar T a = (SheafOfModules.unitHomEquiv _).symm
        ⟨a.val, a.property⟩ := by
    apply (SheafOfModules.unitHomEquiv _).injective
    rw [Equiv.apply_symm_apply]
    ext U
    change (a.val U : T.obj.obj U) * 1 = a.val U
    exact mul_one _
  obtain ⟨c, ⟨hc⟩, ec, hec⟩ := scalarLocalization_regularColimit R s
  obtain ⟨d, ⟨hd⟩, ed, hed⟩ := scalarLocalization_regularColimit S t
  rw [scalar_eq R s, scalar_eq S t] at h
  obtain ⟨q, hq⟩ := sequence_colimit_transport F _ _ i h c d hc hd
  refine ⟨(F.mapIso ec).symm ≪≫ q ≪≫ ed, ?_⟩
  have hc0 : F.map (ringedSectionLocalizationUnit R s) ≫ F.map ec.inv =
      F.map (c.ι.app 0) := by
    exact (F.map_comp _ _).symm.trans
      (congrArg F.map ((Iso.comp_inv_eq ec).mpr hec.symm))
  change F.map (ringedSectionLocalizationUnit R s) ≫
    ((F.map ec.inv ≫ q.hom) ≫ ed.hom) = _
  rw [← Category.assoc, ← Category.assoc, hc0, Category.assoc, reassoc_of% hq, hed]

private def presentationFunctorOfCore
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    {F : PresentationModules R ⥤ PresentationModules S}
    (T : RingedPresentationCore R S F) : RingedPresentationFunctor R S F where
  additive := T.additive
  finiteLimits := T.finiteLimits
  finiteColimits := T.finiteColimits
  termwise := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := T.additive
    let := T.finiteLimits
    let := T.finiteColimits
    exact ⟨F.mapDerivedCategoryFactors⟩
  unit := T.unit
  kInjective := T.kInjective
  internalHom := T.internalHom
  localization := by
    let := T.sequentialColimits
    exact localization_transport F T.unit

private def presentationCoreOfEquivalence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S) [F.IsEquivalence]
    (i : F.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
      SheafOfModules.unit (localCoefficientRings S))
    (h : Nonempty (presentationRHom R ⋙
      presentationDerivedMap (R := R) (S := S) F (Functor.additive_of_preserves_binary_products _)
        (inferInstance) (inferInstance) ≅
      ((presentationDerivedMap (R := R) (S := S) F
          (Functor.additive_of_preserves_binary_products _) (inferInstance) (inferInstance)).op.prod
        (presentationDerivedMap (R := R) (S := S) F
          (Functor.additive_of_preserves_binary_products _) (inferInstance) (inferInstance))) ⋙
        presentationRHom S)) :
    RingedPresentationCore R S F := by
  letI ha : F.Additive := Functor.additive_of_preserves_binary_products F
  exact {
    additive := ha
    finiteLimits := inferInstance
    finiteColimits := inferInstance
    sequentialColimits := inferInstance
    unit := i
    kInjective := fun I hI ↦ by
      let := hI
      change CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I)
      infer_instance
    internalHom := h }

private def inverseHomComparison
    {A B : Type*} [Category A] [Category B] (E : A ≌ B)
    (H : Aᵒᵖ × A ⥤ A) (K : Bᵒᵖ × B ⥤ B)
    (a : H ⋙ E.functor ≅ (E.functor.op.prod E.functor) ⋙ K) :
    K ⋙ E.inverse ≅ (E.inverse.op.prod E.inverse) ⋙ H :=
  (Iso.isoCompInverse (H := E)
    (Functor.associator _ _ _ ≪≫
      Iso.inverseCompIso (G := E.op.prod E) a)).symm

private def presentationEquivalenceOfCore
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (T : RingedPresentationEquivalenceCore R S) : RingedPresentationEquivalence R S where
  modules := T.modules
  forward := presentationFunctorOfCore
    (presentationCoreOfEquivalence (R := R) (S := S)
      T.modules.functor T.forwardUnit T.forwardHom)
  backward := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := Functor.additive_of_preserves_binary_products T.modules.functor
    let := Functor.additive_of_preserves_binary_products T.modules.inverse
    exact presentationFunctorOfCore (presentationCoreOfEquivalence (R := S) (S := R)
      T.modules.inverse
      (T.modules.inverse.mapIso T.forwardUnit.symm ≪≫ T.modules.unitIso.symm.app _)
      (T.forwardHom.map (fun a ↦ inverseHomComparison T.modules.mapDerivedCategory _ _ a)))
  derivedUnit := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := Functor.additive_of_preserves_binary_products T.modules.functor
    let := Functor.additive_of_preserves_binary_products T.modules.inverse
    exact ⟨T.modules.mapDerivedCategory.unitIso.symm⟩
  derivedCounit := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := Functor.additive_of_preserves_binary_products T.modules.functor
    let := Functor.additive_of_preserves_binary_products T.modules.inverse
    exact ⟨T.modules.mapDerivedCategory.counitIso⟩

private theorem presentationAt
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] : Nonempty (RingedPresentationAt e) := by
  obtain ⟨T, ⟨p⟩, a, ha⟩ := ringed_equivalence_module_hom e
  exact ⟨{ transport := presentationEquivalenceOfCore T
           pushforward := p
           underlying := a
           structural := ha }⟩

private def elementRestrictionCore
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (h : Nonempty (presentationRHom R ⋙
      presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
        (presentationElementRestriction_additive R A)
        (presentationElementRestriction_exact R A).1
        (presentationElementRestriction_exact R A).2.1 ≅
      ((presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
          (presentationElementRestriction_additive R A)
          (presentationElementRestriction_exact R A).1
          (presentationElementRestriction_exact R A).2.1).op.prod
        (presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
          (presentationElementRestriction_additive R A)
          (presentationElementRestriction_exact R A).1
          (presentationElementRestriction_exact R A).2.1)) ⋙
        presentationRHom (presentationElementRing R A))) :
    RingedPresentationCore R (presentationElementRing R A)
      (elementModulePullback.{u, u} (localCoefficientRings R) A) where
  additive := presentationElementRestriction_additive R A
  finiteLimits := (presentationElementRestriction_exact R A).1
  finiteColimits := (presentationElementRestriction_exact R A).2.1
  sequentialColimits := (presentationElementRestriction_exact R A).2.2
  unit := Iso.refl _
  kInjective := fun I hI ↦ by
    let := presentationElementRestriction_additive R A
    let := hI
    change CochainComplex.IsKInjective
      (((elementModulePullback (localCoefficientRings R) A).mapHomologicalComplex (.up ℤ)).obj I)
    exact presentationElementRestriction_kInjective R A I
  internalHom := h

private theorem presentationRestrictions
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Nonempty (RingedPresentationRestrictions R) := by
  classical
  obtain ⟨s, rhom, hs, hsite⟩ := element_restriction_hom R
  let h := fun {A B : Sheaf J (Type u)} (b : B ⟶ A) ↦
    presentationElementRestriction_continuous b
  have hrel := fun {A B : Sheaf J (Type u)} (b : B ⟶ A) ↦
    presentationElementRestriction_relocalization R b (h b)
  let r := fun A ↦ elementRestrictionCore R A (rhom A)
  refine ⟨{
    restriction := fun A ↦ presentationFunctorOfCore (r A)
    restrictionUnit := fun _ ↦ rfl
    overContinuous := h
    overRestriction := fun b ↦ presentationFunctorOfCore (s b)
    overUnit := hs
    relocalization := hrel
    derivedRelocalization := ?_
    siteObject := ?_ }⟩
  · intro A B b
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules (presentationElementRing R A))
    let := HasDerivedCategory.standard (PresentationModules (presentationElementRing R B))
    let := (r A).additive
    let := (r A).finiteLimits
    let := (r A).finiteColimits
    let := (s b).additive
    let := (s b).finiteLimits
    let := (s b).finiteColimits
    let := (r B).additive
    let := (r B).finiteLimits
    let := (r B).finiteColimits
    obtain ⟨a⟩ := hrel b
    exact ⟨(Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso a⟩
  · intro U
    obtain ⟨E, hE⟩ := hsite U
    exact ⟨presentationEquivalenceOfCore E, hE⟩

private theorem presentationDerivedSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    [PreservesFiniteLimits H] [PreservesFiniteLimits I]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    [PreservesFiniteColimits H] [PreservesFiniteColimits I]
    (a : F ⋙ G ≅ H ⋙ I) :
    Nonempty (F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ I.mapDerivedCategory) := by
  exact ⟨(Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso H I⟩

/-- An equivalence of ringed topoi transports module sheaves, their unbounded derived
categories, all sheaf slices, derived internal Hom, section localizations and local tests.

Source: Stacks Project, Modules on Sites, Tag 03CR, equivalence case, and Algebraization,
Tag 099J, opening reduction (blueprint: lem-weil-pbc-ringed-presentation-transport).

Proof, following the nine steps of the node:
1. Use the tensor adjunction (lem-weil-pbc-ringed-topoi-module-adjunction). Since the
   structural ring map is invertible, pullback is inverse image with its transported
   scalar action. Transport the additive and scalar operations through the sheaf
   equivalence. The linear unit and counit are isomorphisms. An additive equivalence
   preserves kernels and cokernels, hence is exact.
2. Localize the two termwise functors using
   lem-weil-pbc-exact-functor-derived-factorization. Their termwise unit and counit give
   the inverse derived equivalences, without boundedness assumptions.
3. Adjunction on homotopy categories identifies maps from an acyclic complex into the
   transported complex with maps into the original K-injective. The inverse exact
   functor preserves acyclicity; the latter maps are null-homotopic. Interchange the
   functors for the reverse direction (def-pur-kinjective-complex).
4. Apply the equivalence to arrows into A. Its inverse uses the original equivalence
   unit. Finite-product preservation identifies the restricted rings. Use the element
   sites of lem-weil-pbc-ringed-sheaf-slice-adjunction. Further restrictions are the same
   fibre products. For site objects use lem-weil-pbc-localized-sheaves-over-representable
   over the sheafified representable; no subcanonicity is needed.
5. The pullback is exact and computes derived pullback. Tensor preservation from
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback and the closed adjunction from
   lem-sf-ringed-derived-closed-symmetric-monoidal identify, naturally in C,L,M,
   Hom(C,F RHom(L,M)) with Hom(G C,RHom(L,M)), then Hom(G C tensor L,M), then
   Hom(C tensor F L,F M), then Hom(C,RHom(F L,F M)). Yoneda gives the comparison.
6. The exact left adjoint j_A! makes j_A* preserve K-injectives by
   lem-weil-pbc-right-adjoint-preserves-kinjective. On the element site, slicing at (U,s)
   is C/U. Restriction preserves sheaf Hom and sectionwise products, hence the Hom
   complex with differential d phi = d_I phi - (-1)^n phi d_L. Compute derived Hom
   with a K-injective target (def-pur-sheaf-hom, def-pur-hom-complex and
   def-pur-derived-internal-hom). The same restriction formulas give relocalization.
7. Section localization is the module-sheaf colimit of repeated multiplication by the
   section (def-weil-pbc-local-coefficient-localization). Equivalences and restriction
   preserve this colimit and its map from the ring. The multiplication comparison
   therefore identifies the two localizations and their unit maps.
8. Tests on site objects imply tests on an arbitrary sheaf A: restrict the derived Hom
   to every (U,s) of its element site. Steps 6-7 give zero; exactness makes every
   cohomology sheaf have zero values, so the object is zero. Conversely take A to be
   the sheafified representable. Empty sites and empty covering sieves cause no exception.
9. Full faithfulness identifies ideal sections under inverse image, and essential
   surjectivity covers every test sheaf on the other side. Steps 5 and 7 identify the
   test objects; the slice equivalences preserve and reflect zero. Step 8 gives exactly
   the two site-object families, for every ideal and every unbounded N. -/
theorem ringed_presentation_transport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] :
    Nonempty (RingedPresentationTransport e) := by
  classical
  obtain ⟨whole⟩ := presentationAt e
  obtain ⟨rs⟩ := presentationRestrictions S
  obtain ⟨rt⟩ := presentationRestrictions R
  have hs : ∀ A : Sheaf K (Type u),
      Nonempty (RingedSheafSliceAdjunctionData (localCoefficientRings S) A) :=
    fun A ↦ ringed_sheaf_slice_adjunction _ A
  have ht : ∀ A : Sheaf J (Type u),
      Nonempty (RingedSheafSliceAdjunctionData (localCoefficientRings R) A) :=
    fun A ↦ ringed_sheaf_slice_adjunction _ A
  let ss := fun A ↦ Classical.choice (hs A)
  let ts := fun A ↦ Classical.choice (ht A)
  obtain ⟨s, h, k, q, htop, hstruct, hm⟩ := ringed_equivalence_slices e ss ts
  have hT : ∀ A : Sheaf K (Type u), Nonempty (RingedPresentationAt (s A)) := by
    intro A
    let := h A
    let := k A
    exact presentationAt (s A)
  let T := fun A ↦ Classical.choice (hT A)
  obtain ⟨hr, hf⟩ := hm whole T rs rt
  refine ⟨{
    whole := whole
    sourceRestrictions := rs
    targetRestrictions := rt
    sourceSlices := ss
    targetSlices := ts
    sliceMorphism := s
    sliceInverseEquivalence := h
    sliceRingIsIso := k
    sliceTransport := T
    sliceTopos := htop
    sliceSets := q
    sliceStructural := hstruct
    restrictionModules := hr
    restrictionDerived := ?_
    furtherModules := hf
    furtherDerived := ?_
    localTests := ?_ }⟩
  · intro A
    let := HasDerivedCategory.standard (PresentationModules S)
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules (presentationElementRing S A))
    let := HasDerivedCategory.standard
      (PresentationModules (presentationElementRing R (e.inverse.obj A)))
    let := whole.transport.forward.additive
    let := whole.transport.forward.finiteLimits
    let := whole.transport.forward.finiteColimits
    let := (rt.restriction (e.inverse.obj A)).additive
    let := (rt.restriction (e.inverse.obj A)).finiteLimits
    let := (rt.restriction (e.inverse.obj A)).finiteColimits
    let := (rs.restriction A).additive
    let := (rs.restriction A).finiteLimits
    let := (rs.restriction A).finiteColimits
    let := (T A).transport.forward.additive
    let := (T A).transport.forward.finiteLimits
    let := (T A).transport.forward.finiteColimits
    obtain ⟨a⟩ := hr A
    exact presentationDerivedSquare _ _ _ _ a
  · intro A B b
    let := HasDerivedCategory.standard (PresentationModules (presentationElementRing S A))
    let := HasDerivedCategory.standard (PresentationModules (presentationElementRing S B))
    let := HasDerivedCategory.standard
      (PresentationModules (presentationElementRing R (e.inverse.obj A)))
    let := HasDerivedCategory.standard
      (PresentationModules (presentationElementRing R (e.inverse.obj B)))
    let := (T A).transport.forward.additive
    let := (T A).transport.forward.finiteLimits
    let := (T A).transport.forward.finiteColimits
    let := (rt.overRestriction (e.inverse.map b)).additive
    let := (rt.overRestriction (e.inverse.map b)).finiteLimits
    let := (rt.overRestriction (e.inverse.map b)).finiteColimits
    let := (rs.overRestriction b).additive
    let := (rs.overRestriction b).finiteLimits
    let := (rs.overRestriction b).finiteColimits
    let := (T B).transport.forward.additive
    let := (T B).transport.forward.finiteLimits
    let := (T B).transport.forward.finiteColimits
    obtain ⟨a⟩ := hf b
    exact presentationDerivedSquare _ _ _ _ a
  · intro N I ι hι
    exact ringed_equivalence_local_tests e whole N I ι

end CategoryTheory
