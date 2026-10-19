/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
public import Sheaf.AlgebraicGeometry.EllAdicRationalConstantModelCohomology
import all Sheaf.AlgebraicGeometry.EllAdicIntegralConstructibleConstantComparison
import all Sheaf.AlgebraicGeometry.EllAdicRationalConstantModelCohomology
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Sheaf.CategoryTheory.Triangulated.LocalizingFunctor
import Sheaf.Paper.LocalizingClosureExistence
import Sheaf.SixFunctors.IntegralRestrictionGlue
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Integral geometric cohomology preservation

Source: det-existence-restriction.proof.md, rational and integral restriction bullets.
(blueprint: lem-sfb-adic-integral-constant-model-cohomology)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

private theorem integral_coefficient_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F.val)) := by
  let f : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)
  let e : E ≃ₐ[ℚ_[ℓ]] f.fieldRange := f.equivFieldRange
  let : FiniteDimensional ℚ_[ℓ] f.fieldRange := e.toLinearEquiv.finiteDimensional
  let F : PadicAlgCl.FiniteIntermediateField ℓ := ⟨f.fieldRange, inferInstance⟩
  let eI : PadicAlgCl.integers ℓ E ≃+* PadicAlgCl.integers ℓ F.val :=
    e.toRingEquiv.restrict _ _ (by
      intro x
      rw [PadicAlgCl.mem_integers_iff, PadicAlgCl.mem_integers_iff]
      rfl)
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F.val
  have hi : Isometry eI := by intro x y; rfl
  let ei : PadicAlgCl.integers ℓ E ≃ᵢ PadicAlgCl.integers ℓ F.val :=
    { eI.toEquiv with isometry_toFun := hi }
  let es : Profinite.padicIntegersCondensedRing.{u} ℓ E ≅
      Profinite.padicIntegersCondensedRing.{u} ℓ F.val := by
    apply ObjectProperty.isoMk _
    refine NatIso.ofComponents (fun V ↦
      (ULift.ringEquiv.trans ((continuousMapRingEquiv eI
        ei.continuous ei.symm.continuous V.unop).trans
          ULift.ringEquiv.symm)).toRingCatIso) ?_
    intro V V' a
    rfl
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso es
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ es.hom
  have : IsMonHom ea.inv := Sheaf.isMonHom_sheafCompose_map _ es.inv
  exact ⟨F, ⟨{ hom := ⟨ea.hom⟩
               inv := ⟨ea.inv⟩
               hom_inv_id := by apply Mon.Hom.ext; exact ea.hom_inv_id
               inv_hom_id := by apply Mon.Hom.ext; exact ea.inv_hom_id }⟩⟩

section Transport
variable {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
  (φ : Λ ⟶ Γ) [IsMonHom φ] [IsIso φ]

private noncomputable abbrev coefficientComap (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  Mod.comap (coefficientMap φ X)

private lemma constant_bounded_comap (X : Scheme.{u}) [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Γ X))}
    (hK : constantModelBoundedConstructible Γ X K) :
    constantModelBoundedConstructible Λ X
      ((coefficientComap φ X).mapDerivedCategory.obj K) := by
  refine ⟨(Mod.comap (coefficientMap φ X)).bounded_mapDerivedCategory_obj hK.1, ?_⟩
  intro n
  exact constant_constructible_iso
    (((coefficientComap φ X).mapDerivedCategoryHomologyFunctorIso n).app K)
    (constant_constructible_comap φ (hK.2 n))

private noncomputable def comap_roundtrip (X : Scheme.{u}) :
    (coefficientComap φ X).mapDerivedCategory ⋙
      (coefficientComap (inv φ) X).mapDerivedCategory ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (coefficientMap (inv φ) X) (coefficientMap φ X)).symm ≪≫
        Mod.comapCongr (by
          change (upperStarFromPoint X).map (inv φ) ≫
            (upperStarFromPoint X).map φ = _
          rw [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]) ≪≫
        Mod.comapId _) ≪≫
    Functor.mapDerivedCategoryIdIso _

private noncomputable def coefficientDerivedEquivalence (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Γ X)) ≌
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  CategoryTheory.Equivalence.mk (coefficientComap φ X).mapDerivedCategory
    (coefficientComap (inv φ) X).mapDerivedCategory
    (comap_roundtrip φ X).symm
    (by simpa using comap_roundtrip (inv φ) X)

private lemma constant_hull_comap (X : Scheme.{u}) [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Γ X))}
    (hK : localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Γ X) K) :
    localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X)
      ((coefficientComap φ X).mapDerivedCategory.obj K) := by
  obtain ⟨sΓ, _, _, _, _, _, _, _⟩ := localizingClosure_exists Γ X
    (constantModelBoundedConstructible Γ X)
  obtain ⟨sΛ, _, _, _, _, _, _, _⟩ := localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X)
  let := sΓ
  let := sΛ
  have : (coefficientComap φ X).IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap φ X)).functor.IsEquivalence
  obtain ⟨_, _, hh, _, _⟩ := Functor.maps_localizingClosure
    (constantModelBoundedConstructible Γ X) (constantModelBoundedConstructible Λ X)
    (coefficientComap φ X).mapDerivedCategory (fun L hL ↦ constantModel_le_localizingClosure Λ X _
      (constant_bounded_comap φ X hL))
  exact hh K hK

private lemma constant_hull_iso_closed (X : Scheme.{u}) :
    (localizingClosureOfSize.{u + 1}
      (constantModelBoundedConstructible Λ X)).IsClosedUnderIsomorphisms := by
  constructor
  intro K L e hK P hP hS
  let := hP.2.1
  exact P.prop_of_iso e (hK P hP hS)

private lemma constant_hull_comap_iff (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Γ X))) :
    localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X)
      ((coefficientComap φ X).mapDerivedCategory.obj K) ↔
    localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Γ X) K := by
  refine ⟨fun h ↦ ?_, constant_hull_comap φ X⟩
  let := constant_hull_iso_closed (Λ := Γ) X
  exact ObjectProperty.prop_of_iso _ ((comap_roundtrip φ X).app K)
    (constant_hull_comap (inv φ) X h)

private noncomputable def coefficientPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R((f)_*⟦Γ⟧) ⋙ (coefficientComap φ Y).mapDerivedCategory ≅
      (coefficientComap φ X).mapDerivedCategory ⋙ R((f)_*⟦Λ⟧) := by
  have (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ T)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (coefficientMap φ T)).symm
  exact derivedComapLowerStarIso φ f

private noncomputable def coefficientHullEquivalence (X : Scheme.{u}) [IsNoetherian X] :
    (localizingClosureOfSize.{u + 1}
      (constantModelBoundedConstructible Γ X)).FullSubcategory ≌
    (localizingClosureOfSize.{u + 1}
      (constantModelBoundedConstructible Λ X)).FullSubcategory := by
  let := constant_hull_iso_closed (Λ := Λ) X
  let := constant_hull_iso_closed (Λ := Γ) X
  let e := coefficientDerivedEquivalence φ X
  apply e.congrFullSubcategory
  funext K
  apply propext
  constructor
  · intro hK
    exact ObjectProperty.prop_of_iso _ (e.unitIso.app K).symm
      (constant_hull_comap (inv φ) X hK)
  · exact constant_hull_comap φ X

end Transport

private theorem integral_image_cohomology
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Z ⟶ Y) [IsProper g.left]
    (h : ∀ K, localizingClosureOfSize.{u + 1}
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Z.left) K →
      localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y.left)
        ((R((g.left)_*⟦(Profinite.padicIntegersRingObj ℓ E.val)⟧)).obj K))
    (G : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible
          (Profinite.padicIntegersRingObj ℓ E.val) Y.left)).FullSubcategory ⥤
      (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible
          (Profinite.padicIntegersRingObj ℓ E.val) Z.left)).FullSubcategory)
    (adj : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y.left)).lift
      ((localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Z.left)).ι ⋙
          R((g.left)_*⟦Profinite.padicIntegersRingObj ℓ E.val⟧))
      (fun K ↦ h K.obj K.property) ⊣ G)
    (K : (constantModelBoundedConstructible
      (Profinite.padicIntegersRingObj ℓ E.val) Y.left).FullSubcategory) :
    ∀ n : ℤ, IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) Z.left
      ((DerivedCategory.homologyFunctor _ n).obj
        (G.obj ((ObjectProperty.ιOfLE (constantModel_le_localizingClosure
          (Profinite.padicIntegersRingObj ℓ E.val) Y.left)).obj
          K)).obj) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have he (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
      localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X) =
        IntegralCompactSupport.localizing Λ X := by
    have hc := (localizingClosure_ctf_equals_bc ℓ X Λ
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.1
    exact (hull_eq Λ X hc).trans (by
      unfold localizingClosureProEtale IntegralCompactSupport.localizing
      rw [hc])
  let CZ := localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Z.left)
  let CY := localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Y.left)
  let iZ := ObjectProperty.ιOfLE (le_of_eq (he Z.left).symm)
  let iY := ObjectProperty.ιOfLE (le_of_eq (he Y.left).symm)
  let jZ := ObjectProperty.ιOfLE (le_of_eq (he Z.left))
  let Gc := iY ⋙ G ⋙ jZ
  let c : Compactification.BoundaryCompactification g.left :=
    ⟨⟨properIdentityCompactification g.left, by
      change QuasiCompact (𝟙 Z.left)
      infer_instance⟩⟩
  have hs : ∀ L, IntegralCompactSupport.localizing Λ Z.left L →
      IntegralCompactSupport.localizing Λ Y.left ((R((g.left)_*⟦Λ⟧)).obj L) := by
    intro L hL
    exact le_of_eq (he Y.left) _ (h L (le_of_eq (he Z.left).symm _ hL))
  have hd : ∀ L, IntegralCompactSupport.localizing Λ Z.left L →
      IntegralCompactSupport.localizing Λ Y.left
        ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj L) := by
    intro L hL
    obtain ⟨_, _, _, hp, _, _, _, _⟩ := localizingClosure_exists Λ Y.left
      (constantModelBoundedConstructible Λ Y.left)
    let : (IntegralCompactSupport.localizing Λ Y.left).IsClosedUnderIsomorphisms := hp.2.1
    exact ObjectProperty.prop_of_iso _ ((properIdentityPushforwardIso Λ g.left).app L).symm
      (hs L hL)
  let Fc := IntegralCompactSupport.lowerShriek Λ c.obj.obj hd
  let Fs := CY.lift (CZ.ι ⋙ R((g.left)_*⟦Λ⟧)) (fun L ↦ h L.obj L.property)
  have eF : iZ ⋙ Fs ≅ Fc ⋙ iY :=
    NatIso.ofComponents (fun L ↦
      ObjectProperty.isoMk _ ((properIdentityPushforwardIso Λ g.left).app L.obj).symm)
      (fun f ↦ by ext; exact ((properIdentityPushforwardIso Λ g.left).inv.naturality f.hom))
  have eG : iY ⋙ G ≅ Gc ⋙ iZ :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by simp; rfl)
  have adjc : Fc ⊣ Gc := adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _) eF eG
  have : LocallyOfFiniteType (Z.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : QuasiCompact (Z.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Z.hom)
  have : IsSeparated (Z.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Z.hom)
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  have : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  obtain ⟨_, hGc, _⟩ := (IntegralCompactSupport.IntegralRestriction.integralRestrictionGlue.{u, u}
    ℓ E k).2 Z.left Y.left g.left c hd Gc adjc
  have hK : IntegralCompactSupport.localizing Λ Y.left K.obj :=
    le_of_eq (he Y.left) _ (constantModel_le_localizingClosure Λ Y.left _ K.property)
  exact (hGc ⟨K.obj, hK⟩ K.property).2

/-- Integral geometric preservation on the ordinary finite-constant-model hull.
Source: det-existence-restriction.proof.md, integral bullet; sk-thm-int-restriction.
Proof: identify this valuation ring with that of the image finite intermediate
field in the fixed algebraic closure, transporting its continuous condensed ring
and scalar presentations. Integral finite-Tor comparison identifies Dctf and Dbc.
The identity compactification of the proper map identifies its localizing compact
support functor with derived pushforward in the same coproduct universe u+1.
The integral Brown adjunction and geometric restriction theorem apply: on finite
affine charts use the smooth-projection formula and the closed restriction theorem,
then finite-open gluing. The full inclusions and uniqueness of right adjoints
transport the cohomology back to G. This includes torsion, the zero module, empty
schemes and every degree, and imposes no completed-category replacement.
(blueprint: lem-sfb-adic-integral-constant-model-cohomology) -/
theorem ellAdic_integral_constantModel_rightAdjoint_homology_constructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Z ⟶ Y) [IsProper g.left]
    (h : ∀ K, localizingClosureOfSize.{u + 1}
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Z.left) K →
      localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y.left)
        ((R((g.left)_*⟦(Profinite.padicIntegersRingObj ℓ E)⟧)).obj K))
    (G : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible
          (Profinite.padicIntegersRingObj ℓ E) Y.left)).FullSubcategory ⥤
      (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible
          (Profinite.padicIntegersRingObj ℓ E) Z.left)).FullSubcategory)
    (adj : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y.left)).lift
      ((localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Z.left)).ι ⋙
          R((g.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧))
      (fun K ↦ h K.obj K.property) ⊣ G)
    (K : (constantModelBoundedConstructible
      (Profinite.padicIntegersRingObj ℓ E) Y.left).FullSubcategory) :
    ∀ n : ℤ, IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) Z.left
      ((DerivedCategory.homologyFunctor _ n).obj
        (G.obj ((ObjectProperty.ιOfLE (constantModel_le_localizingClosure
          (Profinite.padicIntegersRingObj ℓ E) Y.left)).obj
          K)).obj) := by
  obtain ⟨F, ⟨e⟩⟩ := integral_coefficient_normalization.{u} ℓ E
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E
  let Γ := Profinite.padicIntegersRingObj.{u} ℓ F.val
  let φ : Λ ⟶ Γ := e.hom.hom
  have : IsMonHom φ := inferInstance
  have : IsIso φ := inferInstance
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : IsNoetherian Y.left := ⟨⟩
  let CZ := localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Γ Z.left)
  let CY := localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Γ Y.left)
  let eZ := coefficientHullEquivalence φ Z.left
  let eY := coefficientHullEquivalence φ Y.left
  have hΓ : ∀ L, CZ L → CY ((R((g.left)_*⟦Γ⟧)).obj L) := by
    intro L hL
    apply (constant_hull_comap_iff φ Y.left _).mp
    let := constant_hull_iso_closed (Λ := Λ) Y.left
    exact ObjectProperty.prop_of_iso _
      ((coefficientPushforwardIso φ g.left).app L).symm
      (h _ (constant_hull_comap φ Z.left hL))
  let Fs := CY.lift (CZ.ι ⋙ R((g.left)_*⟦Γ⟧)) (fun L ↦ hΓ L.obj L.property)
  let GΓ := eY.functor ⋙ G ⋙ eZ.inverse
  have eF : eZ.functor ⋙
      (localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Y.left)).lift
        ((localizingClosureOfSize.{u + 1}
          (constantModelBoundedConstructible Λ Z.left)).ι ⋙ R((g.left)_*⟦Λ⟧))
        (fun L ↦ h L.obj L.property) ≅ Fs ⋙ eY.functor :=
    NatIso.ofComponents (fun L ↦
      ObjectProperty.isoMk _ ((coefficientPushforwardIso φ g.left).app L.obj).symm)
      (fun f ↦ by
        ext
        exact (coefficientPushforwardIso φ g.left).inv.naturality f.hom)
  have eG : eY.functor ⋙ G ≅ GΓ ⋙ eZ.functor :=
    NatIso.ofComponents (fun L ↦ eZ.counitIso.symm.app (G.obj (eY.functor.obj L)))
      (fun f ↦ eZ.counitIso.inv.naturality (G.map (eY.functor.map f)))
  have adjΓ : Fs ⊣ GΓ := adj.restrictFullyFaithful
    eZ.fullyFaithfulFunctor eY.fullyFaithfulFunctor eF eG
  let KΓ : (constantModelBoundedConstructible Γ Y.left).FullSubcategory :=
    ⟨(coefficientComap (inv φ) Y.left).mapDerivedCategory.obj K.obj,
      constant_bounded_comap (inv φ) Y.left K.property⟩
  let AΓ : CY.FullSubcategory :=
    (ObjectProperty.ιOfLE (constantModel_le_localizingClosure Γ Y.left)).obj KΓ
  let A : (localizingClosureOfSize.{u + 1}
      (constantModelBoundedConstructible Λ Y.left)).FullSubcategory :=
    (ObjectProperty.ιOfLE (constantModel_le_localizingClosure Λ Y.left)).obj K
  have ei : eY.functor.obj AΓ ≅ A :=
    eY.counitIso.app A
  have eo : eZ.functor.obj (GΓ.obj AΓ) ≅ G.obj A :=
    eZ.counitIso.app (G.obj (eY.functor.obj AΓ)) ≪≫ G.mapIso ei
  intro n
  have hn := integral_image_cohomology ℓ F g hΓ GΓ adjΓ KΓ n
  have ht := constant_constructible_comap φ hn
  apply constant_constructible_iso _ ht
  exact ((coefficientComap φ Z.left).mapDerivedCategoryHomologyFunctorIso n).app
    (GΓ.obj AΓ).obj ≪≫ (DerivedCategory.homologyFunctor _ n).mapIso
      ((localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Z.left)).ι.mapIso eo)


end AlgebraicGeometry.ProEtale.CondensedRing
