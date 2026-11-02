/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.ProEtaleCoefficients.ConnectedComponentsProfinite
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentPointMonoidalFactorization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentDerivedSymmetry
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentSectionRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentLisseEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentFinalScalarComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedPullbackSquare
import WeilConjectures.SixFunctors.Clopen.ClopenComponentHomeomorphism
import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting
import WeilConjectures.ZetaWeil.HenselianWStrictLocalInvariance

/-!
# Henselian rigidity of lisse condensed-coefficient complexes

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Corollary 4.4(1)--(2)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity).

## Main definitions and statement

* `discreteScalarExtensionPullbackIso` constructs the canonical comparison on all
  unbounded complexes over the discrete ring Γ(*, Λ), using the recorded constant functor.
* `henselian_lisse_rigidity` states the component homeomorphism, invariance of
  w-contractibility, and the exact symmetric monoidal lisse equivalence. Symmetric
  monoidality is `Functor.Braided` for the published Koszul braiding
  `DerivedCategory.braidedCategory'` of the derived tensor, passed explicitly in source
  and target.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ordinary unbounded derived inverse image of condensed modules from the point.
In particular it sends a discrete scalar complex extended to Λ to its scalar extension
on X. This is the existing inverse image, applied levelwise, with no completeness condition.
Source: HRS, Section 3, pullback paragraph before (3.1)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
def derivedFromCondensed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  ((upperStarFromPoint X).mapMod Λ).mapDerivedCategory

/-- The canonical coefficient-compatible comparison on module inverse images from the
point. It is induced by upperStarFromPointComp, followed by cancellation of restriction
and extension along the SAME coefficient isomorphism condensedPullbackHom.
Source: HRS, Section 3, pullback paragraph before (3.1)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
def fromCondensedPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarFromPoint Y).mapMod Λ ⋙ upperStar Λ f ≅
      (upperStarFromPoint X).mapMod Λ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapModCompIso (upperStarFromPoint Y) (ProEtale.upperStar Ab.{u + 1} f)
        (upperStarFromPointComp f).hom Λ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)) ≪≫
        (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).unitIso.symm) ≪≫
    Functor.rightUnitor _

/-- The derived canonical point comparison. Whiskering it with the realization of
constant discrete scalar complexes gives the scalar-extension compatibility in the
rigidity statement. It is the derived image of the specified coefficient comparison,
not a chosen unrelated isomorphism.
Source: HRS, Section 3, pullback paragraph before (3.1)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
def derivedFromCondensedPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedFromCondensed Λ Y ⋙ (upperStar Λ f).mapDerivedCategory ≅
      derivedFromCondensed Λ X :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (fromCondensedPullbackIso Λ f)

/-- The canonical scalar comparison for every unbounded discrete scalar complex.
It is obtained by whiskering the canonical coefficient-compatible point comparison,
so its coefficient map is exactly condensedPullbackHom, including for identities.
Source: HRS, Section 3, pullback paragraph before (3.1); Corollary 4.4
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
def discreteScalarExtensionPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    condensedScalarRealization Λ Y ⋙ (upperStar Λ f).mapDerivedCategory ≅
      condensedScalarRealization Λ X :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (derivedFromCondensedPullbackIso Λ f)))

private theorem mapMod_equivalence
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (e : C ≌ D) [e.functor.Monoidal]
    (R : C) [MonObj R] : (e.functor.mapMod R).IsEquivalence := by
  let := e.inverseMonoidal
  have hu (M : Mod C R) :
      IsIso ((e.toAdjunction.mapModAdjunction R).unit.app M) := by
    have : IsIso ((Mod.forget R).map
        ((e.toAdjunction.mapModAdjunction R).unit.app M)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_unit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget R)
  have hc (N : Mod D (e.functor.obj R)) :
      IsIso ((e.toAdjunction.mapModAdjunction R).counit.app N) := by
    have : IsIso ((Mod.forget (e.functor.obj R)).map
        ((e.toAdjunction.mapModAdjunction R).counit.app N)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget (e.functor.obj R))
  have : IsIso (e.toAdjunction.mapModAdjunction R).unit := NatIso.isIso_of_isIso_app _
  have : IsIso (e.toAdjunction.mapModAdjunction R).counit := NatIso.isIso_of_isIso_app _
  exact (e.toAdjunction.mapModAdjunction R).toEquivalence.isEquivalence_functor

private theorem dualizable_equivalence
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (E : C ≌ D) [E.functor.Monoidal] :
    ∃ e : ObjectProperty.FullSubcategory (IsDualizable (C := C)) ≌
        ObjectProperty.FullSubcategory (IsDualizable (C := D)),
      Nonempty (e.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ E.functor) := by
  let := E.inverseMonoidal
  let P : ObjectProperty C := IsDualizable
  let Q : ObjectProperty D := IsDualizable
  let : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.of_iso e⟩
  have heq : Q.inverseImage E.functor = P := by
    ext K
    exact ⟨fun h ↦ (h.map E.inverse).of_iso (E.unitIso.app K).symm,
      fun h ↦ h.map E.functor⟩
  exact ⟨E.congrFullSubcategory heq, ⟨Iso.refl _⟩⟩

private theorem lift_equivalence_of_witness
    {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (h : ∀ X, P X → Q (F.obj X))
    (e : P.FullSubcategory ≌ Q.FullSubcategory)
    (a : e.functor ⋙ Q.ι ≅ P.ι ⋙ F) :
    (Q.lift (P.ι ⋙ F) (fun X ↦ h X.obj X.property)).IsEquivalence := by
  exact Functor.isEquivalence_of_iso
    ((Q.fullyFaithfulι.whiskeringRight _).preimageIso a)

private theorem slice_direct_equivalence {P Q : Profinite.{u}} (h : Q ⟶ P)
    [IsIso h] : (ComponentDerivedSquare.sliceDirect h).IsEquivalence := by
  let F := ComponentDerivedSquare.sliceDirect h
  let G := ComponentDerivedSquare.sliceDirect (inv h)
  let a : Over.pullback (inv h) ⋙ Over.pullback h ≅ 𝟭 (Over Q) :=
    (Over.pullbackComp h (inv h)).symm ≪≫
      eqToIso (by
        change (fun k : Q ⟶ Q ↦ Over.pullback k) (h ≫ inv h) = _
        rw [IsIso.hom_inv_id]) ≪≫ Over.pullbackId
  let b : Over.pullback h ⋙ Over.pullback (inv h) ≅ 𝟭 (Over P) :=
    (Over.pullbackComp (inv h) h).symm ≪≫
      eqToIso (by
        change (fun k : P ⟶ P ↦ Over.pullback k) (inv h ≫ h) = _
        rw [IsIso.inv_hom_id]) ≪≫ Over.pullbackId
  let J := coherentTopology Profinite.{u}
  have : (Over.pullback (inv h) ⋙ Over.pullback h).IsContinuous (J.over Q) (J.over Q) :=
    Functor.isContinuous_comp _ _ _ (J.over P) _
  have : (Over.pullback h ⋙ Over.pullback (inv h)).IsContinuous (J.over P) (J.over P) :=
    Functor.isContinuous_comp _ _ _ (J.over Q) _
  let a' : F ⋙ G ≅ 𝟭 _ :=
    Functor.sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId' a _ _
  let b' : G ⋙ F ≅ 𝟭 _ :=
    Functor.sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId' b _ _
  exact (CategoryTheory.Equivalence.mk F G a'.symm b').isEquivalence_functor

private theorem slice_modules_equivalence
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {P Q : Profinite.{u}} (h : Q ⟶ P) [IsIso h]
    (s : ComponentDerivedSquare.Slice Λ h) : (s.modules Λ).IsEquivalence := by
  have := slice_direct_equivalence h
  have : s.inverse.IsEquivalence := s.adjunction.isEquivalence_left_of_isEquivalence_right
  let : s.inverse.asEquivalence.functor.Monoidal := s.braided.toMonoidal
  have hm := mapMod_equivalence s.inverse.asEquivalence (profiniteCoefficient Λ.X P)
  have : (s.inverse.mapMod (profiniteCoefficient Λ.X P)).IsEquivalence := hm
  have : (Mod.comap s.coefficient.inv.hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso s.coefficient.inv.hom).isEquivalence_functor
  dsimp only [ComponentDerivedSquare.Slice.modules]
  infer_instance

private theorem wContractible_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] [IsWContractibleRing R]
    (e : R ≃+* S) : IsWContractibleRing S := by
  have : IsWLocalRing S := IsWLocalRing.of_surjective (f := e.toRingHom) e.surjective
  have : IsWStrictlyLocalRing S := by
    refine ⟨fun m hm ↦ ?_⟩
    have : (m.comap e.toRingHom).IsMaximal :=
      (Ideal.isMaximal_comap_iff_of_bijective e.toRingHom e.bijective).mpr hm
    have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization
      (m.comap e.toRingHom)
    have hM : (m.comap e.toRingHom).primeCompl.map e.toMonoidHom = m.primeCompl := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        change e (e.symm x) ∉ m
        rwa [e.apply_symm_apply]
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.ringEquivOfRingEquiv
        (Localization.AtPrime (m.comap e.toRingHom)) (Localization.AtPrime m) e hM)
  have := IsWContractibleRing.extremallyDisconnected_connectedComponents (R := R)
  let h := PrimeSpectrum.homeomorphOfRingEquiv e
  have hc : ∀ y, _root_.IsConnected (h ⁻¹' {y}) := by
    intro y
    have heq : h ⁻¹' {y} = {h.symm y} := by
      ext x
      change h x = y ↔ x = h.symm y
      exact ⟨fun hx ↦ h.injective (hx.trans (h.apply_symm_apply y).symm),
        fun hx ↦ hx ▸ h.apply_symm_apply y⟩
    rw [heq]
    exact isConnected_singleton
  exact ⟨extremallyDisconnected_of_homeo
    (h.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hc)⟩

private theorem henselian_clopens (A : Type u) [CommRing A]
    (I : Ideal A) [HenselianRing A I] :
    Function.Bijective
      (fun U : TopologicalSpace.Clopens (PrimeSpectrum A) ↦
        (⟨PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' (U : Set (PrimeSpectrum A)),
          U.isClopen.preimage (PrimeSpectrum.continuous_comap _)⟩ :
          TopologicalSpace.Clopens (PrimeSpectrum (A ⧸ I)))) := by
  classical
  let q := Ideal.Quotient.mk I
  let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := A)
  let E' := PrimeSpectrum.isIdempotentElemEquivClopens (R := A ⧸ I)
  have hlift (e₀ : A ⧸ I) (he₀ : IsIdempotentElem e₀) :
      ∃! e : A, IsIdempotentElem e ∧ q e = e₀ := by
    have hmap : I.map (algebraMap A A) = I := by simp
    have h := Algebra.existsUnique_isIdempotentElem_of_henselianRing A I A
    rw [hmap] at h
    exact h e₀ he₀
  have hpre (e : {e : A // IsIdempotentElem e}) :
      (⟨PrimeSpectrum.comap q ⁻¹' (E e : Set (PrimeSpectrum A)),
        (E e).isClopen.preimage (PrimeSpectrum.continuous_comap q)⟩ :
        TopologicalSpace.Clopens (PrimeSpectrum (A ⧸ I))) = E' ⟨q e, e.property.map q⟩ := by
    ext x
    rfl
  constructor
  · intro U V h
    obtain ⟨e, rfl⟩ := E.surjective U
    obtain ⟨f, rfl⟩ := E.surjective V
    have heq : q e = q f := congrArg Subtype.val (E'.injective
      ((hpre e).symm.trans (h.trans (hpre f))))
    obtain ⟨g, _, hg⟩ := hlift (q e) (e.property.map q)
    exact congrArg E (Subtype.ext ((hg e ⟨e.property, rfl⟩).trans
      (hg f ⟨f.property, heq.symm⟩).symm))
  · intro U
    obtain ⟨e₀, rfl⟩ := E'.surjective U
    obtain ⟨e, ⟨he, hq⟩, _⟩ := hlift e₀ e₀.property
    refine ⟨E ⟨e, he⟩, (hpre ⟨e, he⟩).trans ?_⟩
    exact congrArg E' (Subtype.ext hq)

/-- The lisse equivalence part of henselian rigidity.

Source: HRS, Corollary 4.4(2); the proof uses the component evaluation and
component pullback comparison theorems together with the canonical coefficient map.
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
private theorem henselian_lisse_equivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (hA : IsWContractibleRing A)
    (hZ : IsWContractibleRing (A ⧸ I))
    (hh : IsHomeomorph
      (PrimeSpectrum.continuous_comap (Ideal.Quotient.mk I)).connectedComponentsMap) :
    (upperStar Λ (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory.IsTriangulated ∧
      Nonempty (@Functor.Braided _ _ _ (DerivedCategory.braidedCategory' _) _ _ _
        (DerivedCategory.braidedCategory' _)
        (upperStar Λ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory) ∧
      ∃ e :
        (ObjectProperty.FullSubcategory
          (IsDualizable (C := DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
              (condensedRingObj Λ (Spec (.of A))))))) ≌
        (ObjectProperty.FullSubcategory
          (IsDualizable (C := DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (A ⧸ I)))) Ab.{u + 1})
              (condensedRingObj Λ (Spec (.of (A ⧸ I)))))))),
        Nonempty (e.functor ⋙ ObjectProperty.ι _ ≅
          ObjectProperty.ι _ ⋙
            (upperStar Λ (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory) := by
  classical
  let : IsWContractibleRing A := hA
  let : IsWContractibleRing (A ⧸ I) := hZ
  let X := Spec (.of A)
  let Y := Spec (.of (A ⧸ I))
  let f : Y ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsWContractibleRing Γ(X, ⊤) := wContractible_of_ringEquiv
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  have : IsWContractibleRing Γ(Y, ⊤) := wContractible_of_ringEquiv
    (Scheme.ΓSpecIso (.of (A ⧸ I))).commRingCatIsoToRingEquiv.symm
  obtain ⟨s⟩ := ComponentDerivedSquare.component_derived_pullback_square (Mon.mk Λ)
  let CX : ObjectProperty (Evaluation.D (Scheme.ProEt.topology X)
      (condensedRingObj Λ X)) := IsDualizable
  let CY : ObjectProperty (Evaluation.D (Scheme.ProEt.topology Y)
      (condensedRingObj Λ Y)) := IsDualizable
  let PX : ObjectProperty (Evaluation.D
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (profiniteCoefficient Λ (affineComponentSpace X))) := IsDualizable
  let PY : ObjectProperty (Evaluation.D
      ((coherentTopology Profinite.{u}).over (affineComponentSpace Y))
      (profiniteCoefficient Λ (affineComponentSpace Y))) := IsDualizable
  let F := CY.lift (CX.ι ⋙ (upperStar Λ f).mapDerivedCategory)
    (fun K ↦ s.schemeDuals X Y f K.obj K.property)
  let EX := CX.lift (PX.ι ⋙ (s.corner X).derived (Mon.mk Λ) X)
    (fun K ↦ s.cornerDuals X K.obj K.property)
  let EY := CY.lift (PY.ι ⋙ (s.corner Y).derived (Mon.mk Λ) Y)
    (fun K ↦ s.cornerDuals Y K.obj K.property)
  let H := PY.lift (PX.ι ⋙ (s.slice f).derived (Mon.mk Λ))
    (fun K ↦ s.sliceDuals X Y f K.obj K.property)
  have : EX.IsEquivalence := corner_lisse_equivalence (Mon.mk Λ) X
    (s.corner X) (s.cornerDuals X)
  have : EY.IsEquivalence := corner_lisse_equivalence (Mon.mk Λ) Y
    (s.corner Y) (s.cornerDuals Y)
  have hiso : IsIso (affineComponentMap f) :=
    CompHausLike.isIso_of_bijective _ hh.bijective
  have := slice_modules_equivalence (Mon.mk Λ) (affineComponentMap f) (s.slice f)
  let : ((s.slice f).modules (Mon.mk Λ)).Additive :=
    ComponentDerivedSquare.Slice.modulesAdditive (Mon.mk Λ) (s.slice f)
  let : PreservesFiniteLimits ((s.slice f).modules (Mon.mk Λ)) :=
    ComponentDerivedSquare.Slice.modulesFiniteLimits (Mon.mk Λ) (s.slice f)
  let : PreservesFiniteColimits ((s.slice f).modules (Mon.mk Λ)) :=
    ComponentDerivedSquare.Slice.modulesFiniteColimits (Mon.mk Λ) (s.slice f)
  have : ((s.slice f).derived (Mon.mk Λ)).IsEquivalence := by
    unfold ComponentDerivedSquare.Slice.derived
    infer_instance
  let : ((s.slice f).modules (Mon.mk Λ)).Monoidal := by
    dsimp only [ComponentDerivedSquare.Slice.modules]
    infer_instance
  let : ((s.slice f).derived (Mon.mk Λ)).Monoidal := by
    unfold ComponentDerivedSquare.Slice.derived
    exact (s.sliceTensor f).monoidal
  let : ((s.slice f).derived (Mon.mk Λ)).asEquivalence.functor.Monoidal := by
    change ((s.slice f).derived (Mon.mk Λ)).Monoidal
    unfold ComponentDerivedSquare.Slice.derived
    exact (s.sliceTensor f).monoidal
  obtain ⟨eH, ⟨heH⟩⟩ :=
    dualizable_equivalence ((s.slice f).derived (Mon.mk Λ)).asEquivalence
  have : H.IsEquivalence := lift_equivalence_of_witness _ _ _ _ eH heH
  let a : EX ⋙ F ≅ H ⋙ EY :=
    (CY.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft PX.ι ((s.square f).theta (Mon.mk Λ)) ≪≫
          (Functor.associator _ _ _).symm)
  have : (EX ⋙ F).IsEquivalence := Functor.isEquivalence_of_iso a.symm
  have : F.IsEquivalence := Functor.isEquivalence_of_comp_left EX F
  exact ⟨(condensed_derivedPullback_exact_symmetricMonoidal (Mon.mk Λ) f).1,
    (condensed_derivedPullback_exact_symmetricMonoidal (Mon.mk Λ) f).2,
    F.asEquivalence, ⟨Iso.refl _⟩⟩

/-- Henselian rigidity, including the canonical inverse-image functor on the full
subcategories of dualizable objects.

Source: HRS, Corollary 4.4(1)--(2)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity).

The exact symmetric monoidal clause is `Functor.IsTriangulated` together with a
`Functor.Braided` structure: a strong monoidal structure (invertible unit and tensor
comparisons with their coherence laws) whose tensor comparison commutes with the derived
Koszul braidings `DerivedCategory.braidedCategory'` of source and target. These braidings
are `DerivedMonoidal.braiding'` for `DerivedCategory.Qh` and quasi-isomorphisms, over the
same derived tensor `Mod.derivedMonoidalCategory` as the dualizable subcategories.

Proof:
1. Unique idempotent lifting from
   [lem-weil-pbc-henselian-pair-integral-idempotent-lifting], applied to the integral
   algebra A itself, gives a bijection on idempotents. The dictionary
   [lem-weil-pbc-spec-clopen-idempotent] identifies its map with clopen inverse image.
2. Apply [lem-sfb-spectral-clopen-component-homeomorphism] to obtain the homeomorphism
   on component quotients. Combine it with [lem-zl-henselian-wstrict-local-invariance]:
   w-contractibility consists of w-strict locality and extremal disconnectedness of
   the component space, and the latter is invariant under homeomorphism.
3. Under w-contractibility, take the coherent component System from
   [lem-zl-component-derived-pullback-square]. Apply
   [lem-zl-condensed-component-pullback-compatibility] with each Corner's own continuity,
   tensor and exactness witnesses. Its lisse equivalence uses a coefficient isomorphism
   alpha which need not equal the Corner's coefficient isomorphism c. Restriction of
   scalars along c inverse followed by alpha is an exact monoidal equivalence. The
   restriction-of-scalars composition comparison identifies the Corner functor with
   the evaluation component functor followed by this scalar automorphism. Hence both
   actual Corners induce equivalences on dualizable objects.
4. The component homeomorphism is an isomorphism in Profinite. Slice base change along
   it and its inverse compose to identity. Continuous sheaf pushforward, the slice
   adjunction, module transport, and termwise derivation therefore give an equivalence
   for the slice derived inverse image. Its monoidal structure restricts this to
   dualizable objects.
5. Lift Square.theta through the fully faithful inclusions of dualizable objects.
   Both Corner functors and the slice functor are equivalences; cancellation in this
   square shows that the prescribed scheme inverse image is an equivalence as well.
   It is defined by ObjectProperty.lift, so its inclusion comparison is reflexive.
   [lem-zl-condensed-lisse-proetale-locality] supplies exactness and symmetry for the
   published derived braidings. The preceding explicit scalar comparison definitions
   record its compatibility with constant discrete scalar complexes. -/
theorem henselian_lisse_rigidity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I] :
    IsHomeomorph (PrimeSpectrum.continuous_comap (Ideal.Quotient.mk I)).connectedComponentsMap ∧
      (IsWContractibleRing A ↔ IsWContractibleRing (A ⧸ I)) ∧
      (IsWContractibleRing A →
        (upperStar Λ (Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory.IsTriangulated ∧
        Nonempty (@Functor.Braided _ _ _ (DerivedCategory.braidedCategory' _) _ _ _
          (DerivedCategory.braidedCategory' _)
          (upperStar Λ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory) ∧
        ∃ e :
          (ObjectProperty.FullSubcategory
            (IsDualizable (C := DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
                (condensedRingObj Λ (Spec (.of A))))))) ≌
          (ObjectProperty.FullSubcategory
            (IsDualizable (C := DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (A ⧸ I)))) Ab.{u + 1})
                (condensedRingObj Λ (Spec (.of (A ⧸ I)))))))),
          Nonempty (e.functor ⋙ ObjectProperty.ι _ ≅
            ObjectProperty.ι _ ⋙
              (upperStar Λ (Spec.map
                (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory)) :=
  by
    classical
    have hhome := (isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage
      (PrimeSpectrum.continuous_comap (Ideal.Quotient.mk I)) (henselian_clopens A I)).1
    have hw : IsWContractibleRing A ↔ IsWContractibleRing (A ⧸ I) := by
      constructor
      · intro hA
        let : IsWContractibleRing A := hA
        let : IsWStrictlyLocalRing (A ⧸ I) :=
          (isWStrictlyLocalRing_iff_quotient_of_henselianRing A I).mp
          (inferInstance : IsWStrictlyLocalRing A)
        let : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) :=
          IsWContractibleRing.extremallyDisconnected_connectedComponents
        exact { extremallyDisconnected_connectedComponents :=
          extremallyDisconnected_of_homeo hhome.homeomorph.symm }
      · intro hZ
        let : IsWContractibleRing (A ⧸ I) := hZ
        let : IsWStrictlyLocalRing A :=
          (isWStrictlyLocalRing_iff_quotient_of_henselianRing A I).mpr
          (inferInstance : IsWStrictlyLocalRing (A ⧸ I))
        let : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum (A ⧸ I))) :=
          IsWContractibleRing.extremallyDisconnected_connectedComponents
        exact { extremallyDisconnected_connectedComponents :=
          extremallyDisconnected_of_homeo hhome.homeomorph }
    refine ⟨hhome, hw, ?_⟩
    intro hA
    exact henselian_lisse_equivalence Λ A I hA (hw.mp hA) hhome

end AlgebraicGeometry.ProEtale.CondensedRing
