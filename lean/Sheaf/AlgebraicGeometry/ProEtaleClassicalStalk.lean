/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NR and E4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import Sheaf.RingTheory.IndEtaleStability

/-!
# Classical pro-etale stalks

Source: Stacks Project, Tags 0991 and 0993
(blueprint: lem-cbc-proetale-classical-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Olivier gives a section through the specified field-valued point.
Adapted from the proved etale helper in `StrictlyHenselianOpenSectionsStalk`. -/
private theorem classicalStalk_pointedSection
    {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [WeaklyEtale f]
    (a : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω) ⟶ Spec (.of R))
    (hat : a ≫ f = t) (ht : t default = IsLocalRing.closedPoint R) :
    ∃ σ : Spec (.of R) ⟶ X, σ ≫ f = 𝟙 _ ∧ t ≫ σ = a := by
  obtain ⟨B, j, hj, haj, _⟩ :=
    exists_affine_mem_range_and_range_subset (x := a default) (U := ⊤) (by simp)
  let : IsOpenImmersion j := hj
  let l : Spec (.of Ω) ⟶ Spec B := IsOpenImmersion.lift j a (by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z default] using haj)
  have hl : l ≫ j = a := IsOpenImmersion.lift_fac j a _
  let φ : CommRingCat.of R ⟶ B := Spec.preimage (j ≫ f)
  have hφ : Spec.map φ = j ≫ f := Spec.map_preimage _
  let := φ.hom.toAlgebra
  have hφw : WeaklyEtale (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Algebra.WeaklyEtale R B := weaklyEtale_SpecMap_algebraMap_iff.1 hφw
  let q : PrimeSpectrum B := l default
  have hq : q.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal R := by
    have h : (Spec.map φ) q = IsLocalRing.closedPoint R := by
      rw [hφ]
      change (l ≫ (j ≫ f)) default = _
      rw [← Category.assoc, hl, hat, ht]
    exact congrArg PrimeSpectrum.asIdeal h
  let Bq := Localization.AtPrime q.asIdeal
  have : Algebra.WeaklyEtale R Bq := Algebra.WeaklyEtale.trans R B Bq
  have : IsLocalHom (algebraMap R Bq) := by
    refine ⟨fun z hz ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply R B Bq,
      IsLocalization.AtPrime.isUnit_to_map_iff Bq q.asIdeal] at hz
    by_contra hn
    exact hz (by
      have : z ∈ IsLocalRing.maximalIdeal R := hn
      rw [← hq] at this
      exact this)
  let er : R ≃+* Bq := RingEquiv.ofBijective (algebraMap R Bq)
    (Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := R) (S := Bq))
  let ψ : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (er.symm.toRingHom.comp (algebraMap B Bq))
  have hψ : φ ≫ ψ = 𝟙 _ := by
    ext z
    change er.symm (algebraMap B Bq (algebraMap R B z)) = z
    rw [← IsScalarTower.algebraMap_apply R B Bq]
    exact er.symm_apply_apply z
  let χ : B ⟶ CommRingCat.of Ω := Spec.preimage l
  let θ : CommRingCat.of R ⟶ CommRingCat.of Ω := Spec.preimage t
  have hχ : Spec.map χ = l := Spec.map_preimage _
  have hθ : Spec.map θ = t := Spec.map_preimage _
  have hφχ : φ ≫ χ = θ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ, hφ, hθ, ← Category.assoc, hl, hat]
  have hunit : ∀ z : q.asIdeal.primeCompl, IsUnit (χ.hom z) := by
    intro z
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply z.property
    change z.val ∈ (l default).asIdeal
    rw [← hχ, Spec.map_apply]
    simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, default_asIdeal,
      Ideal.mem_bot] using hz
  let χq : Bq →+* Ω := IsLocalization.lift hunit
  have hχq : χq.comp (algebraMap R Bq) = θ.hom := by
    ext z
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R B Bq,
      IsLocalization.lift_eq]
    exact congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of Ω ↦ m.hom z) hφχ
  have hψθ : ψ ≫ θ = χ := by
    ext z
    change θ.hom (er.symm (algebraMap B Bq z)) = χ.hom z
    rw [← hχq, RingHom.comp_apply]
    change χq (er (er.symm (algebraMap B Bq z))) = _
    rw [er.apply_symm_apply]
    exact IsLocalization.lift_eq hunit z
  refine ⟨Spec.map ψ ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, hψ, Spec.map_id]
  · rw [← hθ, ← Spec.map_comp_assoc, hψθ, hχ, hl]

/-- Base change turns the section construction into a pointed lifting property. -/
private theorem classicalStalk_pointedLift
    {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] {X S : Scheme.{u}}
    (f : X ⟶ S) [WeaklyEtale f]
    (a : Spec (.of Ω) ⟶ X) (b : Spec (.of R) ⟶ S)
    (t : Spec (.of Ω) ⟶ Spec (.of R))
    (hat : a ≫ f = t ≫ b) (ht : t default = IsLocalRing.closedPoint R) :
    ∃ σ : Spec (.of R) ⟶ X, σ ≫ f = b ∧ t ≫ σ = a := by
  let aP := pullback.lift a t hat
  obtain ⟨σ, hσ, htσ⟩ := classicalStalk_pointedSection
    (pullback.snd f b) aP t (by simp [aP]) ht
  refine ⟨σ ≫ pullback.fst f b, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  · rw [← Category.assoc, htσ]
    simp [aP]

/-- Lifting through the weakly etale diagonal forces pointed maps to agree. -/
private theorem classicalStalk_rigidity
    {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] {X S : Scheme.{u}}
    (f : X ⟶ S) [WeaklyEtale f]
    (t : Spec (.of Ω) ⟶ Spec (.of R))
    (ht : t default = IsLocalRing.closedPoint R)
    (a b : Spec (.of R) ⟶ X) (hab : a ≫ f = b ≫ f)
    (hpoint : t ≫ a = t ≫ b) : a = b := by
  let d := pullback.lift a b hab
  have hd : (t ≫ a) ≫ pullback.diagonal f = t ≫ d := by
    apply pullback.hom_ext
    · simp [d]
    · simpa [d] using hpoint
  obtain ⟨σ, hσ, _⟩ := classicalStalk_pointedLift (pullback.diagonal f)
    (t ≫ a) d t hd ht
  have ha := congrArg (fun k ↦ k ≫ pullback.fst f f) hσ
  have hb := congrArg (fun k ↦ k ≫ pullback.snd f f) hσ
  have ha' : σ = a := by simpa [d] using ha
  have hb' : σ = b := by simpa [d] using hb
  exact ha'.symm.trans hb'

/-- The strict-localization map is weakly etale by its affine ind-etale chart. -/
private theorem classicalStalk_weaklyEtale
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T)
    [IsLocalRing (strictHenselizationRing t)]
    (ht : strictHenselizationStructuralMap t
      (IsLocalRing.closedPoint (strictHenselizationRing t)) = t default) :
    WeaklyEtale (strictHenselizationStructuralMap t) := by
  obtain ⟨B, i, hi, hti, _⟩ :=
    exists_affine_mem_range_and_range_subset (x := t default) (U := ⊤) (by simp)
  let : IsOpenImmersion i := hi
  have hrange : Set.range (strictHenselizationStructuralMap t) ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map
      (strictHenselizationStructuralMap t).continuous).mem_open
        (IsOpenImmersion.isOpen_range i) (ht ▸ hti)
  let f := IsOpenImmersion.lift i (strictHenselizationStructuralMap t) hrange
  have hf : f ≫ i = strictHenselizationStructuralMap t :=
    IsOpenImmersion.lift_fac i _ _
  let a := Spec.preimage f
  have ha : Spec.map a = f := Spec.map_preimage _
  have he := smallStrictHenselization_indEtale_of_affine_chart t B i
    (by convert hti using 1; exact congrArg t (Subsingleton.elim _ _))
    (Iso.refl _) a.hom (by
      change Spec.map a ≫ i = 𝟙 _ ≫ strictHenselizationStructuralMap t
      simpa only [ha, Category.id_comp] using hf)
  let := a.hom.toAlgebra
  have hw : a.hom.WeaklyEtale :=
    RingHom.indEtale_principalZariski_stability.2.2.2.2.2.2.1 _ _ a.hom he
  have : Algebra.WeaklyEtale B (strictHenselizationRing t) := hw
  have : WeaklyEtale f := by
    rw [← ha]
    exact (weaklyEtale_SpecMap_algebraMap_iff
      (R := B) (S := strictHenselizationRing t)).2 inferInstance
  rw [← hf]
  infer_instance

/-- Pointed lifts and their uniqueness exhibit the initial neighbourhood. -/
private noncomputable def classicalStalk_initial
    {T : Scheme.{u}} {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (j : Spec (.of R) ⟶ T) [WeaklyEtale j]
    (l : Spec (.of Ω) ⟶ Spec (.of R)) (hl : l ≫ j = t)
    (ht : l default = IsLocalRing.closedPoint R) :
    IsInitial (StructuredArrow.mk (Y := ProEt.mk j) (Over.homMk l hl) :
      ProEtaleGeometricNeighbourhood t) := by
  classical
  let N : ProEtaleGeometricNeighbourhood t :=
    StructuredArrow.mk (Y := ProEt.mk j) (Over.homMk l hl)
  have he (U : ProEtaleGeometricNeighbourhood t) : Nonempty (N ⟶ U) := by
    obtain ⟨σ, hσ, hlσ⟩ := classicalStalk_pointedLift U.right.hom U.hom.left j l
      ((Over.w U.hom).trans hl.symm) ht
    exact ⟨StructuredArrow.homMk (MorphismProperty.Over.homMk σ hσ) (by
      apply Over.OverMorphism.ext
      exact hlσ)⟩
  apply IsInitial.ofUniqueHom (fun U ↦ Classical.choice (he U))
  intro U a
  let b := Classical.choice (he U)
  apply StructuredArrow.hom_ext
  apply MorphismProperty.Over.Hom.ext
  apply classicalStalk_rigidity U.right.hom l ht a.right.left b.right.left
  · exact (MorphismProperty.Over.w a.right).trans
      (MorphismProperty.Over.w b.right).symm
  · have ha : l ≫ a.right.left = U.hom.left :=
      congrArg Over.Hom.left (StructuredArrow.w a)
    have hb : l ≫ b.right.left = U.hom.left :=
      congrArg Over.Hom.left (StructuredArrow.w b)
    exact ha.trans hb.symm

/-- A covering member through the closed point splits, so the sieve contains the identity. -/
private theorem classicalStalk_cover_id
    {T : Scheme.{u}} {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    (j : Spec (.of R) ⟶ T) [WeaklyEtale j]
    {S : Sieve (ProEt.mk j)} (hS : S ∈ ProEt.topology T _) : S (𝟙 _) := by
  obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.1 hS
  obtain ⟨ι, Z, f, rfl⟩ := P.exists_eq_ofArrows
  have hP' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage (Spec (.of R)) := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst, ProEt.mk,
      MorphismProperty.Over.mk] using hP
  have hp := (ofArrows_mem_precoverage_iff _).1
    (propQCPrecoverage_le_precoverage _ hP')
  obtain ⟨i, x, hx⟩ := hp.1 (IsLocalRing.closedPoint R)
  have : WeaklyEtale (f i).left := hp.2 i
  let a := (Z i).left.fromSpecResidueField x
  obtain ⟨σ, hσ, _⟩ := classicalStalk_pointedSection (f i).left a
    (a ≫ (f i).left) rfl (by
      change (f i).left (a default) = IsLocalRing.closedPoint R
      exact (congrArg (f i).left
        (fromSpecResidueField_apply (X := (Z i).left) x default)).trans hx)
  let σ' : ProEt.mk j ⟶ Z i := MorphismProperty.Over.homMk σ (by
    change σ ≫ (Z i).hom = j
    rw [← MorphismProperty.Over.w (f i)]
    change σ ≫ (f i).left ≫ j = j
    rw [← Category.assoc, hσ, Category.id_comp])
  have h := S.downward_closed (hPS _ _ ⟨i⟩) σ'
  convert h using 1
  apply MorphismProperty.Over.Hom.ext
  exact hσ.symm

/-- At this object sheafification preserves sections, hence evaluation preserves colimits. -/
private theorem classicalStalk_abelian_colimits
    {T : Scheme.{u}} {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    (j : Spec (.of R) ⟶ T) [WeaklyEtale j]
    (J : Type) [SmallCategory J] : PreservesColimitsOfShape J
      ((sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj (op (ProEt.mk j))) := by
  let U := op (ProEt.mk j)
  let E := (sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj U
  have hb (G : T.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
      Function.Bijective ((toSheafify (ProEt.topology T) G).app U) := by
    refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
    · have hh := classicalStalk_cover_id j
        (Presheaf.equalizerSieve_mem (ProEt.topology T) (toSheafify _ G) x y hxy)
      change G.map (𝟙 U) x = G.map (𝟙 U) y at hh
      simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hh
    · obtain ⟨t, ht⟩ := classicalStalk_cover_id j
        (Presheaf.imageSieve_mem (ProEt.topology T) (toSheafify _ G) s)
      change (toSheafify (ProEt.topology T) G).app U t =
        (sheafify (ProEt.topology T) G).map (𝟙 U) s at ht
      rw [CategoryTheory.Functor.map_id] at ht
      exact ⟨t, ht⟩
  have (G : T.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : IsIso ((Functor.whiskerRight
      (sheafificationAdjunction (ProEt.topology T) AddCommGrpCat.{u + 1}).unit
      ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj U)).app G) :=
    (isIso_iff_of_reflects_iso _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).1
      ((isIso_iff_bijective _).2 (hb G))
  have : IsIso (Functor.whiskerRight
      (sheafificationAdjunction (ProEt.topology T) AddCommGrpCat.{u + 1}).unit
      ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj U)) := NatIso.isIso_of_isIso_app _
  have : PreservesColimitsOfShape J
      (presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙ E) :=
    preservesColimitsOfShape_of_natIso (asIso (Functor.whiskerRight
      (sheafificationAdjunction (ProEt.topology T) AddCommGrpCat.{u + 1}).unit
      ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj U)))
  exact (sheafificationAdjunction (ProEt.topology T) AddCommGrpCat.{u + 1})
    |>.preservesColimitsOfShape_of_comp E J

/-- The strict localization is a pro-etale neighbourhood; its canonical colimit
coprojection is an isomorphism naturally in set-valued and abelian sheaves.
The abelian stalk functor preserves finite limits and finite colimits.
Source: Stacks Project, Tags 0991 and 0993
(blueprint: lem-cbc-proetale-classical-stalk).

Proof: Choose the canonical residue-field identification from
`strictHenselizationResidue`, giving the marked closed point of the strict localization.
Its structural map factors through an affine open through the image point; the
chart map is ind-etale, hence weakly etale, so the structural map is weakly etale.
For a weakly etale morphism over a strictly henselian local spectrum, choose an
affine chart at the marked point and localize its ring at that prime. Olivier's
theorem makes the resulting local ring map bijective. Its inverse defines a section;
the marked field map extends to the localization, so this section preserves the
whole geometric point. Base change gives pointed lifts over arbitrary bases.
Apply this lifting result to the weakly etale diagonal to prove uniqueness of
pointed lifts. Thus the strict localization is initial among pointed neighbourhoods.
Its opposite is terminal, making the specified canonical colimit leg an isomorphism
for any coefficient category, naturally in the sheaf.
Every covering sieve on the strict localization contains the identity: a covering
family has a point above its closed point, and the same section construction with
that point's residue field splits a member. Consequently local injectivity and
surjectivity of the sheafification unit give a bijection on sections there. Evaluation
therefore commutes with sheafification. The reflective sheafification adjunction
and pointwise presheaf colimits imply preservation of finite colimits. Limits of
sheaves are computed sectionwise. Transfer both preservation properties through
the canonical abelian evaluation-to-stalk isomorphism. -/
theorem proEtale_classical_stalk
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    ∃ (h : WeaklyEtale (strictHenselizationStructuralMap t))
      (l : Spec (.of Ω) ⟶ strictHenselizationScheme t)
      (hl : l ≫ strictHenselizationStructuralMap t = t),
      IsIso (Functor.whiskerLeft (sheafToPresheaf (ProEt.topology T) (Type (u + 1)))
        (Functor.whiskerLeft
          ((Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
            (Type (u + 1))).obj (proEtaleGeometricNeighbourhoodForget t).op)
          (colim.ι (op (StructuredArrow.mk
            (Y := @ProEt.mk T _ (strictHenselizationStructuralMap t) h)
                  (Over.homMk l hl)))))) ∧
      IsIso (Functor.whiskerLeft (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1})
        (Functor.whiskerLeft
          ((Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
            AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget t).op)
          (colim.ι (op (StructuredArrow.mk
            (Y := @ProEt.mk T _ (strictHenselizationStructuralMap t) h)
                  (Over.homMk l hl)))))) ∧
      PreservesFiniteLimits
        (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
          (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
            AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim) ∧
      PreservesFiniteColimits
        (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
          (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
            AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim) := by
  classical
  let : Algebra (T.residueField (t (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo t)).hom.toAlgebra
  obtain ⟨hlocal, hstrict, hclosed, _, σ, ⟨_, hl⟩, _⟩ :=
    strictHenselizationResidue t rfl
  let := hlocal
  let := hstrict
  let β : strictHenselizationRing t →+* Ω :=
    (((IntermediateField.val
      (separableClosure (T.residueField (t (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        σ.toRingHom).comp (IsLocalRing.residue (strictHenselizationRing t)))
  let l : Spec (.of Ω) ⟶ strictHenselizationScheme t := Spec.map (CommRingCat.ofHom β)
  have hβ : IsLocalHom β := by dsimp [β]; infer_instance
  have ht : l default = IsLocalRing.closedPoint (strictHenselizationRing t) := by
    have hb : l (IsLocalRing.closedPoint Ω) =
        IsLocalRing.closedPoint (strictHenselizationRing t) :=
      IsLocalRing.comap_closedPoint β
    exact (congrArg l (Subsingleton.elim _ _)).trans hb
  have hj : WeaklyEtale (strictHenselizationStructuralMap t) :=
    classicalStalk_weaklyEtale t (by
      exact hclosed.trans (congrArg t (Subsingleton.elim _ _)))
  let N : ProEtaleGeometricNeighbourhood t :=
    StructuredArrow.mk (Y := @ProEt.mk T _ (strictHenselizationStructuralMap t) hj)
      (Over.homMk l hl)
  have hN : IsInitial N := classicalStalk_initial (R := strictHenselizationRing t) t
    (strictHenselizationStructuralMap t) l hl ht
  have hι (C : Type (u + 2)) [Category.{u + 1} C]
      [HasColimitsOfSize.{u + 1, u + 1} C] : IsIso (colim.ι (C := C) (op N)) := by
    have (F : (ProEtaleGeometricNeighbourhood t)ᵒᵖ ⥤ C) :
        IsIso ((colim.ι (C := C) (op N)).app F) :=
      (colimit.isColimit F).isIso_ι_app_of_isTerminal _ hN.op
    exact NatIso.isIso_of_isIso_app _
  have := hι (Type (u + 1))
  have := hι AddCommGrpCat.{u + 1}
  let E := (sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj
    (op (@ProEt.mk T _ (strictHenselizationStructuralMap t) hj))
  let K := sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
      AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim
  let α : E ⟶ K := Functor.whiskerLeft
    (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1})
    (Functor.whiskerLeft
      ((Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
        AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget t).op)
      (colim.ι (op N)))
  have : IsIso α := inferInstance
  have hElim : PreservesFiniteLimits E := by
    change PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ _).obj _)
    infer_instance
  have hEcol : PreservesFiniteColimits E :=
    ⟨fun J _ _ ↦ classicalStalk_abelian_colimits (R := strictHenselizationRing t)
      (strictHenselizationStructuralMap t) J⟩
  exact ⟨hj, l, hl, inferInstance, inferInstance,
    preservesFiniteLimits_of_natIso (asIso α),
    preservesFiniteColimits_of_natIso (asIso α)⟩

end AlgebraicGeometry.Scheme
