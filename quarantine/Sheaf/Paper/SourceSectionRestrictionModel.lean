/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.SourceSectionStalkConeData
import Sheaf.Paper.PointAutomorphismDerivedTransportInverse

/-! # Restriction and its normalized descent on point sections

Source: Stacks Tags 0F4F, 05V1 and the point-automorphism inverse theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u a b c d wC wB
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit Functor.mapDerivedCategory

private theorem derivedSectionsComparison
    {C : Type a} {B : Type c} [Category.{b} C] [Category.{d} B] [Abelian C] [Abelian B]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wB} B]
    (F : C ⥤ B) (G : C ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G ⋙ F)
    (N : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso G F).hom.app
        (DerivedCategory.Q.obj N) ≫
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app N) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj N) =
      F.mapDerivedCategoryFactors.hom.app N ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app N) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac G F N
  have hn := Functor.mapDerivedCategoryNatIso_fac e N
  have hid : ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F))
      (.up ℤ)).hom.app N) = 𝟙 _ := by
    ext i
    rfl
  erw [hid, DerivedCategory.Q.map_id, Category.comp_id] at hc
  have hh := (congrArg (fun f ↦ (Functor.mapDerivedCategoryNatIso e).hom.app
    (DerivedCategory.Q.obj N) ≫ f) hc).trans hn
  simpa only [Iso.trans_hom, NatTrans.comp_app, Category.assoc] using hh

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (D : FiniteFieldDatum.{u})

private def transportNatIso {C : Type a} {A : Type c}
    [Category.{b} C] [Ring A] {F F' G G' : C ⥤ ModuleCat.{d} A}
    (hF : F = F') (hG : G = G') (e : F ≅ G) : F' ≅ G' :=
  eqToIso hF.symm ≪≫ e ≪≫ eqToIso hG

private theorem transportNatIso_apply {C : Type a} {A : Type c}
    [Category.{b} C] [Ring A] {F F' G G' : C ⥤ ModuleCat.{d} A}
    (hF : F = F') (hG : G = G') (e : F ≅ G) (M : C)
    (x : F.obj M) (x' : F'.obj M) (hx : HEq x x') :
    HEq ((transportNatIso hF hG e).hom.app M x') (e.hom.app M x) := by
  cases hF
  cases hG
  cases hx
  rfl

private theorem restrictionIso_apply (hl : l ≠ D.p)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (level : Option ℕ)
    (M : SheafOfModules.{u + 1} (pointRestrictionRing l E (Spec (.of D.k)) level))
    (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    ((point_automorphism_sections_inverse l E D hl
      g level).choose).hom.app M x =
      pointRestrictionRaw l E g level M x := by
  have hσ := (point_automorphism_sections_inverse l E D hl
    g level).choose_spec.2.2.1
  exact (congrArg (fun f ↦ f.app M x) hσ).trans
    ((point_automorphism_restriction_natural l E D hl
      g level).2.2.choose_spec.1 M x)

/-- An explicit equation between the two existing section presentations keeps their
large scalar-restriction dictionaries out of subsequent conversion checking. -/
private theorem integralSections_eq_restriction :
    pointRestrictionSections l E D.k none = pointIntegralSections l E D.k := by
  rfl

private theorem integralRestrictionTarget_eq
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    pointRestrictionInverseImage l E g none ⋙
        pointRestrictionSections l E D.k none =
      inverseImageIntegralModules l E g ⋙
        pointIntegralSections l E D.k := by
  exact congrArg
    (fun F ↦ inverseImageIntegralModules l E
      g ⋙ F)
    (integralSections_eq_restriction l E D)

/-- The section isomorphism is fixed by its restriction formula. Its construction
uses explicit equations of functors instead of repeatedly converting their large
scalar-restriction and sheafification dictionaries. -/
@[irreducible] private def integralRestrictionIso (hl : l ≠ D.p)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    pointIntegralSections l E D.k ≅
      inverseImageIntegralModules l E g ⋙
        pointIntegralSections l E D.k :=
  transportNatIso (integralSections_eq_restriction l E D)
    (integralRestrictionTarget_eq l E D g)
    (point_automorphism_sections_inverse l E D hl
      g none).choose

private theorem integralRestrictionIso_apply (hl : l ≠ D.p)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (M : integralTowerModules l E (Spec (.of D.k)))
    (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    HEq ((integralRestrictionIso l E D hl g).hom.app M x)
      (pointRestrictionRaw l E g none M x) := by
  unfold integralRestrictionIso
  have hs := point_automorphism_sections_inverse l E D hl
    g none
  have ht := transportNatIso_apply (integralSections_eq_restriction l E D)
    (integralRestrictionTarget_eq l E D g)
    hs.choose M x x (HEq.rfl)
  exact ht.trans (heq_of_eq (restrictionIso_apply l E D hl
    g none M x))

/-- Restriction is an isomorphism and has the prescribed ordinary derived descent.
Source: Stacks Tags 0F4F and 05V1
(blueprint: lem-trf-source-section-restriction-model).

Proof: use point_automorphism_sections_inverse at completed coefficients. Its
forward section map is the restriction transformation of
point_automorphism_restriction_natural. Derive this section isomorphism using
the small-Hom localization dictionaries of the point fibre. The exact-functor
comparison equations give the required normalization for this derived isomorphism. -/
theorem trfSourceSectionRestrictionModel (hl : l ≠ D.p) (α : D.k ≃+* D.k) :
    ∃ (σ : pointIntegralSections l E D.k ≅
      inverseImageIntegralModules l E (Spec.map (CommRingCat.ofHom α.toRingHom)) ⋙
        pointIntegralSections l E D.k)
      (ρ : pointFibreIntegralAmbient D l E ≅
        inverseImageIntegralDerived l E (Spec.map (CommRingCat.ofHom α.toRingHom)) ⋙
          pointFibreIntegralAmbient D l E),
    (∀ (M : integralTowerModules l E (Spec (.of D.k)))
        (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        HEq (σ.hom.app M x) (pointRestrictionRaw l E
          (Spec.map (CommRingCat.ofHom α.toRingHom)) none M x)) ∧
    (∀ P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
        ρ.hom.app (DerivedCategory.Q.obj P) ≫
            (pointFibreIntegralAmbient D l E).map
              (X := (inverseImageIntegralDerived l E
                (Spec.map (CommRingCat.ofHom α.toRingHom))).obj (DerivedCategory.Q.obj P))
              (Y := DerivedCategory.Q.obj
                (((inverseImageIntegralModules l E
                  (Spec.map (CommRingCat.ofHom α.toRingHom))).mapHomologicalComplex (.up ℤ)).obj P))
              ((inverseImageIntegralModules l E
                (Spec.map (CommRingCat.ofHom α.toRingHom))).mapDerivedCategoryFactors.hom.app P) ≫
            (trfIntegralSectionsFactors l E D).hom.app
              (((inverseImageIntegralModules l E
                (Spec.map (CommRingCat.ofHom α.toRingHom))).mapHomologicalComplex (.up ℤ)).obj P) =
          (trfIntegralSectionsFactors l E D).hom.app P ≫
            (trfIntegralModuleQ l E).map
              (X := ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P)
              (Y := ((inverseImageIntegralModules l E
                (Spec.map (CommRingCat.ofHom α.toRingHom)) ⋙
                  pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P)
              ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P)) := by
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let g := Spec.map (CommRingCat.ofHom α.toRingHom)
  let σ₀ := integralRestrictionIso l E D hl g
  let ρ : pointFibreIntegralAmbient D l E ≅
      inverseImageIntegralDerived l E g ⋙ pointFibreIntegralAmbient D l E :=
    Functor.mapDerivedCategoryNatIso σ₀ ≪≫
      Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
        (pointIntegralSections l E D.k)
  refine ⟨σ₀, ρ, ?_, ?_⟩
  · exact integralRestrictionIso_apply l E D hl g
  · intro P
    exact derivedSectionsComparison (pointIntegralSections l E D.k)
      (inverseImageIntegralModules l E g) σ₀ P

end WeilConjectures
