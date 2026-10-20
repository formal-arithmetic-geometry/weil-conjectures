/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Naturality of the supported Hom identification under base change

Source: literature/stacks-project/etale-cohomology.tex, Tag 0A45,
lemma-cohomology-with-support-triangle;
blueprint sec-smooth-purity/sk-prop-sf-cbc
(blueprint: lem-asd-supported-kummer-support-hom-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true

universe w v u v' u' v'' u'' v₀ u₀

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor ZeroObject

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections

/-- The standard resolution functor and its unit, packaged before site specialization.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomResolutionData (C : Type u') [Category.{v'} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] where
  R : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  unit : 𝟭 (CochainComplex C ℤ) ⟶ R
  isKInjective : ∀ K, (R.obj K).IsKInjective
  unitMonoQuasiIso : ∀ K, HomologicalComplex.monoQuasiIso C (.up ℤ) (unit.app K)
  isFibrant : ∀ K, (HomologicalComplex.monoQuasiIso C (.up ℤ)).rlp
    (0 : R.obj K ⟶ (0 : CochainComplex C ℤ))

/-- Package the existing functorial resolution, without changing its chosen objects.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomResolutionData (C : Type u') [Category.{v'} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] : SupportedHomResolutionData C where
  R := CochainComplex.kInjectiveResolutionFunctor C
  unit := CochainComplex.toKInjectiveResolution C
  isKInjective := fun _ ↦ inferInstance
  unitMonoQuasiIso := CochainComplex.monoQuasiIso_toKInjectiveResolution_app C
  isFibrant := by
    intro K
    let d := MorphismProperty.functorialFactorizationData
      (HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ)).rlp
    have hp := d.hp ((CochainComplex.toArrowZero C).obj K)
    have he : d.p.app ((CochainComplex.toArrowZero C).obj K) = 0 :=
      (isZero_zero (CochainComplex C ℤ)).eq_of_tgt _ _
    rw [he] at hp
    exact hp

namespace CategoryTheory.Functor

/-- The canonical comparison from a derived functor to its functorial resolution model.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomResolutionMap
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {B : Type u} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{v} B]
    (F : C ⥤ B) [F.Additive] (K : CochainComplex C ℤ) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((supportedHomResolutionData C).R.obj K)) := by
  letI := (supportedHomResolutionData C).isKInjective K
  exact F.rightDerivedFunctor.map
      (DerivedCategory.Q.map ((supportedHomResolutionData C).unit.app K)) ≫
    (F.rightDerivedFunctorObjQIso ((supportedHomResolutionData C).R.obj K)).hom

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 200000] closedSupportEtaleAbelian
attribute [local instance 200000] closedSupportEtaleLinear

/-- The Grothendieck property for the same fixed abelian structure.
Source: Stacks, Tag 03DA (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
theorem supportedEtaleGrothendieck (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

attribute [local instance 200000] supportedEtaleGrothendieck


/-- The fixed functorial resolution on the etale site.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedResolutionFunctor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedHomResolutionData (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).R

/-- The resolution unit, with its target functor fixed explicitly.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedResolutionUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    𝟭 (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) ⟶
      supportedResolutionFunctor A T :=
  (supportedHomResolutionData (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).unit

/-- Functorial degreewise-injective K-injective replacement, on the specified etale site.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedResolution (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedResolutionFunctor A T).obj K

/-- The functor of complexes of Hom from the closed constant sheaf.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomComplexFunctor (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :=
  (closedSupportHomFunctor A i).mapHomologicalComplex (.up ℤ)

/-- The derived Hom functor on complexes, with its model fixed before specialization.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomDerivedFunctor (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
  DerivedCategory.Q ⋙ (closedSupportHomFunctor A i).rightDerivedFunctor

/-- The global-section functor on complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedSectionsComplexFunctor (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :=
  (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The open-section functor on complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedOpenSectionsComplexFunctor (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) :=
  (upperStar (ModuleCat.{u + 1} A) v ⋙
    Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise ordinary Hom from the closed constant sheaf. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomComplex (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  (supportedHomComplexFunctor A i).obj I

/-- The derived Hom object of the recorded closed-support theorem. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomObject (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
  (supportedHomDerivedFunctor A i).obj K

/-- Evaluation at 1 identifies a map from the rank-one constant sheaf with a global section.
Use the constant-sheaf adjunction and the published terminal-section/global-section iso.
Source: Stacks, Tag 095L (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedEvaluateSection (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (c : ordinaryFiniteConstant A T ⟶ F) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj F :=
  rankOneSectionsEquiv A T F c

/-- Termwise inverse image as a fixed functor on complexes.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedPullbackComplexFunctor (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (upperStar (ModuleCat.{u + 1} A) h).mapHomologicalComplex (.up ℤ)

/-- The inverse image of a complex is taken termwise; exactness makes this derived pullback.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedPullbackComplex (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedPullbackComplexFunctor A h).obj K


/-- The normalized cone model, with its complex functors supplied as parameters.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomDiagram (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀]
    (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] where
  R : C ⥤ C
  F : C ⥤ CochainComplex B₀ ℤ
  E : C ⥤ CochainComplex B₀ ℤ
  B : C ⥤ CochainComplex B₀ ℤ
  H : C ⥤ D₀
  modelMap : ∀ K, H.obj K ⟶ Q₀.obj (F.obj (R.obj K))
  restriction : ∀ I n, (E.obj I).X n ⟶ (B.obj I).X n
  normalization : ∀ I, (F.obj I ⟶ E.obj I) → Prop

/-- A normalized cone model of a fixed diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomConeModelCore (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀]
    (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C]
    (d : SupportedHomDiagram B₀ D₀ Q₀ C) where
  q : d.E ⟶ d.B
  q_spec : ∀ I n, (q.app I).f n = d.restriction I n
  modelIso : ∀ K, d.H.obj K ≅ Q₀.obj (d.F.obj (d.R.obj K))
  modelIso_spec : ∀ K, (modelIso K).hom = d.modelMap K
  toSections : ∀ K, d.F.obj (d.R.obj K) ⟶ d.E.obj (d.R.obj K)
  toSections_spec : ∀ K, d.normalization (d.R.obj K) (toSections K)
  inclusion : ∀ K, d.F.obj (d.R.obj K) ⟶
    (CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧
  inclusion_fst : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n),
    (inclusion K).f n ≫ (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (q.app (d.R.obj K)) m n hn =
        (toSections K).f n
  inclusion_snd : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)),
    (inclusion K).f n ≫ (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.sndX (q.app (d.R.obj K)) m = 0
  comparison : ∀ K, d.H.obj K ≅
    Q₀.obj ((CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧)
  comparison_spec : ∀ K, (comparison K).hom =
    (modelIso K).hom ≫ Q₀.map (inclusion K)
  comparison_naturality : ∀ (K L : C) (f : K ⟶ L),
    d.H.map f ≫ (comparison L).hom =
      (comparison K).hom ≫ Q₀.map
        ((shiftFunctor (CochainComplex (B₀) ℤ) (-1 : ℤ)).map
          (CochainComplex.mappingCone.map _ _ (d.E.map (d.R.map f)) (d.B.map (d.R.map f))
            (q.naturality (d.R.map f)).symm))
  projection : ∀ K, (CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧ ⟶ d.E.obj (d.R.obj K)
  projection_spec : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n),
    (projection K).f n = (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (q.app (d.R.obj K)) m n hn

/-- Transport a map through the two fixed derived models.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev SupportedHomConeModelCore.transport
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C]
    {d : SupportedHomDiagram B₀ D₀ Q₀ C}
    {C' : Type u''} [Category.{v''} C']
    {d' : SupportedHomDiagram B₀ D₀ Q₀ C'}
    (M : SupportedHomConeModelCore B₀ D₀ Q₀ C d)
    (M' : SupportedHomConeModelCore B₀ D₀ Q₀ C' d')
    (K : C) (K' : C') (f : d.F.obj (d.R.obj K) ⟶ d'.F.obj (d'.R.obj K')) :
    d.H.obj K ⟶ d'.H.obj K' :=
  (M.modelIso K).hom ≫ Q₀.map f ≫ (M'.modelIso K').inv

/-- Evaluation normalization on a chosen resolution, with its complex functors fixed.
Source: Stacks, Tag 095L (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedHomSectionNormalization (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (t : (supportedHomComplexFunctor A i).obj I ⟶
      (supportedSectionsComplexFunctor A T).obj I) : Prop :=
  t = (NatTrans.mapHomologicalComplex (closedSupportHomToSections A i) (.up ℤ)).app I

/-- Equality with the canonical map is exactly the original evaluation normalization.
Source: Stacks, Tags 095L, 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality).

Evaluate the canonical map componentwise for the forward implication. Conversely, equality
on every element gives equality of the module maps in each degree and hence of chain maps. -/
theorem supportedHomSectionNormalization_iff (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (t : (supportedHomComplexFunctor A i).obj I ⟶
      (supportedSectionsComplexFunctor A T).obj I) :
    supportedHomSectionNormalization A i I t ↔
      ∀ (n : ℤ) (c : (closedSupportHomSource A i) ⟶ I.X n),
        (t.f n) c = supportedEvaluateSection A T (I.X n) (supportedConstantUnit A i ≫ c) := by
  have hc (n : ℤ) (c : (closedSupportHomSource A i) ⟶ I.X n) :
      (((NatTrans.mapHomologicalComplex (closedSupportHomToSections A i) (.up ℤ)).app I).f n)
        c = supportedEvaluateSection A T (I.X n) (supportedConstantUnit A i ≫ c) := by
    change (closedSupportHomToSections A i).app (I.X n) c = _
    simpa only [supportedEvaluateSection, supportedConstantUnit, ordinaryFiniteConstant] using
      (closedSupportHomToSections_apply A i (I.X n) c)
  constructor
  · intro h n c
    change t = _ at h
    rw [h]
    exact hc n c
  · intro h
    change t = _
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (h n c).trans (hc n c).symm

/-- Build the resolution and section diagram before specifying a concrete sheaf category.
Source: Stacks, Tags 070K, 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomDiagramFactory
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {D : Type u} [Category.{v} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{v} D]
    (F E B : C ⥤ D) [F.Additive] [E.PreservesZeroMorphisms] [B.PreservesZeroMorphisms]
    (restriction : ∀ (I : CochainComplex C ℤ) n,
      ((E.mapHomologicalComplex (.up ℤ)).obj I).X n ⟶
        ((B.mapHomologicalComplex (.up ℤ)).obj I).X n)
    (α : F ⟶ E) :
    SupportedHomDiagram D (DerivedCategory.{v} D) DerivedCategory.Q (CochainComplex C ℤ) where
  R := (supportedHomResolutionData C).R
  F := F.mapHomologicalComplex (.up ℤ)
  E := E.mapHomologicalComplex (.up ℤ)
  B := B.mapHomologicalComplex (.up ℤ)
  H := DerivedCategory.Q ⋙ F.rightDerivedFunctor
  modelMap := CategoryTheory.Functor.supportedHomResolutionMap F
  restriction := restriction
  normalization := fun I t ↦
    t = (NatTrans.mapHomologicalComplex α (.up ℤ)).app I

/-- The functors and normalization maps defining the supported-Hom diagram.
Source: Stacks, Tags 070K, 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomDiagram (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) (v : V ⟶ T) :
    SupportedHomDiagram (ModuleCat.{u + 1} A)
      (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
      (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  supportedHomDiagramFactory
    (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := ModuleCat.{u + 1} A) (closedSupportHomFunctor A i)
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (fun I n ↦ (closedSupportSectionsPullback A v).app (I.X n))
    (closedSupportHomToSections A i)

/-- The etale specialization of the normalized supported-Hom cone model.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev SupportedHomConeModel (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) (v : V ⟶ T) :=
  SupportedHomConeModelCore (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
    (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (supportedHomDiagram A i v)

/-- The relative object uses the actual shifted restriction cone. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedRelativeObject (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} {i : D ⟶ T} {v : V ⟶ T} (M : SupportedHomConeModel A i v)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
  DerivedCategory.Q.obj
    ((CochainComplex.mappingCone (M.q.app (supportedResolution A T K)))⟦(-1 : ℤ)⟧)

/-- The normalized supported-Hom identification on cohomology. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomIdentification (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} {i : D ⟶ T} {v : V ⟶ T} (M : SupportedHomConeModel A i v)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (n : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).mapIso (M.comparison K).symm

/-- The condition that a resolution comparison extends the resolution unit.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedResolutionComparisonCondition (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h (supportedResolution A T K) ⟶
      supportedResolution A T' (supportedPullbackComplex A h K)) : Prop :=
  (supportedPullbackComplexFunctor A h).map
    ((supportedResolutionUnit A T).app K) ≫ a =
      (supportedResolutionUnit A T').app (supportedPullbackComplex A h K)

/-- The degreewise formula for pullback of sections along a comparison of complexes.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedSectionsMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (s : (supportedSectionsComplexFunctor A T).obj I ⟶
      (supportedSectionsComplexFunctor A T').obj J) : Prop :=
  ∀ n, s.f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h (I.X n) ≫
    (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).map (a.f n)

/-- The degreewise formula for the open part of a pullback square.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedOpenSectionsMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T V' V : Scheme.{u}} (h : T' ⟶ T) (v : V ⟶ T) (v' : V' ⟶ T')
    (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (b : (supportedOpenSectionsComplexFunctor A v).obj I ⟶
      (supportedOpenSectionsComplexFunctor A v').obj J) : Prop :=
  ∀ n, b.f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) hV
    ((upperStar (ModuleCat.{u + 1} A) v).obj (I.X n)) ≫
      (Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStarComp (ModuleCat.{u + 1} A) hV v).inv.app _ ≫
          (upperStarComp (ModuleCat.{u + 1} A) v' h (hV ≫ v) sqV.w).hom.app _ ≫
          (upperStar (ModuleCat.{u + 1} A) v').map (a.f n))

/-- The degreewise formula for inverse-image and precomposition on Hom complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedHomMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i)))
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (f : supportedHomComplex A i I ⟶ supportedHomComplex A i' J) : Prop :=
  ∀ (n : ℤ) (c : (closedSupportHomSource A i) ⟶ I.X n),
    (f.f n) c = e ≫ (upperStar (ModuleCat.{u + 1} A) h).map c ≫ a.f n

/-- Pullback maps with the source complexes and their functors left abstract.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomPullbackDiagram
    (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀] (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] (C' : Type u'') [Category.{v''} C'] where
  source : SupportedHomDiagram B₀ D₀ Q₀ C
  target : SupportedHomDiagram B₀ D₀ Q₀ C'
  P : C ⥤ C'
  unitSpec : ∀ K, (P.obj (source.R.obj K) ⟶ target.R.obj (P.obj K)) → Prop
  sectionsSpec : ∀ I J, (P.obj I ⟶ J) → (source.E.obj I ⟶ target.E.obj J) → Prop
  openSpec : ∀ I J, (P.obj I ⟶ J) → (source.B.obj I ⟶ target.B.obj J) → Prop
  homSpec : ∀ I J, (P.obj I ⟶ J) → (source.F.obj I ⟶ target.F.obj J) → Prop

/-- Normalized representative maps for a fixed pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomPullbackMaps
    (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀] (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] (C' : Type u'') [Category.{v''} C']
    (d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C') where
  sourceModel : SupportedHomConeModelCore B₀ D₀ Q₀ C d.source
  targetModel : SupportedHomConeModelCore B₀ D₀ Q₀ C' d.target
  resolutionComparison : ∀ K, d.P.obj (d.source.R.obj K) ⟶ d.target.R.obj (d.P.obj K)
  resolutionComparison_spec : ∀ K, d.unitSpec K (resolutionComparison K)
  sectionsMap : ∀ K, d.source.E.obj (d.source.R.obj K) ⟶ d.target.E.obj (d.target.R.obj (d.P.obj K))
  sectionsMap_spec : ∀ K, d.sectionsSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (sectionsMap K)
  openSectionsMap : ∀ K, d.source.B.obj (d.source.R.obj K) ⟶
    d.target.B.obj (d.target.R.obj (d.P.obj K))
  openSectionsMap_spec : ∀ K, d.openSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (openSectionsMap K)
  restriction_square : ∀ K, sectionsMap K ≫ targetModel.q.app (d.target.R.obj (d.P.obj K)) =
    sourceModel.q.app (d.source.R.obj K) ≫ openSectionsMap K
  homMap : ∀ K, d.source.F.obj (d.source.R.obj K) ⟶ d.target.F.obj (d.target.R.obj (d.P.obj K))
  homMap_spec : ∀ K, d.homSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (homMap K)

/-- Hom transport through normalized models of an abstract pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def SupportedHomPullbackMaps.homPullback
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀] {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'} (N : SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d)
    (K : C) :=
  SupportedHomConeModelCore.transport N.sourceModel N.targetModel K (d.P.obj K) (N.homMap K)

/-- The diagonal cone map of an abstract pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def SupportedHomPullbackMaps.relativePullback
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀] {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'} (N : SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d)
    (K : C) :=
  Q₀.map ((shiftFunctor (CochainComplex B₀ ℤ) (-1 : ℤ)).map
    (CochainComplex.mappingCone.map _ _ (N.sectionsMap K) (N.openSectionsMap K)
      (N.restriction_square K).symm))

/-- The specialization of the representative-map record to an etale pullback square.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomPullbackDiagram (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (v : V ⟶ T) (v' : V' ⟶ T') (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i))) :
  SupportedHomPullbackDiagram (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
    (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) where
  source := supportedHomDiagram A i v
  target := supportedHomDiagram A i' v'
  P := supportedPullbackComplexFunctor A h
  unitSpec := supportedResolutionComparisonCondition A h
  sectionsSpec := supportedSectionsMapCondition A h
  openSpec := supportedOpenSectionsMapCondition A h v v' hV sqV
  homSpec := supportedHomMapCondition A h i i' e

/-- The type of normalized maps on the fixed etale pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev supportedHomPullbackMapsType (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (v : V ⟶ T) (v' : V' ⟶ T') (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i))) :=
  SupportedHomPullbackMaps (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
    (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (supportedHomPullbackDiagram A h i i' v v' hV sqV e)

/-- The canonical representative maps for pullback of a closed/open pair. A resolution
comparison must extend the pulled-back resolution unit. Its section maps and Hom map are
specified degreewise; the relative pullback is then the diagonal mapping-cone map.
Source: Stacks, Tag 0A45 and blueprint lem-amb-cartier-kummer-map, penultimate paragraph
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedKummerSupportHomData (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T)
    (i' : D' ⟶ T') (hD : D' ⟶ D) (v : V ⟶ T) (v' : V' ⟶ T')
    (sqD : IsPullback hD i' i h) (hV : V' ⟶ V) (sqV : IsPullback hV v' v h) where
  exchange_isIso : IsIso (supportedConstantExchange A i i' h hD sqD.toCommSq)
  exchangeInverse : (closedSupportHomSource A i') ⟶
    (upperStar (ModuleCat.{u + 1} A) h).obj
      ((closedSupportHomSource A i))
  exchange_hom_inv : supportedConstantExchange A i i' h hD sqD.toCommSq ≫ exchangeInverse = 𝟙 _
  exchange_inv_hom : exchangeInverse ≫ supportedConstantExchange A i i' h hD sqD.toCommSq = 𝟙 _
  maps : supportedHomPullbackMapsType A h i i' v v' hV sqV exchangeInverse

namespace SupportedKummerSupportHomData

variable {A : Type (u + 1)} [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}

/-- The source normalized cone model.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev sourceModel
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) := N.maps.sourceModel

/-- The target normalized cone model.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev targetModel
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) := N.maps.targetModel

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def resolutionComparison
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.resolutionComparison

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev resolutionComparison_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.resolutionComparison_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def sectionsMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.sectionsMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev sectionsMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.sectionsMap_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def openSectionsMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.openSectionsMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev openSectionsMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.openSectionsMap_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev restriction_square
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.restriction_square

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def homMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.homMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev homMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.homMap_spec

end SupportedKummerSupportHomData

/-- Actual relative pullback: apply localization and cohomology to the shifted diagonal
cone map, whose two components have specified section formulas. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedRelativePullback (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  N.maps.relativePullback K

/-- Actual Hom pullback: pull a representative back and precompose with the inverse of
closed exchange, then transport through the specified resolution-model isomorphisms.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomPullback (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  N.maps.homPullback K


set_option backward.isDefEq.respectTransparency false

private noncomputable def supportedConeProjection
    {C : Type u'} [Category.{v'} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (q : P ⟶ Q) :
    (CochainComplex.mappingCone q)⟦(-1 : ℤ)⟧ ⟶ P :=
  CochainComplex.mappingCocone.fst q

private lemma supportedConeProjection_f
    {C : Type u'} [Category.{v'} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (q : P ⟶ Q)
    (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n) :
    (supportedConeProjection q).f n =
      (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
        HomologicalComplex.homotopyCofiber.fstX q m n hn := by
  subst m
  simp [supportedConeProjection, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cochain.leftShift,
    CochainComplex.mappingCone.fst]

attribute [local irreducible] CategoryTheory.Functor.closedSupport_resolutionIso

private theorem supportedConeModelCore
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {D : Type u} [Category.{v} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{v} D]
    (F E B : C ⥤ D) [F.Additive] [E.Additive] [B.Additive]
    (restriction : ∀ (I : CochainComplex C ℤ) n,
      ((E.mapHomologicalComplex (.up ℤ)).obj I).X n ⟶
        ((B.mapHomologicalComplex (.up ℤ)).obj I).X n)
    (τ : E ⟶ B) (hτ : ∀ I n, τ.app (I.X n) = restriction I n)
    (α : F ⟶ E) (hzero : ∀ J, α.app J ≫ τ.app J = 0)
    (hExact : ∀ (J : C), Injective J →
      (ShortComplex.mk (α.app J) (τ.app J) (hzero J)).ShortExact)
    :
    Nonempty (SupportedHomConeModelCore D (DerivedCategory.{v} D) DerivedCategory.Q
      (CochainComplex C ℤ) (supportedHomDiagramFactory F E B restriction
        α)) := by
  classical
  let q := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
  let a := NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)
  have hz (I : CochainComplex C ℤ) : a.app I ≫ q.app I = 0 := by
    ext n : 1
    exact hzero (I.X n)
  let R := CochainComplex.kInjectiveResolutionFunctor C
  let κ K := CochainComplex.closedConeLift (q.app (R.obj K)) (a.app (R.obj K)) (hz _)
  have hκ K : QuasiIso (κ K) := by
    apply CochainComplex.closedConeLift_quasiIso
      (ShortComplex.mk (a.app (R.obj K)) (q.app (R.obj K)) (hz _))
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact hExact ((R.obj K).X n) inferInstance
  let e (K : CochainComplex C ℤ) :
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (R.obj K)) :=
    CategoryTheory.Functor.closedSupport_resolutionIso F K
  let c K := e K ≪≫ asIso (DerivedCategory.Q.map (κ K))
  refine ⟨{
      q := q
      q_spec := hτ
      modelIso := e
      modelIso_spec := by
        intro K
        dsimp only [e]
        unfold CategoryTheory.Functor.closedSupport_resolutionIso
        rfl
      toSections := fun K ↦ a.app (R.obj K)
      toSections_spec := fun K ↦ rfl
      inclusion := κ
      inclusion_fst := ?_
      inclusion_snd := ?_
      comparison := c
      comparison_spec := fun _ ↦ rfl
      comparison_naturality := ?_
      projection := fun K ↦ supportedConeProjection (q.app (R.obj K))
      projection_spec := ?_ }⟩
  · intro K n m hm hn
    exact (CochainComplex.closedConeLift_projections _ _ _ n m hm).2
  · intro K n m hm
    exact (CochainComplex.closedConeLift_projections _ _ _ n m hm).1
  · intro K L f
    dsimp only [c, Iso.trans_hom, asIso_hom, supportedHomDiagramFactory,
      supportedHomResolutionData,
      Functor.comp_map]
    rw [← Category.assoc, CategoryTheory.Functor.closedSupport_resolutionIso_naturality]
    simp only [Category.assoc]
    apply congrArg (fun t ↦ (e K).hom ≫ t)
    have hn := CochainComplex.closedConeLift_naturality
      (q.app (R.obj K)) (q.app (R.obj L)) (a.app (R.obj K)) (a.app (R.obj L))
      (hz (R.obj K)) (hz (R.obj L))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.map f))
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.map f))
      ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map (R.map f))
      (a.naturality (R.map f)) (q.naturality (R.map f))
    let QD := DerivedCategory.Q.{v, v, u} (C := D)
    simpa only [Functor.map_comp] using congrArg (fun t ↦ QD.map t) hn
  · intro K n m hm hn
    exact supportedConeProjection_f _ n m hm hn

private theorem supportedConeModel (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ) :
    Nonempty (SupportedHomConeModel A i v) := by
  classical
  let E := Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let B := upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)
  let F := closedSupportHomFunctor A i
  have : E.Additive := (constantSheafΓAdj T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).right_adjoint_additive
  have : (Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).Additive :=
    (constantSheafΓAdj V.smallEtaleTopology
      (ModuleCat.{u + 1} A)).right_adjoint_additive
  let τ : E ⟶ B := closedSupportSectionsPullback A v
  have hzero := closedSupportHomToSections_comp A i v hcomp τ (fun _ ↦ rfl)
  have hExact := closedSupportHomSequence_shortExact A i v hcomp τ (fun _ ↦ rfl)
  change Nonempty (SupportedHomConeModelCore (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q _ _)
  exact supportedConeModelCore
    (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := ModuleCat.{u + 1} A) F E B
    (fun I n ↦ (closedSupportSectionsPullback A v).app (I.X n))
    τ (fun _ _ ↦ rfl) (closedSupportHomToSections A i) hzero hExact

private theorem supportedInclusionProjection
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C]
    {d : SupportedHomDiagram B₀ D₀ Q₀ C}
    (M : SupportedHomConeModelCore B₀ D₀ Q₀ C d) (K : C) :
    M.inclusion K ≫ M.projection K = M.toSections K := by
  ext n : 1
  rw [HomologicalComplex.comp_f, M.projection_spec K n (n + (-1)) rfl (by omega)]
  exact M.inclusion_fst K n (n + (-1)) rfl (by omega)

private theorem supportedForget
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C]
    {d : SupportedHomDiagram B₀ D₀ Q₀ C}
    {E : Type u''} [Category.{v''} E]
    (M : SupportedHomConeModelCore B₀ D₀ Q₀ C d) (H : D₀ ⥤ E) (K : C) :
    H.map (Q₀.map (M.projection K)) = H.map (M.comparison K).inv ≫
      H.map ((M.modelIso K).hom ≫ Q₀.map (M.toSections K)) := by
  apply (cancel_epi (H.map (M.comparison K).hom)).mp
  rw [← H.map_comp, ← Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id,
    Category.id_comp, M.comparison_spec, Category.assoc, ← Q₀.map_comp,
    supportedInclusionProjection]

private noncomputable def supportedResolutionLift
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {X Y : CochainComplex C ℤ} (Z : CochainComplex C ℤ)
    (f : X ⟶ Y) [Mono f] [QuasiIso f]
    (g : X ⟶ (supportedHomResolutionData C).R.obj Z) :
    {a : Y ⟶ (supportedHomResolutionData C).R.obj Z // f ≫ a = g} := by
  classical
  have hf : HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ) f :=
    ⟨inferInstance, (show QuasiIso f from inferInstance)⟩
  let sq : CommSq g f (0 : (supportedHomResolutionData C).R.obj Z ⟶
      (0 : CochainComplex C ℤ)) 0 :=
    ⟨(isZero_zero (CochainComplex C ℤ)).eq_of_tgt _ _⟩
  letI : sq.HasLift := ((supportedHomResolutionData C).isFibrant Z f hf).sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left⟩

private noncomputable def supportedResolutionComparisonCore
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {D : Type u''} [Category.{v''} D] [Abelian D] [IsGrothendieckAbelian.{w} D]
    (H : C ⥤ D) [H.Additive] [H.PreservesHomology] [PreservesFiniteLimits H]
    (K : CochainComplex C ℤ) :
    {a : (H.mapHomologicalComplex (.up ℤ)).obj ((supportedHomResolutionData C).R.obj K) ⟶
        (supportedHomResolutionData D).R.obj ((H.mapHomologicalComplex (.up ℤ)).obj K) //
      (H.mapHomologicalComplex (.up ℤ)).map ((supportedHomResolutionData C).unit.app K) ≫ a =
        (supportedHomResolutionData D).unit.app ((H.mapHomologicalComplex (.up ℤ)).obj K)} := by
  classical
  let P := H.mapHomologicalComplex (ComplexShape.up ℤ)
  haveI : Mono ((supportedHomResolutionData C).unit.app K) :=
    ((supportedHomResolutionData C).unitMonoQuasiIso K).1
  haveI : QuasiIso ((supportedHomResolutionData C).unit.app K) :=
    ((supportedHomResolutionData C).unitMonoQuasiIso K).2
  exact supportedResolutionLift (P.obj K)
    (P.map ((supportedHomResolutionData C).unit.app K))
    ((supportedHomResolutionData D).unit.app (P.obj K))

private noncomputable abbrev supportedResolutionComparison (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T) :=
  supportedResolutionComparisonCore (upperStar (ModuleCat.{u + 1} A) h)

private noncomputable def supportedComplexComparison
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    {B : Type u''} [Category.{v''} B] [Preadditive B]
    (H : C ⥤ D) [H.PreservesZeroMorphisms]
    (E : C ⥤ B) [E.PreservesZeroMorphisms]
    (E' : D ⥤ B) [E'.PreservesZeroMorphisms] (α : E ⟶ H ⋙ E')
    (I : CochainComplex C ℤ) (J : CochainComplex D ℤ)
    (a : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J) :
    (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      (E'.mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
  (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I ≫
    (E'.mapHomologicalComplex (ComplexShape.up ℤ)).map a

private noncomputable def supportedLinearHomComparison (A : Type v) [CommRing A]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]
    {D : Type u'} [Category.{v} D] [Preadditive D] [Linear A D]
    (H : C ⥤ D) [H.Additive] [H.Linear A] (P : C) (P' : D) (e : P' ⟶ H.obj P) :
    (linearCoyoneda A C).obj (op P) ⟶ H ⋙ (linearCoyoneda A D).obj (op P') where
  app L := ModuleCat.ofHom
    { toFun := fun c ↦ e ≫ H.map c
      map_add' := by intros; simp [Functor.map_add, Preadditive.comp_add]
      map_smul' := by intros; simp [Functor.map_smul, Linear.comp_smul] }
  naturality L L' f := by
    ext c
    change e ≫ H.map (c ≫ f) = (e ≫ H.map c) ≫ H.map f
    simp [Functor.map_comp]

private noncomputable def supportedSectionChainMap (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J) :
    ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶
    ((Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J :=
  supportedComplexComparison (upperStar (ModuleCat.{u + 1} A) h)
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A))
    (closedSupportSectionsPullback A h) I J a

private noncomputable def supportedOpenSectionChainMap (A : Type (u + 1)) [CommRing A]
    {T' T V' V : Scheme.{u}} (h : T' ⟶ T) (v : V ⟶ T) (v' : V' ⟶ T')
    (hV : V' ⟶ V) (sq : CommSq hV v' v h)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J) :
    ((upperStar (ModuleCat.{u + 1} A) v ⋙
      Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I ⟶
    ((upperStar (ModuleCat.{u + 1} A) v' ⋙
      Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J := by
  let e := (squareUpperStarIso (ModuleCat.{u + 1} A) sq).symm
  let β :
      upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) h ⋙
        (upperStar (ModuleCat.{u + 1} A) v' ⋙
          Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v)
      (closedSupportSectionsPullback A hV) ≫
    Functor.whiskerRight e.hom (Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A))
  exact supportedComplexComparison (upperStar (ModuleCat.{u + 1} A) h)
    (upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStar (ModuleCat.{u + 1} A) v' ⋙ Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A))
    β I J a

private theorem supportedUpperStarLinear (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T) :
    (upperStar (ModuleCat.{u + 1} A) h).Linear A := inferInstance

private noncomputable def supportedHomChainMap (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i)))
    : ∀ (I : CochainComplex
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      (supportedPullbackComplex A h I ⟶ J) →
        (supportedHomComplex A i I ⟶ supportedHomComplex A i' J) :=
  let H := upperStar (ModuleCat.{u + 1} A) h
  letI : H.Linear A := supportedUpperStarLinear A h
  supportedComplexComparison H (closedSupportHomFunctor A i) (closedSupportHomFunctor A i')
    (supportedLinearHomComparison A
      (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
      (D := Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) H
      ((closedSupportHomSource A i))
      ((closedSupportHomSource A i')) e)

private theorem supportedHomChainMap_condition (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (e : closedSupportHomSource A i' ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj (closedSupportHomSource A i))
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J) :
    supportedHomMapCondition A h i i' e I J a (supportedHomChainMap A h i i' e I J a) := by
  intro n c
  change (e ≫ (upperStar (ModuleCat.{u + 1} A) h).map c) ≫ a.f n = _
  exact Category.assoc _ _ _

private theorem supportedSectionChainMap_f (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J) (n : ℤ) :
    (supportedSectionChainMap A h I J a).f n =
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h (I.X n) ≫
        (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).map (a.f n) := rfl

private theorem supportedOpenSectionChainMap_f (A : Type (u + 1)) [CommRing A]
    {T' T V' V : Scheme.{u}} (h : T' ⟶ T) (v : V ⟶ T) (v' : V' ⟶ T')
    (hV : V' ⟶ V) (sq : CommSq hV v' v h)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J) (n : ℤ) :
    (supportedOpenSectionChainMap A h v v' hV sq I J a).f n =
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) hV
          ((upperStar (ModuleCat.{u + 1} A) v).obj (I.X n)) ≫
        (Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).map
          ((squareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app (I.X n) ≫
            (upperStar (ModuleCat.{u + 1} A) v').map (a.f n)) := by
  simp only [supportedOpenSectionChainMap, supportedComplexComparison,
    HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    closedSupportSectionsPullback, Functor.map_comp, Functor.comp_map, Category.assoc]

private theorem supportedSectionsRestrictionSquare (A : Type (u + 1)) [CommRing A]
    {T' T V' V : Scheme.{u}} (h : T' ⟶ T) (v : V ⟶ T) (v' : V' ⟶ T')
    (hV : V' ⟶ V) (sq : CommSq hV v' v h)
    (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A))
    (a : (upperStar (ModuleCat.{u + 1} A) h).obj J ⟶ J') :
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h J ≫
        (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).map a ≫
          globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v' J' =
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J ≫
        globalSectionsUpperStarMap (ModuleCat.{u + 1} A) hV
          ((upperStar (ModuleCat.{u + 1} A) v).obj J) ≫
          (Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).map
            ((squareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app J ≫
              (upperStar (ModuleCat.{u + 1} A) v').map a) := by
  let G := Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)
  have hx := globalSectionsUpperStarMap_comp_squareUpperStarIso
    (ModuleCat.{u + 1} A) sq J
  have hi := congrArg
    (fun f ↦ f ≫ G.map ((squareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app J)) hx
  dsimp only [G] at hi
  simp only [Category.assoc,
    ← (Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).map_comp,
    Iso.hom_inv_id_app] at hi
  erw [(Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).map_id] at hi
  rw [Category.comp_id] at hi
  rw [closedSupportHom_globalSections_natural v' a]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hi]


private theorem supportedConstantComposition (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (k : X ⟶ Z) (hk : k = g ≫ f) :
    (upperStarComp (ModuleCat.{u + 1} A) g f k hk).hom.app (ordinaryFiniteConstant A Z) ≫
      (upperStar (ModuleCat.{u + 1} A) g).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          (ModuleCat.of A A)) ≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).hom.app
        (ModuleCat.of A A) =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) k).hom.app
        (ModuleCat.of A A) := by
  subst k
  exact Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} A) g f (ModuleCat.of A A)

private theorem supportedBaseChangeUnit (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (hD : D' ⟶ D) (sq : CommSq hD i' i h) :
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app
        (ModuleCat.of A A)).inv ≫
      (upperStar (ModuleCat.{u + 1} A) h).map (supportedConstantUnit A i) ≫
        supportedConstantExchange A i i' h hD sq = supportedConstantUnit A i' := by
  let P := ordinaryFiniteConstant A T
  let H := upperStar (ModuleCat.{u + 1} A) h
  let HD := upperStar (ModuleCat.{u + 1} A) hD
  let L := lowerStar (ModuleCat.{u + 1} A) i'
  let c {X Y : Scheme.{u}} (f : X ⟶ Y) := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A)
    f).hom.app
    (ModuleCat.of A A)
  have hc : (squareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app P ≫
      HD.map (c i) ≫ c hD = (upperStar (ModuleCat.{u + 1} A) i').map (c h) ≫ c i' := by
    dsimp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [Scheme.upperStarConstantSheafIso_comp]
    apply (cancel_epi ((upperStarComp (ModuleCat.{u + 1} A) i' h (hD ≫ i) sq.w).hom.app P)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (supportedConstantComposition A i' h (hD ≫ i) sq.w).symm
  simp only [supportedConstantUnit, supportedConstantExchange, Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc]
  change (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app
      (ModuleCat.of A A) ≫ H.map ((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) i).unit.app P) ≫ H.map ((lowerStar
          (ModuleCat.{u + 1} A) i).map (c i)) ≫
      (baseChangeMap (ModuleCat.{u + 1} A) sq).app (ordinaryFiniteConstant A D) ≫
        L.map (c hD) =
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').unit.app
      (ordinaryFiniteConstant A T') ≫ L.map (c i')
  rw [reassoc_of% (baseChangeMap_naturality (ModuleCat.{u + 1} A) sq (c i)),
    reassoc_of% (map_unit_baseChangeMap_app (ModuleCat.{u + 1} A) sq P)]
  rw [← L.map_comp, ← L.map_comp, hc]
  simp only [L.map_comp]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').unit.naturality
    (c h)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp [c]

private theorem supportedEvaluateSection_eq (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : ordinaryFiniteConstant A T ⟶ J) :
    supportedEvaluateSection A T J f = rankOneSectionsEquiv A T J f := rfl

private theorem supportedEvaluationSquare (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A))
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i)))
    (a : (upperStar (ModuleCat.{u + 1} A) h).obj J ⟶ J')
    (c : (closedSupportHomSource A i) ⟶ J)
    (hu : supportedConstantUnit A i' ≫ e =
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app
        (ModuleCat.of A A)).inv ≫
        (upperStar (ModuleCat.{u + 1} A) h).map (supportedConstantUnit A i)) :
    supportedEvaluateSection A T' J'
        (supportedConstantUnit A i' ≫ e ≫ (upperStar (ModuleCat.{u + 1} A) h).map c ≫ a) =
      (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).map a
        (globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h J
          (supportedEvaluateSection A T J (supportedConstantUnit A i ≫ c))) := by
  rw [supportedEvaluateSection_eq, supportedEvaluateSection_eq]
  let H := upperStar (ModuleCat.{u + 1} A) h
  let c₀ := ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app
    (ModuleCat.of A A)).inv
  have he : supportedConstantUnit A i' ≫ e ≫ H.map c ≫ a =
      (c₀ ≫ H.map (supportedConstantUnit A i ≫ c)) ≫ a := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, ← Category.assoc, hu]
    simp only [Category.assoc]
    rfl
  rw [he]
  exact (rankOneSectionsEquiv_naturality A T' a
    (c₀ ≫ H.map (supportedConstantUnit A i ≫ c))).trans
      (congrArg (fun x ↦ (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).map a x)
        (rankOneSections_restriction A h J (supportedConstantUnit A i ≫ c)).symm)

private theorem supportedToSectionsSquareCore (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i)))
    (hu : supportedConstantUnit A i' ≫ e =
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app
        (ModuleCat.of A A)).inv ≫
        (upperStar (ModuleCat.{u + 1} A) h).map (supportedConstantUnit A i))
    (s : (supportedSectionsComplexFunctor A T).obj I ⟶
      (supportedSectionsComplexFunctor A T').obj J)
    (f : supportedHomComplex A i I ⟶ supportedHomComplex A i' J)
    (t : supportedHomComplex A i I ⟶ (supportedSectionsComplexFunctor A T).obj I)
    (t' : supportedHomComplex A i' J ⟶ (supportedSectionsComplexFunctor A T').obj J)
    (hs : supportedSectionsMapCondition A h I J a s)
    (hf : supportedHomMapCondition A h i i' e I J a f)
    (ht : supportedHomSectionNormalization A i I t)
    (ht' : supportedHomSectionNormalization A i' J t') : f ≫ t' = t ≫ s := by
  have ht := (supportedHomSectionNormalization_iff A i I t).mp ht
  have ht' := (supportedHomSectionNormalization_iff A i' J t').mp ht'
  ext n c
  change (t'.f n)
      ((f.f n) c) =
    (s.f n) ((t.f n) c)
  rw [ht' n _, ht n c,
    hf n c, hs n]
  simp only [ModuleCat.comp_apply]
  exact supportedEvaluationSquare A h i i' (I.X n) (J.X n) e
    (a.f n) c hu

private def supportedToSectionsCondition
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀] {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'}
    (N : SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d) (K : C) : Prop :=
  N.homMap K ≫ N.targetModel.toSections (d.P.obj K) =
    N.sourceModel.toSections K ≫ N.sectionsMap K

private theorem supportedToSectionsFromFamily
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀] {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'}
    (N : SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d)
    (compat : ∀ I J (a : d.P.obj I ⟶ J)
      (s : d.source.E.obj I ⟶ d.target.E.obj J)
      (f : d.source.F.obj I ⟶ d.target.F.obj J)
      (t : d.source.F.obj I ⟶ d.source.E.obj I)
      (t' : d.target.F.obj J ⟶ d.target.E.obj J),
      d.sectionsSpec I J a s → d.homSpec I J a f →
      d.source.normalization I t → d.target.normalization J t' → f ≫ t' = t ≫ s)
    (K : C) : supportedToSectionsCondition N K :=
  compat (d.source.R.obj K) (d.target.R.obj (d.P.obj K))
    (N.resolutionComparison K) (N.sectionsMap K) (N.homMap K)
    (N.sourceModel.toSections K) (N.targetModel.toSections (d.P.obj K))
    (N.sectionsMap_spec K) (N.homMap_spec K) (N.sourceModel.toSections_spec K)
    (N.targetModel.toSections_spec (d.P.obj K))

private theorem supportedToSectionsSquare (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    supportedToSectionsCondition N.maps K := by
  let : IsIso (supportedConstantExchange A i i' h hD sqD.toCommSq) := N.exchange_isIso
  have hu : supportedConstantUnit A i' ≫ N.exchangeInverse =
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app
        (ModuleCat.of A A)).inv ≫
        (upperStar (ModuleCat.{u + 1} A) h).map (supportedConstantUnit A i) := by
    apply (cancel_mono (supportedConstantExchange A i i' h hD sqD.toCommSq)).mp
    rw [Category.assoc, N.exchange_inv_hom]
    erw [Category.comp_id]
    simpa only [Category.assoc] using
      (supportedBaseChangeUnit A h i i' hD sqD.toCommSq).symm
  exact supportedToSectionsFromFamily N.maps
    (fun I J a s f t t' hs hf ht ht' ↦
      supportedToSectionsSquareCore A h i i' I J a N.exchangeInverse hu
        s f t t' hs hf ht ht') K


private theorem supportedConeMapComponents
    {C : Type u'} [Category.{v'} C] [Abelian C]
    {P Q P' Q' : CochainComplex C ℤ} (q : P ⟶ Q) (q' : P' ⟶ Q')
    (s : P ⟶ P') (b : Q ⟶ Q') (hp : q ≫ b = s ≫ q')
    (n m : ℤ) (hn : m + 1 = n) :
    (CochainComplex.mappingCone.map q q' s b hp).f m ≫
        HomologicalComplex.homotopyCofiber.fstX q' m n hn =
      HomologicalComplex.homotopyCofiber.fstX q m n hn ≫ s.f n ∧
    (CochainComplex.mappingCone.map q q' s b hp).f m ≫
        HomologicalComplex.homotopyCofiber.sndX q' m =
      HomologicalComplex.homotopyCofiber.sndX q m ≫ b.f m := by
  have hi : HomologicalComplex.homotopyCofiber.inlX q n m hn ≫
      (CochainComplex.mappingCone.map q q' s b hp).f m =
    s.f n ≫ HomologicalComplex.homotopyCofiber.inlX q' n m hn := by
    have hm : m = n + (-1 : ℤ) := by omega
    change (CochainComplex.mappingCone.inl q).v n m hm.symm ≫ _ =
      s.f n ≫ (CochainComplex.mappingCone.inl q').v n m hm.symm
    simp [CochainComplex.mappingCone.map]
  have hj : HomologicalComplex.homotopyCofiber.inrX q m ≫
      (CochainComplex.mappingCone.map q q' s b hp).f m =
    b.f m ≫ HomologicalComplex.homotopyCofiber.inrX q' m := by
    change (CochainComplex.mappingCone.inr q).f m ≫ _ =
      b.f m ≫ (CochainComplex.mappingCone.inr q').f m
    simp [CochainComplex.mappingCone.map]
  constructor
  · apply HomologicalComplex.homotopyCofiber.ext_from_X q n m hn
    · rw [← Category.assoc, hi, Category.assoc]
      simp
    · rw [← Category.assoc, hj, Category.assoc]
      simp
  · apply HomologicalComplex.homotopyCofiber.ext_from_X q n m hn
    · rw [← Category.assoc, hi, Category.assoc]
      simp
    · rw [← Category.assoc, hj, Category.assoc]
      simp

private theorem supportedInclusionSquare
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'}
    (N : SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d) (K : C)
    (hsections : supportedToSectionsCondition N K) :
    N.homMap K ≫ N.targetModel.inclusion (d.P.obj K) =
      N.sourceModel.inclusion K ≫
        (CochainComplex.mappingCone.map
          (N.sourceModel.q.app (d.source.R.obj K))
          (N.targetModel.q.app (d.target.R.obj (d.P.obj K)))
          (N.sectionsMap K) (N.openSectionsMap K)
          (N.restriction_square K).symm)⟦(-1 : ℤ)⟧' := by
  let q := N.sourceModel.q.app (d.source.R.obj K)
  let q' := N.targetModel.q.app (d.target.R.obj (d.P.obj K))
  let f := CochainComplex.mappingCone.map q q' (N.sectionsMap K) (N.openSectionsMap K)
    (N.restriction_square K).symm
  have hf (n : ℤ) : f.f (n + (-1)) ≫
      HomologicalComplex.homotopyCofiber.fstX q' (n + (-1)) n (by change _ + 1 = n; omega) =
    HomologicalComplex.homotopyCofiber.fstX q (n + (-1)) n (by change _ + 1 = n; omega) ≫
      (N.sectionsMap K).f n :=
    (supportedConeMapComponents q q' (N.sectionsMap K) (N.openSectionsMap K)
      (N.restriction_square K).symm n (n + (-1)) (by omega)).1
  have hg (n : ℤ) : f.f (n + (-1)) ≫
      HomologicalComplex.homotopyCofiber.sndX q' (n + (-1)) =
    HomologicalComplex.homotopyCofiber.sndX q (n + (-1)) ≫
      (N.openSectionsMap K).f (n + (-1)) :=
    (supportedConeMapComponents q q' (N.sectionsMap K) (N.openSectionsMap K)
      (N.restriction_square K).symm n (n + (-1)) (by omega)).2
  have hsf (n : ℤ) : (N.sourceModel.inclusion K).f n ≫
      HomologicalComplex.homotopyCofiber.fstX q (n + (-1)) n (by change _ + 1 = n; omega) =
    (N.sourceModel.toSections K).f n := by
    simpa [CochainComplex.shiftFunctorObjXIso] using
      N.sourceModel.inclusion_fst K n (n + (-1)) rfl (by omega)
  have hsg (n : ℤ) : (N.sourceModel.inclusion K).f n ≫
      HomologicalComplex.homotopyCofiber.sndX q (n + (-1)) = 0 := by
    simpa [CochainComplex.shiftFunctorObjXIso] using
      N.sourceModel.inclusion_snd K n (n + (-1)) rfl
  have htf (n : ℤ) : (N.targetModel.inclusion (d.P.obj K)).f n ≫
      HomologicalComplex.homotopyCofiber.fstX q' (n + (-1)) n (by change _ + 1 = n; omega) =
    (N.targetModel.toSections (d.P.obj K)).f n := by
    simpa [CochainComplex.shiftFunctorObjXIso] using
      N.targetModel.inclusion_fst _ n (n + (-1)) rfl (by omega)
  have htg (n : ℤ) : (N.targetModel.inclusion (d.P.obj K)).f n ≫
      HomologicalComplex.homotopyCofiber.sndX q' (n + (-1)) = 0 := by
    simpa [CochainComplex.shiftFunctorObjXIso] using
      N.targetModel.inclusion_snd _ n (n + (-1)) rfl
  ext n : 1
  change (N.homMap K).f n ≫ (N.targetModel.inclusion _).f n =
    (N.sourceModel.inclusion K).f n ≫ f.f (n + (-1))
  apply HomologicalComplex.homotopyCofiber.ext_to_X q' (n + (-1)) n
    (by change _ + 1 = n; omega)
  · simp only [Category.assoc, htf, hf, reassoc_of% hsf]
    exact congrArg (fun a ↦ a.f n) hsections
  · simp only [Category.assoc, htg, hg, reassoc_of% hsg, comp_zero, zero_comp]

private theorem supportedPullbackSquareCore
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'}
    (N : SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d)
    {E : Type*} [Category E] (H : D₀ ⥤ E) (K : C)
    (hsections : supportedToSectionsCondition N K) :
    H.map (N.relativePullback K) ≫ H.map (N.targetModel.comparison (d.P.obj K)).inv =
      H.map (N.sourceModel.comparison K).inv ≫ H.map (N.homPullback K) := by
  have hs : (N.sourceModel.comparison K).hom ≫ N.relativePullback K =
      N.homPullback K ≫
        (N.targetModel.comparison (d.P.obj K)).hom := by
    rw [N.sourceModel.comparison_spec,
      N.targetModel.comparison_spec]
    simp only [SupportedHomPullbackMaps.homPullback, SupportedHomConeModelCore.transport,
      Category.assoc, Iso.inv_hom_id_assoc]
    dsimp only [SupportedHomPullbackMaps.relativePullback]
    rw [← Q₀.map_comp, ← supportedInclusionSquare N K hsections,
      Q₀.map_comp]
  change H.map _ ≫ H.map (N.targetModel.comparison _).inv =
    H.map (N.sourceModel.comparison K).inv ≫ H.map _
  simp only [← H.map_comp]
  apply congrArg H.map
  apply (cancel_epi (N.sourceModel.comparison K).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hs]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem supportedPullbackSquare (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
        (supportedRelativePullback A N K) ≫
      (supportedHomIdentification A N.targetModel (supportedPullbackComplex A h K) n).hom =
    (supportedHomIdentification A N.sourceModel K n).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
        (supportedHomPullback A N K) := by
  exact supportedPullbackSquareCore N.maps
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n) K
    (supportedToSectionsSquare A N K)

private noncomputable def supportedPullbackMapsFromFamilies
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀] {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'}
    (M : SupportedHomConeModelCore B₀ D₀ Q₀ C d.source)
    (M' : SupportedHomConeModelCore B₀ D₀ Q₀ C' d.target)
    (a : ∀ K, d.P.obj (d.source.R.obj K) ⟶ d.target.R.obj (d.P.obj K))
    (ha : ∀ K, d.unitSpec K (a K))
    (s : ∀ I J, (d.P.obj I ⟶ J) → (d.source.E.obj I ⟶ d.target.E.obj J))
    (hs : ∀ I J a, d.sectionsSpec I J a (s I J a))
    (b : ∀ I J, (d.P.obj I ⟶ J) → (d.source.B.obj I ⟶ d.target.B.obj J))
    (hb : ∀ I J a, d.openSpec I J a (b I J a))
    (f : ∀ I J, (d.P.obj I ⟶ J) → (d.source.F.obj I ⟶ d.target.F.obj J))
    (hf : ∀ I J a, d.homSpec I J a (f I J a))
    (hr : ∀ I J a, s I J a ≫ M'.q.app J = M.q.app I ≫ b I J a) :
    SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d where
  sourceModel := M
  targetModel := M'
  resolutionComparison := a
  resolutionComparison_spec := ha
  sectionsMap := fun K ↦ s _ _ (a K)
  sectionsMap_spec := fun K ↦ hs _ _ (a K)
  openSectionsMap := fun K ↦ b _ _ (a K)
  openSectionsMap_spec := fun K ↦ hb _ _ (a K)
  restriction_square := fun K ↦ hr _ _ (a K)
  homMap := fun K ↦ f _ _ (a K)
  homMap_spec := fun K ↦ hf _ _ (a K)

private theorem supportedHomDataWithModels (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) [IsClosedImmersion i]
    (i' : D' ⟶ T') (hD : D' ⟶ D) (sqD : IsPullback hD i' i h) [IsClosedImmersion i']
    (v : V ⟶ T) (v' : V' ⟶ T') [IsOpenImmersion v] [IsOpenImmersion v']
    (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (M : SupportedHomConeModel A i v) (M' : SupportedHomConeModel A i' v') :
    Nonempty (SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) := by
  classical
  let E := supportedConstantExchange A i i' h hD sqD.toCommSq
  have : IsIso (baseChangeMap (ModuleCat.{u + 1} A) sqD.toCommSq) :=
    isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sqD
  have : IsIso E := by dsimp only [E, supportedConstantExchange]; infer_instance
  refine ⟨{
      exchange_isIso := inferInstance
      exchangeInverse := inv E
      exchange_hom_inv := IsIso.hom_inv_id E
      exchange_inv_hom := IsIso.inv_hom_id E
      maps := supportedPullbackMapsFromFamilies M M'
        (fun K ↦ (supportedResolutionComparison A h K).val)
        (fun K ↦ (supportedResolutionComparison A h K).property)
        (supportedSectionChainMap A h) (supportedSectionChainMap_f A h)
        (supportedOpenSectionChainMap A h v v' hV sqV.toCommSq) ?_
        (supportedHomChainMap A h i i' (inv E))
        (supportedHomChainMap_condition A h i i' (inv E)) ?_ }⟩
  · intro I J a n
    rw [supportedOpenSectionChainMap_f]
    simp only [squareUpperStarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Category.assoc]
  · intro I J a
    ext n : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, M.q_spec, M'.q_spec]
    rw [supportedSectionChainMap_f, supportedOpenSectionChainMap_f]
    simp only [Category.assoc]
    exact supportedSectionsRestrictionSquare A h v v' hV sqV.toCommSq
      (I.X n) (J.X n) (a.f n)

private theorem supportedHomData (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) [IsClosedImmersion i]
    (i' : D' ⟶ T') (hD : D' ⟶ D) (sqD : IsPullback hD i' i h) [IsClosedImmersion i']
    (v : V ⟶ T) (v' : V' ⟶ T') [IsOpenImmersion v] [IsOpenImmersion v']
    (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (hcomp' : Set.range v'.base = (Set.range i'.base)ᶜ) :
    Nonempty (SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) := by
  obtain ⟨M⟩ := supportedConeModel A i v hcomp
  obtain ⟨M'⟩ := supportedConeModel A i' v' hcomp'
  exact supportedHomDataWithModels A h i i' hD sqD v v' hV sqV M M'

/-- The supported-Hom identification intertwines the actual relative pullback and
inverse-image/precomposition map. Forgetting support is the actual cone projection, with
fixed target the global-section complex, and corresponds to precomposition with the unit.
Source: Stacks, Tags 0A45, 095L; blueprint lem-amb-cartier-kummer-map, penultimate paragraph
(blueprint: lem-asd-supported-kummer-support-hom-naturality).

Proof:
1. A closed immersion is finite, so finite base change makes the specified exchange
   invertible. The mate identity for exchange and compatibility of the constant-sheaf
   comparison with composition show that it preserves the specified constant units.
2. Exact inverse image sends the functorial resolution unit to a monomorphic
   quasi-isomorphism. Lift it against the map from the fixed target K-injective
   resolution to zero. The resulting chain map extends the pulled-back unit.
3. Apply Hom into an injective term to the constant open-closed short exact sequence.
   The rank-one constant-sheaf/global-section equivalence gives the specified evaluation
   formula and identifies the second map with restriction. The resulting degreewise
   short exact sequence makes its normalized kernel inclusion into the shifted
   restriction cone a quasi-isomorphism. Localize that inclusion and the canonical
   derived-functor computation on the chosen resolution to obtain the natural model.
4. Construct the section and Hom chain maps from their natural transformations and the
   resolution comparison. The square's upper-star isomorphism defines the open map.
   Functoriality gives the restriction square; the unit identity gives the evaluation
   square. The two cone projections then prove the square with the kernel inclusions.
5. Localize this strict square, cancel the specified comparison isomorphisms and apply
   homology. This proves the pullback formula for all complexes, including bounded-below
   complexes as required by the statement.
6. The cone projection composed with the kernel inclusion equals the normalized map to
   sections. Localizing this identity and applying homology gives the two equations for
   forgetting support with exactly their specified targets.
-/
theorem supportedKummerSupportHomNaturality (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) [IsClosedImmersion i]
    (i' : D' ⟶ T') (hD : D' ⟶ D) (sqD : IsPullback hD i' i h) [IsClosedImmersion i']
    (v : V ⟶ T) (v' : V' ⟶ T') [IsOpenImmersion v] [IsOpenImmersion v']
    (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (hcomp' : Set.range v'.base = (Set.range i'.base)ᶜ) :
    ∃ N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV,
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (_hK : ∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (K.X n)) (n : ℤ),
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
            (supportedRelativePullback A N K) ≫
          (supportedHomIdentification A N.targetModel (supportedPullbackComplex A h K) n).hom =
        (supportedHomIdentification A N.sourceModel K n).hom ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
            (supportedHomPullback A N K)) ∧
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (n : ℤ),
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
            (DerivedCategory.Q.map (N.sourceModel.projection K)) =
          (supportedHomIdentification A N.sourceModel K n).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
              ((N.sourceModel.modelIso K).hom ≫
                DerivedCategory.Q.map (N.sourceModel.toSections K))) ∧
      (∀ (K : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (n : ℤ),
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
            (DerivedCategory.Q.map (N.targetModel.projection K)) =
          (supportedHomIdentification A N.targetModel K n).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
              ((N.targetModel.modelIso K).hom ≫
                DerivedCategory.Q.map (N.targetModel.toSections K))) := by
  obtain ⟨N⟩ := supportedHomData A h i i' hD sqD v v' hV sqV hcomp hcomp'
  exact ⟨N, (fun K _ n ↦ supportedPullbackSquare A N K n),
    (fun K n ↦ supportedForget N.sourceModel
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n) K),
    (fun K n ↦ supportedForget N.targetModel
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n) K)⟩

end AlgebraicGeometry.Etale
