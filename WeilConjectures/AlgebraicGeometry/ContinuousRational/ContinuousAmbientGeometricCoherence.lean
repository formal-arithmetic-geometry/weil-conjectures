/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationScalarCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit

/-! # Normalized continuous tensor coherence

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-ambient-geometric-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.ContinuousRational

attribute [local irreducible] HasDerivedCategory.standard
  Functor.sheafPullbackConstruction.sheafPullback proEtaleRingInverseImageComp
  LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary and derived composition, before any raw lift.
Source: BS Remark 6.8.15; Stacks 0D6D
(blueprint: lem-per-continuous-ambient-geometric-coherence). -/
structure AmbientComposition {X Y Z : Base.{u} l}
    (g : X.scheme ⟶ Y.scheme)
    (h : Z.scheme ⟶ X.scheme) (aX : At l E X) (aY : At l E Y) (aZ : At l E Z)
    (ag : Along l E g aX aY) (ah : Along l E h aZ aX)
    (ahg : Along l E (h ≫ g) aZ aY) where
  coefficient : ahg.coefficient =
    (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l Y.scheme E) ≫
      (adicTowerInverseImage h).map ag.coefficient ≫ ah.coefficient
  ordinary : modulePull (h ≫ g) ahg.coefficient ≅
    modulePull g ag.coefficient ⋙ modulePull h ah.coefficient
  ordinary_units : ∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
      (U : Y.scheme.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (h ≫ g)).obj U))
        (moduleUnit (h ≫ g) ahg.coefficient M U m) =
      (((modulePull h ah.coefficient).obj ((modulePull g ag.coefficient).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp h g).hom.app U).op)
          (moduleUnit h ah.coefficient ((modulePull g ag.coefficient).obj M)
            ((proEtaleBaseChange g).obj U) (moduleUnit g ag.coefficient M U m))
  complex : (modulePull (h ≫ g) ahg.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (modulePull g ag.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (modulePull h ah.coefficient).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  ambient : derivedPull (h ≫ g) ahg.coefficient ≅
    derivedPull g ag.coefficient ⋙ derivedPull h ah.coefficient
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) (P.X n)) →
    ahg.counit.app P ≫ DerivedCategory.Q.map (complex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (derivedPull h ah.coefficient).map (ag.counit.app P) ≫
        ah.counit.app (((modulePull g ag.coefficient).mapHomologicalComplex (.up ℤ)).obj P)

/-- Ordinary and derived identity, before any raw lift.
Source: BS Remark 6.8.15; Stacks 0D6D
(blueprint: lem-per-continuous-ambient-geometric-coherence). -/
structure AmbientIdentity (X : Base.{u} l) (a : At l E X)
    (ai : Along l E (𝟙 X.scheme) a a) where
  site : proEtaleBaseChange (𝟙 X.scheme) ≅ 𝟭 X.scheme.ProEt
  site_normalization : ∀ U,
    (site.hom.app U).left = pullback.fst U.hom (𝟙 X.scheme)
  ordinary : modulePull (𝟙 X.scheme) ai.coefficient ≅ 𝟭 _
  ordinary_units : ∀ (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
      (U : X.scheme.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X.scheme)).obj U))
        (moduleUnit (𝟙 X.scheme) ai.coefficient M U m) =
      M.val.map (site.hom.app U).op m
  ambient : derivedPull (𝟙 X.scheme) ai.coefficient ≅ 𝟭 _
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X.scheme)
      (R := rationalCoefficientSheaf l X.scheme E) P →
    ai.counit.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P)

private theorem coefficient_unique {X Y : Scheme.{u}} (g : X ⟶ Y)
    (c d : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l X E)
    (hc : rationalCoefficientRestrictionNormalized l E g c)
    (hd : rationalCoefficientRestrictionNormalized l E g d) : c = d := by
  let := coefficientExtensionNormedField l E
  apply ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ContinuousMap.ext
  intro x
  exact (hc U.unop s x).trans (hd U.unop s x).symm

private structure LegacyComposition {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Z ⟶ X)
    (cg : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l X E)
    (ch : (adicTowerInverseImage h).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Z E)
    (cc : (adicTowerInverseImage (h ≫ g)).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l Z E) where
  coefficient : cc = (proEtaleRingInverseImageComp h g).hom.app
    (rationalCoefficientSheaf l Y E) ≫ (adicTowerInverseImage h).map cg ≫ ch
  ordinary : rationalPullModule l E (h ≫ g) cc ≅
    rationalPullModule l E g cg ⋙ rationalPullModule l E h ch
  units : ∀ (M : pbcModules Y (rationalCoefficientSheaf l Y E))
      (U : Y.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (h ≫ g)).obj U))
        (rationalScalarPullModuleUnit l E (h ≫ g) cc M U m) =
      (((rationalPullModule l E h ch).obj ((rationalPullModule l E g cg).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp h g).hom.app U).op)
          (rationalScalarPullModuleUnit l E h ch ((rationalPullModule l E g cg).obj M)
            ((proEtaleBaseChange g).obj U) (rationalScalarPullModuleUnit l E g cg M U m))
  ambient : derivedPull (h ≫ g) cc ≅ derivedPull g cg ⋙ derivedPull h ch
  normalization : ∀ P : CochainComplex (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ,
    ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (derivedPull h ch).map (rationalPullComplexCounit l E g cg P) ≫
        rationalPullComplexCounit l E h ch
          (((rationalPullModule l E g cg).mapHomologicalComplex (.up ℤ)).obj P) =
      rationalPullComplexCounit l E (h ≫ g) cc P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

private theorem legacyComposition {X Y Z : Base.{u} l}
    (g : X.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme)
    {aX : At l E X} {aY : At l E Y} {aZ : At l E Z}
    (ag : Along l E g aX aY) (ah : Along l E h aZ aX)
    (ac : Along l E (h ≫ g) aZ aY) :
    Nonempty (LegacyComposition l E g h ag.coefficient ah.coefficient ac.coefficient) := by
  obtain ⟨sX⟩ := rationalModuleRealizationFunctor l E X.scheme
  obtain ⟨sY⟩ := rationalModuleRealizationFunctor l E Y.scheme
  obtain ⟨sZ⟩ := rationalModuleRealizationFunctor l E Z.scheme
  obtain ⟨rg⟩ := rationalRealizationPullbackComparison l E g sX sY
  obtain ⟨rh⟩ := rationalRealizationPullbackComparison l E h sZ sX
  obtain ⟨rc⟩ := rationalRealizationPullbackComparison l E (h ≫ g) sZ sY
  obtain ⟨c⟩ := rationalScalarPullComposition l E g h sX sY sZ rg rh rc
  have heG := coefficient_unique l E g rg.rationalCoefficient ag.coefficient
    rg.rational_normalization ag.normalized
  have heH := coefficient_unique l E h rh.rationalCoefficient ah.coefficient
    rh.rational_normalization ah.normalized
  have heC := coefficient_unique l E (h ≫ g) rc.rationalCoefficient ac.coefficient
    rc.rational_normalization ac.normalized
  have H : Nonempty (LegacyComposition l E g h
      rg.rationalCoefficient rh.rationalCoefficient rc.rationalCoefficient) :=
    ⟨{ coefficient := c.coefficient, ordinary := c.ordinary, units := c.ordinary_units,
       ambient := c.ambient, normalization := c.normalization }⟩
  simpa only [heG, heH, heC] using H

private structure LegacyIdentity (X : Scheme.{u})
    (ci : (adicTowerInverseImage (𝟙 X)).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l X E) where
  site : proEtaleBaseChange (𝟙 X) ≅ 𝟭 X.ProEt
  site_normalization : ∀ U, (site.hom.app U).left = pullback.fst U.hom (𝟙 X)
  ordinary : rationalPullModule l E (𝟙 X) ci ≅ 𝟭 _
  units : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E))
      (U : X.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj U))
        (rationalScalarPullModuleUnit l E (𝟙 X) ci M U m) =
      M.val.map (site.hom.app U).op m
  ambient : derivedPull (𝟙 X) ci ≅ 𝟭 _
  normalization : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    ambient.hom.app (DerivedCategory.Q.obj P) =
      rationalPullComplexCounit l E (𝟙 X) ci P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

private theorem legacyIdentity (X : Base.{u} l) {a : At l E X}
    (ai : Along l E (𝟙 X.scheme) a a) :
    Nonempty (LegacyIdentity l E X.scheme ai.coefficient) := by
  obtain ⟨s⟩ := rationalModuleRealizationFunctor l E X.scheme
  obtain ⟨r⟩ := rationalRealizationPullbackComparison l E (𝟙 X.scheme) s s
  obtain ⟨c⟩ := rationalScalarPullIdentity l E s r
  have he := coefficient_unique l E (𝟙 X.scheme) r.rationalCoefficient ai.coefficient
    r.rational_normalization ai.normalized
  have H : Nonempty (LegacyIdentity l E X.scheme r.rationalCoefficient) :=
    ⟨{ site := c.site, site_normalization := c.site_normalization, ordinary := c.ordinary,
       units := c.ordinary_units, ambient := c.ambient, normalization := c.normalization }⟩
  simpa only [he] using H

private theorem tensor_transport (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : pbcModules X R) (W : X.ProEtᵒᵖ) (s : R.obj.obj W) (m : M.val.obj W) :
    (eqToHom ((completedAdicChangeData X (𝟙 R)).choose_spec.choose M)).val.app W
        (pbcTensorSection (𝟙 R) M W s m) =
      (toSheafify (ProEt.topology X)
        (SheafOfModules.changeOfRingsPresheaf (𝟙 R) M).presheaf).app W
          (s ⊗ₜ[R.obj.obj W, ((𝟙 R : R ⟶ R).hom.app W).hom] m) := by
  simp only [pbcTensorSection, completedAdicChangeTensor, ← ConcreteCategory.comp_apply,
    ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, eqToHom_trans,
    eqToHom_refl, SheafOfModules.id_val, PresheafOfModules.id_app,
    ConcreteCategory.id_apply]

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
private theorem normalizedCancellation
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    {aX : At l E X} {aY : At l E Y} (a : Along l E g aX aY) :
    ∃ e : rationalPullModule l E g a.coefficient ≅ modulePull g a.coefficient,
      (∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
        (U : Y.scheme.ProEt) (m : M.val.obj (op U)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj U))
          (rationalScalarPullModuleUnit l E g a.coefficient M U m) =
            moduleUnit g a.coefficient M U m) ∧
      ∀ P, a.counit.app P = rationalPullComplexCounit l E g a.coefficient P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  obtain ⟨e, eC, hC, hs, hd⟩ := a.normalized_counit
  have heC : eC = NatIso.mapHomologicalComplex e (.up ℤ) := by
    apply Iso.ext
    apply NatTrans.ext
    funext P
    apply HomologicalComplex.hom_ext
    intro n
    exact hC P n
  refine ⟨e, ?_, ?_⟩
  · intro M U m
    have h := hs M (op ((proEtaleBaseChange g).obj U)) 1
      ((((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
        (proEtaleModelRingUnit g (rationalCoefficientSheaf l Y.scheme E))).unit.app
          ((proEtaleModuleToModel ((adicLisseForget Y.scheme).obj
            (rationalCoefficientSheaf l Y.scheme E))).obj M)).val.app
              (op (AsSmall.up.obj U))) m)
    rw [tensor_transport] at h
    simpa only [rationalScalarPullModuleUnit, proEtaleRingModuleUnitSection, moduleUnit,
      Iso.refl_hom, adicTowerInverseImage, adicLisseForget] using h
  · intro P
    simpa only [heC, rationalPullComplexCounit, Category.assoc] using hd P

private theorem legacyUnit_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    (c : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l X E)
    {M N : pbcModules Y (rationalCoefficientSheaf l Y E)} (f : M ⟶ N)
    (U : Y.ProEt) (m : M.val.obj (op U)) :
    ((rationalPullModule l E g c).map f).val.app (op ((proEtaleBaseChange g).obj U))
      (rationalScalarPullModuleUnit l E g c M U m) =
    rationalScalarPullModuleUnit l E g c N U (f.val.app (op U) m) := by
  let R := rationalCoefficientSheaf l Y E
  let RI := (adicTowerInverseImage g).obj R
  let A := (proEtaleRingModuleAdjunction g R RI (Iso.refl _)).comp (pbcScalarAdjunction c)
  have hu (M : pbcModules Y R) (m : M.val.obj (op U)) :
      (A.unit.app M).val.app (op U) m =
        rationalScalarPullModuleUnit l E g c M U m := by
    change ((pbcScalarAdjunction c).unit.app
      ((proEtaleRingModulePullback g R RI (Iso.refl _)).obj M)).val.app
      (op ((proEtaleBaseChange g).obj U))
        (((proEtaleRingModuleAdjunction g R RI (Iso.refl _)).unit.app M).val.app
          (op U) m) = _
    erw [(proEtaleRingModuleAdjunction_normalized g R RI (Iso.refl _)) M U m]
    exact (pbcScalarAdjunction_exists c).exists.choose_spec _ _ _
  have hn := congrArg (fun t ↦ t.val.app (op U) m) (A.unit.naturality f)
  change (A.unit.app N).val.app (op U) (f.val.app (op U) m) =
    ((rationalPullModule l E g c).map f).val.app (op ((proEtaleBaseChange g).obj U))
      ((A.unit.app M).val.app (op U) m) at hn
  rw [hu, hu] at hn
  exact hn.symm

private theorem moduleUnit_naturality {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    {aX : At l E X} {aY : At l E Y} (a : Along l E g aX aY)
    {M N : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)} (f : M ⟶ N)
    (U : Y.scheme.ProEt) (m : M.val.obj (op U)) :
    ((modulePull g a.coefficient).map f).val.app (op ((proEtaleBaseChange g).obj U))
      (moduleUnit g a.coefficient M U m) =
    moduleUnit g a.coefficient N U (f.val.app (op U) m) := by
  obtain ⟨e, hu, _⟩ := normalizedCancellation l E g a
  rw [← hu M U m, ← hu N U (f.val.app (op U) m)]
  have hn := congrArg (fun t ↦ t.val.app (op ((proEtaleBaseChange g).obj U))
    (rationalScalarPullModuleUnit l E g a.coefficient M U m)) (e.hom.naturality f)
  change (e.hom.app N).val.app _
      (((rationalPullModule l E g a.coefficient).map f).val.app _ _) =
    ((modulePull g a.coefficient).map f).val.app _
      ((e.hom.app M).val.app _ _) at hn
  rw [legacyUnit_naturality l E] at hn
  exact hn.symm

/-- Normalized tensor comparisons compose and have a normalized identity.
Source: BS Remark 6.8.15; Stacks 0D6D (blueprint: lem-per-continuous-ambient-geometric-coherence).

Proof: remove the identity scalar factor in each inverse image by multiplication.
The ordinary compositor inserts the intermediate unit, and its inverse multiplies
successive scalar factors. Balancing proves inverse identities. On a generator the
forward map inserts one twice, with restriction along the actual fibre-product
associator. Apply this map degreewise to obtain the complex comparison. On flat-term
K-flat resolutions both iterated pullbacks compute the derived functors. Descend
the complex comparison through their universal counits. The specified counit
normalizations identify its computation with the displayed equation. For identity
use the first projection of the identity fibre product and multiplication by one,
then descend through the same normalized counit. No raw realization, completion
unit or full-faithfulness argument is involved in these calculations. -/
theorem continuousAmbientGeometricCoherence
    {X Y Z : Base.{u} l} (g : X.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme)
    (aX : At l E X) (aY : At l E Y) (aZ : At l E Z)
    (ag : Along l E g aX aY) (ah : Along l E h aZ aX)
    (ac : Along l E (h ≫ g) aZ aY) (ai : Along l E (𝟙 Y.scheme) aY aY) :
    Nonempty (AmbientComposition l E g h aX aY aZ ag ah ac) ∧
      Nonempty (AmbientIdentity l E Y aY ai) := by
  constructor
  · obtain ⟨c⟩ := legacyComposition l E g h ag ah ac
    obtain ⟨eg, hug, hdg⟩ := normalizedCancellation l E g ag
    obtain ⟨eh, huh, hdh⟩ := normalizedCancellation l E h ah
    obtain ⟨ec, huc, hdc⟩ := normalizedCancellation l E (h ≫ g) ac
    let o := ec.symm ≪≫ c.ordinary ≪≫
      Functor.isoWhiskerLeft (rationalPullModule l E g ag.coefficient) eh ≪≫
      Functor.isoWhiskerRight eg (modulePull h ah.coefficient)
    refine ⟨{
      coefficient := c.coefficient
      ordinary := o
      ordinary_units := ?_
      complex := NatIso.mapHomologicalComplex o (.up ℤ)
      complex_components := fun _ _ ↦ rfl
      ambient := c.ambient
      ambient_normalization := ?_ }⟩
    · intro M U m
      rw [← huc M U m]
      change (((modulePull h ah.coefficient).map (eg.hom.app M)).val.app _)
        ((eh.hom.app ((rationalPullModule l E g ag.coefficient).obj M)).val.app _
          ((c.ordinary.hom.app M).val.app _
            ((ec.inv.app M).val.app _ ((ec.hom.app M).val.app _ _)))) = _
      have hi := congrArg (fun t ↦ t.val.app (op ((proEtaleBaseChange (h ≫ g)).obj U))
        (rationalScalarPullModuleUnit l E (h ≫ g) ac.coefficient M U m))
        (ec.hom_inv_id_app M)
      change (ec.inv.app M).val.app _ ((ec.hom.app M).val.app _ _) = _ at hi
      simp only [SheafOfModules.id_val, PresheafOfModules.id_app,
        ConcreteCategory.id_apply] at hi
      rw [hi, c.units M U m]
      erw [PresheafOfModules.naturality_apply, huh]
      erw [PresheafOfModules.naturality_apply, moduleUnit_naturality l E h ah, hug]
    · intro P _ _
      let egC := NatIso.mapHomologicalComplex eg (.up ℤ)
      let ehC := NatIso.mapHomologicalComplex eh (.up ℤ)
      let ecC := NatIso.mapHomologicalComplex ec (.up ℤ)
      let oldC := NatIso.mapHomologicalComplex c.ordinary (.up ℤ)
      let newC := NatIso.mapHomologicalComplex o (.up ℤ)
      let oldG := (rationalPullModule l E g ag.coefficient).mapHomologicalComplex (.up ℤ)
      let newH := (modulePull h ah.coefficient).mapHomologicalComplex (.up ℤ)
      have he : ecC.hom.app P ≫ newC.hom.app P =
          oldC.hom.app P ≫ ehC.hom.app (oldG.obj P) ≫ newH.map (egC.hom.app P) := by
        apply HomologicalComplex.hom_ext
        intro n
        simp [ecC, newC, oldC, ehC, egC, oldG, newH, o]
        rfl
      have hn := ah.counit.naturality (egC.hom.app P)
      simp only [Functor.comp_map] at hn
      change ac.counit.app P ≫ DerivedCategory.Q.map (newC.hom.app P) = _
      calc
        _ = rationalPullComplexCounit l E (h ≫ g) ac.coefficient P ≫
            DerivedCategory.Q.map (ecC.hom.app P ≫ newC.hom.app P) := by
          rw [hdc P, Functor.map_comp, Category.assoc]
        _ = rationalPullComplexCounit l E (h ≫ g) ac.coefficient P ≫
            DerivedCategory.Q.map (oldC.hom.app P ≫
              ehC.hom.app (oldG.obj P) ≫ newH.map (egC.hom.app P)) := by rw [he]
        _ = c.ambient.hom.app (DerivedCategory.Q.obj P) ≫
            (derivedPull h ah.coefficient).map
              (rationalPullComplexCounit l E g ag.coefficient P) ≫
            ah.counit.app (oldG.obj P) ≫
              DerivedCategory.Q.map (newH.map (egC.hom.app P)) := by
          rw [hdh (oldG.obj P)]
          simp only [Functor.map_comp, Category.assoc]
          rw [← Category.assoc, ← c.normalization P]
          simp only [Category.assoc]
          rfl
        _ = c.ambient.hom.app (DerivedCategory.Q.obj P) ≫
            (derivedPull h ah.coefficient).map
              (rationalPullComplexCounit l E g ag.coefficient P) ≫
            (derivedPull h ah.coefficient).map (DerivedCategory.Q.map (egC.hom.app P)) ≫
              ah.counit.app (((modulePull g ag.coefficient).mapHomologicalComplex
                (.up ℤ)).obj P) := by rw [← hn]
        _ = _ := by
          rw [hdg P, Functor.map_comp]
          simp only [Category.assoc]
          rfl
  · obtain ⟨c⟩ := legacyIdentity l E Y ai
    obtain ⟨e, hu, hd⟩ := normalizedCancellation l E (𝟙 Y.scheme) ai
    let o := e.symm ≪≫ c.ordinary
    refine ⟨{
      site := c.site
      site_normalization := c.site_normalization
      ordinary := o
      ordinary_units := ?_
      ambient := c.ambient
      ambient_normalization := ?_ }⟩
    · intro M U m
      rw [← hu M U m]
      change (c.ordinary.hom.app M).val.app _
        ((e.inv.app M).val.app _ ((e.hom.app M).val.app _ _)) = _
      have hi := congrArg (fun t ↦ t.val.app (op ((proEtaleBaseChange (𝟙 Y.scheme)).obj U))
        (rationalScalarPullModuleUnit l E (𝟙 Y.scheme) ai.coefficient M U m))
        (e.hom_inv_id_app M)
      change (e.inv.app M).val.app _ ((e.hom.app M).val.app _ _) = _ at hi
      rw [hi]
      exact c.units M U m
    · intro P _
      have he : (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P ≫
          (NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P =
          (NatIso.mapHomologicalComplex c.ordinary (.up ℤ)).hom.app P := by
        apply HomologicalComplex.hom_ext
        intro n
        simp [o]
      rw [hd P, c.normalization P, Category.assoc, ← Functor.map_comp, he]

end AlgebraicGeometry.Scheme.ContinuousRational
