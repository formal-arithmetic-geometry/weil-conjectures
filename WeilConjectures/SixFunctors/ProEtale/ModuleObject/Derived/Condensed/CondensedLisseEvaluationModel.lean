/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentRelativeProfiniteSite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingDerivedScalarExtension.RingDerivedScalarExtension
public import WeilConjectures.AlgebraicGeometry.DerivedChangeOfRingsModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.ProEtaleCoefficients.ConnectedComponentsProfinite
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import Mathlib.CategoryTheory.Sites.LocalSite

/-! # Evaluation and connected components of lisse condensed sheaves

Source: Hemo--Richarz--Scholbach, Section 3, (3.1)--(3.2), Remark 3.2,
Lemma 4.1 and Proposition 4.3(3)
(blueprint: def-zl-condensed-lisse-evaluation-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  [(J.W (A := Ab.{u + 1})).IsMonoidal]
  (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]

/-- The actual commutative section-ring sheaf, reconstructed from the coefficient object.
Source: HRS Section 3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
abbrev ringSheaf : Sheaf J CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J O

/-- The ordinary unbounded derived category, with ordinary relative derived tensor.
Source: HRS Section 3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
abbrev D := DerivedCategory (Mod (Sheaf J Ab.{u + 1}) O)

/-- The section ring at the terminal site object, rather than an auxiliary ring parameter.
Source: HRS Lemma 4.1 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
abbrev A (U : C) : CommRingCat.{u + 1} := (ringSheaf J O).obj.obj (op U)

/-- The constant-section homomorphism is the actual constant-sheaf adjunction counit.
Source: HRS (3.2) (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def scalarMap (U : C) (hU : IsTerminal U) : realizationRing J (A J O U) ⟶ ringSheaf J O :=
  (constantSheafAdj J CommRingCat.{u + 1} hU).counit.app (ringSheaf J O)

/-- The standard localization size for modules over the constant coefficient sheaf.
Source: Stacks 05RU (blueprint: def-zl-condensed-lisse-evaluation-model). -/
instance constantHasDerived (U : C) :
    HasDerivedCategory.{u + 2} (realizationModules J (A J O U)) :=
  HasDerivedCategory.standard _

/-- The standard localization size for sectionwise coefficient modules.
Source: Stacks 05RU (blueprint: def-zl-condensed-lisse-evaluation-model). -/
instance sectionHasDerived : HasDerivedCategory.{u + 2}
    (SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ringSheaf J O))) := HasDerivedCategory.standard _

/-- The universal derived coefficient extension, with its fixed K-flat counit.
Source: HRS (3.2), Stacks 06YY
(blueprint: def-zl-condensed-lisse-evaluation-model). -/
def extensionModel (U : C) (hU : IsTerminal U) :=
  SheafOfModules.canonicalDerivedChangeOfRingsModel (scalarMap J O U hU)

/-- The canonical functor Q ↦ O tensor over constant A with constant Q.
Source: HRS (3.2) and Remark 3.2
(blueprint: def-zl-condensed-lisse-evaluation-model). -/
def F (U : C) (hU : IsTerminal U) :
    DerivedCategory (ModuleCat.{u + 1} (A J O U)) ⥤ D J O :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  letI := Functor.additive_of_preserves_binary_products e.inverse
  commutativeSiteDerivedConstantModuleFunctor J (A J O U) ⋙
    (extensionModel J O U hU).T ⋙ e.inverse.mapDerivedCategory

/-- Actual module evaluation after the sectionwise/internal equivalence.
Source: HRS Lemma 4.1 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def sections (U : C) : Mod (Sheaf J Ab.{u + 1}) O ⥤ ModuleCat.{u + 1} (A J O U) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O).functor ⋙
    SheafOfModules.evaluation _ (op U)

/-- Module evaluation is additive because it preserves sums of maps on every section.
Source: HRS Section 3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
instance sectionsAdditive (U : C) : (sections J O U).Additive :=
  letI := Functor.additive_of_preserves_binary_products
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O).functor
  letI : (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (ringSheaf J O)) (op U)).Additive :=
    inferInstanceAs ((SheafOfModules.forget _ ⋙
      PresheafOfModules.evaluation _ (op U))).Additive
  inferInstanceAs ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    J O).functor ⋙ SheafOfModules.evaluation _ (op U)).Additive

/-- Derived global sections are the right derived functor of actual module evaluation.
Source: HRS Lemma 4.1 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def G (U : C) : D J O ⥤ DerivedCategory (ModuleCat.{u + 1} (A J O U)) :=
  (sections J O U).rightDerivedFunctor

/-- The full subcategory of dualizable objects, using both triangle identities.
Source: HRS Definition 3.3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def lisse : ObjectProperty (D J O) := fun K ↦ IsDualizable K

/-- The full subcategory defined by bounded finite projective representatives.
Source: HRS Lemma 4.1 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def perfect (U : C) : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} (A J O U))) :=
  fun Q ↦ DerivedCategory.IsPerfectRingComplex Q

/-- Preservation of the ordinary Koszul braiding by the strong monoidal realization.
Source: HRS (3.1) (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def strongSymmetric (U : C) (hU : IsTerminal U) : Prop :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u + 1} (A J O U))
  letI := DerivedCategory.braidedCategory' (Mod (Sheaf J Ab.{u + 1}) O)
  Nonempty (F J O U hU).Braided

/-- The complete evaluation claim on the fixed canonical functors. Exact means
triangulated; it imposes no t-exactness. Both natural identifications specify the
restriction of F and its inverse G on the two actual full subcategories.
Source: HRS Lemma 4.1(1)--(2)
(blueprint: def-zl-condensed-lisse-evaluation-model). -/
def Statement (U : C) (hU : IsTerminal U) : Prop :=
  Nonempty (F J O U hU).FullyFaithful ∧
  (∃ (_ : (F J O U hU).CommShift ℤ), (F J O U hU).IsTriangulated) ∧
  strongSymmetric J O U hU ∧
  ∃ e : (perfect J O U).FullSubcategory ≌ (lisse J O).FullSubcategory,
    Nonempty (e.functor ⋙ (lisse J O).ι ≅ (perfect J O U).ι ⋙ F J O U hU) ∧
    Nonempty (e.inverse ⋙ (perfect J O U).ι ≅ (lisse J O).ι ⋙ G J O U)

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Pull a point scalar to the affine terminal object using the monoidal inverse image.
This is a construction on the underlying abelian sheaves, not a chosen ring homomorphism.
Source: HRS (3.1)--(3.2), Remark 3.2
(blueprint: def-zl-condensed-lisse-evaluation-model). -/
def affineScalarSection (T : Scheme.{u}) (r : condensedScalarRing Λ) :
    Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ T)
      (Scheme.ProEt.mk (𝟙 T)) :=
  let rmap : 𝟙_ Ab.{u + 1} ⟶ Λ.obj.obj (op (⊤_ Profinite.{u})) :=
    AddCommGrpCat.ofHom
      (((AddMonoidHom.mulRight r).comp (Int.castAddHom (condensedScalarRing Λ))).comp
        AddEquiv.ulift.toAddMonoidHom)
  let s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ :=
    ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      terminalIsTerminal).homEquiv (𝟙_ Ab.{u + 1}) Λ).symm rmap
  let t : 𝟙_ (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ⟶ condensedRingObj Λ T :=
    Functor.LaxMonoidal.ε (upperStarFromPoint T) ≫ (upperStarFromPoint T).map s
  (t.hom.app (op (Scheme.ProEt.mk (𝟙 T))))
    ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app
        (op (Scheme.ProEt.mk (𝟙 T))) (ULift.up 1))

/-- Restriction to the genuine profinite slice site, with finite jointly surjective covers.
Source: HRS Section 3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
abbrev profiniteCoefficient (S : Profinite.{u}) :=
  ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).obj Λ

/-- The restricted coefficient multiplication and unit are induced by restriction.
Source: HRS Section 3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
instance profiniteCoefficientMon (S : Profinite.{u}) : MonObj (profiniteCoefficient Λ S) :=
  ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).monObjObj Λ

/-- Restriction preserves commutativity of the condensed ring.
Source: HRS Section 3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
instance profiniteCoefficientComm (S : Profinite.{u}) :
    IsCommMonObj (profiniteCoefficient Λ S) :=
  Functor.isCommMonObj_obj

/-- The ring of sections of the restricted coefficient is canonically Λ(S).
The comparison uses the monoidal restriction isomorphism, preserving multiplication and unit.
Source: HRS Section 3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def profiniteSectionRingIso (S : Profinite.{u}) :
    (condensedSectionRing Λ).obj.obj (op S) ≅
      Evaluation.A ((coherentTopology Profinite.{u}).over S)
        (profiniteCoefficient Λ S) (Over.mk (𝟙 S)) := by
  let J := coherentTopology Profinite.{u}
  let e := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    (Over.forget S) Ab.{u + 1} (J.over S) J
  let z := ((Functor.mapCommMonCompIso (F := sheafToPresheaf J Ab.{u + 1})
      (G := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj (Over.forget S).op)).symm ≪≫
    Functor.mapCommMonNatIso e ≪≫
    Functor.mapCommMonCompIso (F := J.overPullback Ab.{u + 1} S)
      (G := sheafToPresheaf (J.over S) Ab.{u + 1})).app (CommMon.mk Λ)
  let w := (Monoidal.commMonFunctorCategoryEquivalence (Over S)ᵒᵖ Ab.{u + 1}).functor.mapIso z
  exact InternalAbelianSheafModule.commMonToRing.mapIso (w.app (op (Over.mk (𝟙 S))))

/-- The scalar restriction R → Γ(S,Λ) is restriction along the unique map S → *.
Source: HRS Section 3 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def profiniteScalarMap (S : Profinite.{u}) : condensedScalarRing Λ →+*
    Evaluation.A ((coherentTopology Profinite.{u}).over S)
      (profiniteCoefficient Λ S) (Over.mk (𝟙 S)) :=
  ((condensedSectionRing Λ).obj.map (terminal.from S).op ≫
    (profiniteSectionRingIso Λ S).hom).hom

/-- Realization from R on the profinite slice uses restriction of the actual realization
on the point. All module operations are induced by the coefficient inverse image.
Source: HRS Definition 3.5 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def profiniteScalarRealization (S : Profinite.{u}) :
    DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) ⥤
      Evaluation.D ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ S) :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ
  letI := Functor.additive_of_preserves_binary_products e.inverse
  let f := ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).mapMod Λ
  letI := Functor.additive_of_preserves_binary_products f
  commutativeSiteDerivedConstantModuleFunctor (coherentTopology Profinite.{u})
      (condensedScalarRing Λ) ⋙
    (condensedScalarExtensionModel Λ).T ⋙ e.inverse.mapDerivedCategory ⋙ f.mapDerivedCategory

/-- The natural scalar associativity formula on a profinite slice, on all unbounded complexes.
Source: HRS Remark 3.2 (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def profiniteScalarClause (S : Profinite.{u}) : Prop :=
  Nonempty (profiniteScalarRealization Λ S ≅
    RingDerivedScalarExtension.moduleDerivedExtension (profiniteScalarMap Λ S) ⋙
      Evaluation.F ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ S)
        (Over.mk (𝟙 S)) Over.mkIdTerminal)

/-- The relative test functor characterized by the recorded component universal property.
Its value and all projections are unique up to their unique compatible isomorphism.
Source: HRS (4.1) (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def componentTests (T : Scheme.{u}) [IsAffine T] :
    Over (affineComponentSpace T) ⥤ T.ProEt :=
  Classical.choose (component_relative_profinite_site T)

/-- The actual inverse image: left Kan extension along the relative tests and sheafification.
Source: HRS (4.1) (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def componentInverse (T : Scheme.{u}) [IsAffine T]
    [(componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T)] :
    Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback (componentTests T) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)

section ComponentPullback

variable (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

/-- Coefficient transport is restriction along the inverse of the specified ring isomorphism.
Source: HRS Proposition 4.3(3)
(blueprint: def-zl-condensed-lisse-evaluation-model). -/
abbrev componentModules
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) :
    Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1})
      (profiniteCoefficient Λ (affineComponentSpace T)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) :=
  (componentInverse T).mapMod (profiniteCoefficient Λ (affineComponentSpace T)) ⋙
    Mod.comap α.inv.hom

/-- The component module pullback is additive, being exact on its underlying abelian sheaves.
Source: HRS (4.1) (blueprint: def-zl-condensed-lisse-evaluation-model). -/
instance componentModulesAdditive
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) : (componentModules Λ T α).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The component inverse image on ordinary unbounded derived categories is induced termwise.
Source: HRS (4.1) (blueprint: def-zl-condensed-lisse-evaluation-model). -/
def componentDerived
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) :
    Evaluation.D ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T)) ⥤
      Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ T) :=
  (componentModules Λ T α).mapDerivedCategory

/-- The symmetric monoidal assertion refers to the ordinary Koszul derived braidings.
Source: HRS Proposition 4.3(3)
(blueprint: def-zl-condensed-lisse-evaluation-model). -/
def componentSymmetric
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) : Prop :=
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1})
      (profiniteCoefficient Λ (affineComponentSpace T)))
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
  Nonempty (componentDerived Λ T α).Braided

/-- The actual pullback induces the lisse equivalence and commutes with section-ring
realization after scalar transport along the coefficient comparison. The section-ring
isomorphism preserves the point scalar map, with the latter computed by monoidal pullback
of the corresponding map from the abelian unit and evaluation on the terminal object.
Source: HRS Proposition 4.3(3)
(blueprint: def-zl-condensed-lisse-evaluation-model). -/
def componentComparisons
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) : Prop :=
  (∃ (_ : (componentDerived Λ T α).CommShift ℤ),
    (componentDerived Λ T α).IsTriangulated) ∧
  componentSymmetric Λ T α ∧
  Nonempty ((componentDerived Λ T α).obj
      (𝟙_ (Evaluation.D ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T)))) ≅
    𝟙_ (Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ T))) ∧
  (∃ e : (Evaluation.lisse
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T))).FullSubcategory ≌
      (Evaluation.lisse (Scheme.ProEt.topology T) (condensedRingObj Λ T)).FullSubcategory,
    Nonempty (e.functor ⋙ (Evaluation.lisse (Scheme.ProEt.topology T)
        (condensedRingObj Λ T)).ι ≅
      (Evaluation.lisse ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))).ι ⋙ componentDerived Λ T α)) ∧
  ∃ a : Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T)) (Over.mk (𝟙 (affineComponentSpace T))) ≅
      Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ T) (Scheme.ProEt.mk (𝟙 T)),
    (∀ r : condensedScalarRing Λ,
      a.hom.hom (profiniteScalarMap Λ (affineComponentSpace T) r) =
        affineScalarSection Λ T r) ∧
    Nonempty (Evaluation.F ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))
        (Over.mk (𝟙 (affineComponentSpace T))) Over.mkIdTerminal ⋙ componentDerived Λ T α ≅
      RingDerivedScalarExtension.moduleDerivedExtension a.hom.hom ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T)) (MorphismProperty.Over.mkIdTerminal
            @AlgebraicGeometry.WeaklyEtale T)) ∧
    Nonempty (profiniteScalarRealization Λ (affineComponentSpace T) ⋙ componentDerived Λ T α ≅
      condensedScalarRealization Λ T) ∧
    Nonempty (condensedScalarRealization Λ T ≅
      RingDerivedScalarExtension.moduleDerivedExtension
          (a.hom.hom.comp (profiniteScalarMap Λ (affineComponentSpace T))) ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T))
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T))

end ComponentPullback

/-- All structure asserted here is on the fixed relative-test inverse image, not on an
auxiliary functor. The coefficient isomorphism is an isomorphism of ring objects.
Source: HRS (4.1) and Proposition 4.3(3)
(blueprint: def-zl-condensed-lisse-evaluation-model). -/
def componentClause (T : Scheme.{u}) [IsAffine T] : Prop :=
  ∃ (_ : (componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T)),
    ∃ (_ : (componentInverse T).Braided)
      (_ : PreservesFiniteLimits (componentInverse T))
      (_ : PreservesFiniteColimits (componentInverse T)),
      ∃ α : (componentInverse T).mapMon.obj
          (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
          Mon.mk (condensedRingObj Λ T),
        (∃ β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
              (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T,
          NatTrans.IsMonoidal β.hom ∧ α.hom.hom = β.hom.app Λ) ∧
        componentComparisons Λ T α

end AlgebraicGeometry.ProEtale.CondensedRing
