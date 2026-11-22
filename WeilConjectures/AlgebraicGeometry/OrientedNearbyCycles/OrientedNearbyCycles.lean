/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.OrientedProduct.OrientedProductUniversal
public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite

/-!
# The vanishing site of a morphism of schemes

## Main definitions

* `EtaleSite`, `etaleMorphism`: the transported small étale sites and their base-change morphisms.
* `VanishingSite`, `vanishingTopology`, `VanishingTopos`: the oriented-product vanishing site.
* `etaleDatum`, `vanishingDatum`, `moduleMorphism`: the constant-coefficient module data.

The étale sites are transported through `AsSmall.equiv`. This changes neither
coverings nor the associated topoi and accommodates independent scheme/coefficient sizes.

## References

* Illusie--Laszlo--Orgogozo, Exposé XI §§1.1--1.7, 1.9, 4.1--4.3
* Illusie, Around the Thom--Sebastiani theorem, §§1.4--1.5, 2.1
* ILO XI §4.3
* ILO XI §1.1, §4.3
* ILO XI §1.1(ii), §4.3
* ILO XI §1.7, §4.3
* ILO XI §1.3, §4.3
* ILO XI §1.3
* ILO XI Lemma 1.2(ii)
* ILO XI §1.3, Theorem 1.4
* ILO XI Theorem 1.4
* ILO XI §1.1
* ILO XI §4.3 (4.b)
* ILO XI §1.9
* ILO XI §1.9, §4.3
* ILO XI Theorem 1.4, §1.9, §4.3
* ILO XI §4.1
* Stacks 03D2
* ILO XI §4.1, §4.3
* Stacks 079P
* Illusie §1.4
* Stacks 06YS, 06YT
* Stacks 03EL, 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v s

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- The small étale site presented in a common universe by Mathlib's equivalence. -/
abbrev EtaleSite (X : Scheme.{u}) := AsSmall.{v} X.Etale

/-- The transported étale topology, using Mathlib's induced topology. -/
def etaleTopology (X : Scheme.{u}) : GrothendieckTopology (EtaleSite.{u, v} X) :=
  (AsSmall.down : EtaleSite.{u, v} X ⥤ X.Etale).inducedTopology X.smallEtaleTopology

/-- The transported small étale site has finite limits. -/
theorem etaleSite_hasFiniteLimits (X : Scheme.{u}) :
    HasFiniteLimits (EtaleSite.{u, v} X) :=
  ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence
    (AsSmall.equiv (C := X.Etale)).inverse⟩

attribute [instance] etaleSite_hasFiniteLimits

/-- The actual scheme-theoretic base-change functor on the transported small étale sites. -/
def etaleBaseChange {T B : Scheme.{u}} (f : T ⟶ B) :
    EtaleSite.{u, v} B ⥤ EtaleSite.{u, v} T :=
  AsSmall.down ⋙ MorphismProperty.Over.pullback @Etale ⊤ f ⋙ AsSmall.up

/-- Base change preserves finite limits on the étale sites. -/
theorem etaleBaseChange_preservesFiniteLimits {T B : Scheme.{u}} (f : T ⟶ B) :
    PreservesFiniteLimits (etaleBaseChange.{u, v} f) := by
  have : PreservesFiniteLimits (AsSmall.down : EtaleSite.{u, v} B ⥤ B.Etale) :=
    inferInstanceAs (PreservesFiniteLimits (AsSmall.equiv (C := B.Etale)).inverse)
  have : PreservesFiniteLimits (AsSmall.up : T.Etale ⥤ EtaleSite.{u, v} T) :=
    inferInstanceAs (PreservesFiniteLimits (AsSmall.equiv (C := T.Etale)).functor)
  have : PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f) := inferInstance
  exact comp_preservesFiniteLimits _ _

attribute [instance] etaleBaseChange_preservesFiniteLimits

/-- Base change is continuous for the transported étale topologies. -/
theorem etaleBaseChange_isContinuous {T B : Scheme.{u}} (f : T ⟶ B) :
    (etaleBaseChange.{u, v} f).IsContinuous (etaleTopology B) (etaleTopology T) := by
  have : (AsSmall.down : EtaleSite.{u, v} B ⥤ B.Etale).IsContinuous (etaleTopology B)
      B.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.equiv (C := B.Etale)).inverse.IsContinuous
      ((AsSmall.equiv (C := B.Etale)).inverse.inducedTopology B.smallEtaleTopology)
      B.smallEtaleTopology)
  have : (AsSmall.up : T.Etale ⥤ EtaleSite.{u, v} T).IsContinuous T.smallEtaleTopology
      (etaleTopology T) :=
    inferInstanceAs ((AsSmall.equiv (C := T.Etale)).functor.IsContinuous T.smallEtaleTopology
      ((AsSmall.equiv (C := T.Etale)).inverse.inducedTopology T.smallEtaleTopology))
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous B.smallEtaleTopology
      T.smallEtaleTopology :=
    Scheme.isContinuous_overPullback (P := @Etale) (Q := @Etale) le_rfl f
  have := Functor.isContinuous_comp (MorphismProperty.Over.pullback @Etale ⊤ f) AsSmall.up
    B.smallEtaleTopology T.smallEtaleTopology (etaleTopology T)
  exact Functor.isContinuous_comp AsSmall.down
    (MorphismProperty.Over.pullback @Etale ⊤ f ⋙ AsSmall.up) (etaleTopology B)
    B.smallEtaleTopology (etaleTopology T)

attribute [instance] etaleBaseChange_isContinuous

/-- The geometric morphism associated to a continuous finite-limit-preserving site functor.
The inverse image is Mathlib's left adjoint; its universal property fixes the construction. -/
def siteMorphism {C D : Type s} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [PreservesFiniteLimits F] :
    GeometricMorphism (Sheaf K (Type s)) (Sheaf J (Type s)) where
  inverse := F.sheafPullback (Type s) J K
  direct := F.sheafPushforwardContinuous (Type s) J K
  adj := F.sheafAdjunctionContinuous (Type s) J K
  leftExact :=
    letI : RepresentablyFlat F := flat_of_preservesFiniteLimits F
    Functor.sheafPullbackConstruction.preservesFiniteLimits F (Type s) J K

/-- A scheme morphism on the étale topoi, with its actual base-change inverse image. -/
def etaleMorphism {T B : Scheme.{u}} (f : T ⟶ B) :=
  siteMorphism (etaleTopology.{u, v} B) (etaleTopology T) (etaleBaseChange f)

/-- The vanishing site's underlying category: exactly the oriented-product triples. -/
abbrev VanishingSite {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.Triples (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- Its three types of covering generators, via the recorded oriented-product construction. -/
def vanishingTopology {T B : Scheme.{u}} (f : T ⟶ B) :
    GrothendieckTopology (VanishingSite.{u, v} f) :=
  OrientedProduct.topology (etaleTopology T).toPretopology
    (etaleTopology B).toPretopology (etaleBaseChange f) (𝟭 _)

/-- The actual topos of sheaves on the vanishing site. -/
abbrev VanishingTopos {T B : Scheme.{u}} (f : T ⟶ B) :=
  Sheaf (vanishingTopology.{u, v} f) (Type (max (u + 1) v))

/-- The first projection's site functor from the recorded oriented product. -/
abbrev first {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.first (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- The second projection's site functor from the recorded oriented product. -/
abbrev second {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.second (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- The identity geometric morphism, with the identity adjunction. -/
def identity (E : Type (s + 1)) [Category.{s} E] : GeometricMorphism E E :=
  ⟨𝟭 E, 𝟭 E, Adjunction.id, inferInstance⟩

/-- A type-(c) covering becomes invertible in every sheaf. -/
theorem map_toFirst_isIso {T B : Scheme.{u}} (f : T ⟶ B)
    (H : VanishingTopos.{u, v} f) (V : EtaleSite.{u, v} B) :
    IsIso (H.obj.map (OrientedProduct.toFirst (etaleBaseChange f) (𝟭 _)
      (OrientedProduct.middle (etaleBaseChange f) (𝟭 _) V)).op) := by
  sorry

attribute [instance] map_toFirst_isIso

/-- A sheaf category is a topos, using its actual small-site presentation. -/
theorem sheaf_isTopos {C : Type s} [SmallCategory C] (J : GrothendieckTopology C) :
    IsGrothendieckTopos.{s} (Sheaf J (Type s)) :=
  ⟨C, inferInstance, J, ⟨CategoryTheory.Equivalence.refl⟩⟩

/-- Base-change associativity transported through the two `AsSmall` equivalences. -/
def etaleBaseChangeComp {T' T B : Scheme.{u}} (h : T' ⟶ T) (f : T ⟶ B) :
    etaleBaseChange.{u, v} (h ≫ f) ≅ etaleBaseChange f ⋙ etaleBaseChange h :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft AsSmall.down (MorphismProperty.Over.pullbackComp h f))
    AsSmall.up

/-- Composition of étale direct images, with the canonical fibre-product comparison. -/
def etaleComposition {T' T B : Scheme.{u}} (h : T' ⟶ T) (f : T ⟶ B) :
    ((etaleMorphism.{u, v} h).comp (etaleMorphism f)).direct ≅
      (etaleMorphism (h ≫ f)).direct :=
  letI := Functor.isContinuous_comp (etaleBaseChange.{u, v} f) (etaleBaseChange h)
    (etaleTopology B) (etaleTopology T) (etaleTopology T')
  (etaleBaseChange f).sheafPushforwardContinuousComp (etaleBaseChange h)
      (Type (max (u + 1) v)) (etaleTopology B) (etaleTopology T) (etaleTopology T') ≪≫
    Functor.sheafPushforwardContinuousIso (etaleBaseChangeComp h f).symm
      (Type (max (u + 1) v)) (etaleTopology B) (etaleTopology T')

/-- The set-topos commutation identification of a scheme square. -/
def squareDirect {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    ((etaleMorphism.{u, v} h).comp (etaleMorphism f)).direct ≅
      ((etaleMorphism f').comp (etaleMorphism g)).direct :=
  etaleComposition h f ≪≫ eqToIso (congrArg
    (fun k : T' ⟶ B ↦ (etaleMorphism.{u, v} k).direct) comm) ≪≫
      (etaleComposition f' g).symm

open CategoryTheory.AdicSites CategoryTheory.ConstantCompletion

/-- The transported étale site as the existing small-site datum. -/
def etaleDatum (X : Scheme.{u}) : Site.{max (u + 1) v} :=
  ⟨EtaleSite X, etaleTopology X⟩

/-- The concrete oriented triple site as the existing small-site datum. -/
def vanishingDatum {T B : Scheme.{u}} (f : T ⟶ B) : Site.{max (u + 1) v} :=
  ⟨VanishingSite f, vanishingTopology f⟩

/-- Lift a geometric inverse image to constant-coefficient modules by transporting all
algebraic operations, using the existing canonical constant-object identification. -/
def moduleMorphism (V U : Site.{s})
    (f : GeometricMorphism (Sheaf U.topology (Type s)) (Sheaf V.topology (Type s))) :
    Morphism V U :=
  letI := f.leftExact
  { inverse := f.inverse
    direct := f.direct
    adjunction := f.adj
    algebra := (inverseImageData_exists f.inverse f.direct f.adj).some }

/-- Universe transport of an arbitrary coefficient ring, along the canonical ring equivalence. -/
abbrev Coeff (Λ : Type v) [CommRing Λ] := ULift.{u + 1} Λ

/-- Unbounded derived étale module sheaves over the constant coefficient ring. -/
abbrev EtaleDerived (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] :=
  (etaleDatum.{u, v} X).derived (Coeff.{u, v} Λ)

/-- Unbounded derived module sheaves on the vanishing topos. -/
abbrev VanishingDerived {T B : Scheme.{u}} (f : T ⟶ B) (Λ : Type v) [CommRing Λ] :=
  (vanishingDatum.{u, v} f).derived (Coeff.{u, v} Λ)

/-- The exact module inverse image attached to a scheme morphism. -/
def etaleModules {T B : Scheme.{u}} (f : T ⟶ B) :=
  moduleMorphism (etaleDatum.{u, v} B) (etaleDatum T) (etaleMorphism f)

/-- The already localized K-flat tensor on a constant-coefficient ringed site. -/
abbrev derivedTensor (S : Site.{s}) (A : Type s) [CommRing A] :
    S.derived A × S.derived A ⥤ S.derived A :=
  SheafOfModules.wfSiteDerivedTensor S.topology (S.ring A)

/-- The existing ringed tensor corner for this very tensor functor. -/
def tensorCorner (S : Site.{s}) (A : Type s) [CommRing A] :
    SheafOfModules.RingedTensorCorner :=
  { site := S.objects
    topology := S.topology
    ring := S.ring A
    derived := Site.hasDerived S A
    tensor := derivedTensor S A }

/-- The precise flat-term K-flat representative subcategory. -/
def flatRepresentatives (S : Site.{s}) (A : Type s) [CommRing A] :
    ObjectProperty (CochainComplex (S.modules A) ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

/-- Localization of both flat-term K-flat arguments. -/
def tensorInput (S : Site.{s}) (A : Type s) [CommRing A] :=
  ((flatRepresentatives S A).ι ⋙ DerivedCategory.Q).prod
    ((flatRepresentatives S A).ι ⋙ DerivedCategory.Q)

end AlgebraicGeometry.OrientedNearbyCycles
