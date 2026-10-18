/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductUniversal
public import Sheaf.Paper.CompletionMateComparison
public import Sheaf.Paper.RingedTensorSquarePresentation
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Paper.WeilTensorProduct
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite

/-!
# Oriented nearby cycles and their canonical comparison maps

Source: Illusie--Laszlo--Orgogozo, Exposé XI §§1.1--1.7, 1.9, 4.1--4.3;
Illusie, Around the Thom--Sebastiani theorem, §§1.4--1.5, 2.1
(blueprint: def-trf-oriented-nearby-cycles).

## Main definitions

* `VanishingTopos`, `p₁`, `p₂`, `orientation`, `psi`: the concrete oriented construction.
* `nearbyCycles`, `baseChange`, `IsPsiGood`: unbounded nearby cycles and base change.
* `laxTensor`, `externalEtale`, `externalVanishing`, `kunneth`: the specified tensor maps.

The étale sites are transported through `AsSmall.equiv`. This changes neither
coverings nor the associated topoi and accommodates independent scheme/coefficient sizes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v s

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- The small étale site presented in a common universe by Mathlib's equivalence.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev EtaleSite (X : Scheme.{u}) := AsSmall.{v} X.Etale

/-- The transported étale topology, using Mathlib's induced topology.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def etaleTopology (X : Scheme.{u}) : GrothendieckTopology (EtaleSite.{u, v} X) :=
  (AsSmall.down : EtaleSite.{u, v} X ⥤ X.Etale).inducedTopology X.smallEtaleTopology

/-- The transported small étale site has finite limits.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles).
Proof: transport the finite limits of `Scheme.Etale` along `AsSmall.equiv`.
The equivalence identifies their cones and their universal properties. -/
theorem etaleSite_hasFiniteLimits (X : Scheme.{u}) :
    HasFiniteLimits (EtaleSite.{u, v} X) := by
  sorry

attribute [instance] etaleSite_hasFiniteLimits

/-- The actual scheme-theoretic base-change functor on the transported small étale sites.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def etaleBaseChange {T B : Scheme.{u}} (f : T ⟶ B) :
    EtaleSite.{u, v} B ⥤ EtaleSite.{u, v} T :=
  AsSmall.down ⋙ MorphismProperty.Over.pullback @Etale ⊤ f ⋙ AsSmall.up

/-- Base change preserves finite limits on the étale sites.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles).
Proof: scheme fibre products commute with finite limits in the slice. The equivalences
`AsSmall.equiv` preserve those limits. -/
theorem etaleBaseChange_preservesFiniteLimits {T B : Scheme.{u}} (f : T ⟶ B) :
    PreservesFiniteLimits (etaleBaseChange.{u, v} f) := by
  sorry

attribute [instance] etaleBaseChange_preservesFiniteLimits

/-- Base change is continuous for the transported étale topologies.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles).
Proof: base change preserves étale morphisms and jointly surjective families. Thus it
preserves the generating étale covers; finite-limit preservation gives continuity.
Transport the covers through `AsSmall.equiv`. -/
theorem etaleBaseChange_isContinuous {T B : Scheme.{u}} (f : T ⟶ B) :
    (etaleBaseChange.{u, v} f).IsContinuous (etaleTopology B) (etaleTopology T) := by
  sorry

attribute [instance] etaleBaseChange_isContinuous

/-- The geometric morphism associated to a continuous finite-limit-preserving site functor.
The inverse image is Mathlib's left adjoint; its universal property fixes the construction.
Source: ILO XI §1.1, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
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

/-- A scheme morphism on the étale topoi, with its actual base-change inverse image.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def etaleMorphism {T B : Scheme.{u}} (f : T ⟶ B) :=
  siteMorphism (etaleTopology.{u, v} B) (etaleTopology T) (etaleBaseChange f)

/-- The vanishing site's underlying category: exactly the oriented-product triples.
Source: ILO XI §1.1, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev VanishingSite {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.Triples (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- Its three types of covering generators, via the recorded oriented-product construction.
Source: ILO XI §1.1(ii), §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def vanishingTopology {T B : Scheme.{u}} (f : T ⟶ B) :
    GrothendieckTopology (VanishingSite.{u, v} f) :=
  OrientedProduct.topology (etaleTopology T).toPretopology
    (etaleTopology B).toPretopology (etaleBaseChange f) (𝟭 _)

/-- The actual topos of sheaves on the vanishing site.
Source: ILO XI §1.7, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev VanishingTopos {T B : Scheme.{u}} (f : T ⟶ B) :=
  Sheaf (vanishingTopology.{u, v} f) (Type (max (u + 1) v))

/-- The first projection's site functor from the recorded oriented product.
Source: ILO XI §1.3, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev first {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.first (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- The second projection's site functor from the recorded oriented product.
Source: ILO XI §1.3, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev second {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.second (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- The projection site functors are continuous and preserve finite limits.
Source: ILO XI §1.3 (blueprint: def-trf-oriented-nearby-cycles).
Proof: finite limits are componentwise in the triple category. The first two
covering generators contain the images of the corresponding étale covering families.
Thus the two projection functors preserve finite limits and covers. -/
theorem projection_properties {T B : Scheme.{u}} (f : T ⟶ B) :
    (first.{u, v} f).IsContinuous (etaleTopology T) (vanishingTopology f) ∧
    PreservesFiniteLimits (first.{u, v} f) ∧
    (second.{u, v} f).IsContinuous (etaleTopology B) (vanishingTopology f) ∧
    PreservesFiniteLimits (second.{u, v} f) := by
  sorry

/-- Continuity of the first projection's site functor.
Source: ILO XI §1.3 (blueprint: def-trf-oriented-nearby-cycles). -/
instance first_continuous {T B : Scheme.{u}} (f : T ⟶ B) :
    (first.{u, v} f).IsContinuous (etaleTopology T) (vanishingTopology f) :=
  (projection_properties f).1

/-- Finite-limit preservation of the first projection's site functor.
Source: ILO XI §1.3 (blueprint: def-trf-oriented-nearby-cycles). -/
instance first_finiteLimits {T B : Scheme.{u}} (f : T ⟶ B) :
    PreservesFiniteLimits (first.{u, v} f) := (projection_properties f).2.1

/-- Continuity of the second projection's site functor.
Source: ILO XI §1.3 (blueprint: def-trf-oriented-nearby-cycles). -/
instance second_continuous {T B : Scheme.{u}} (f : T ⟶ B) :
    (second.{u, v} f).IsContinuous (etaleTopology B) (vanishingTopology f) :=
  (projection_properties f).2.2.1

/-- Finite-limit preservation of the second projection's site functor.
Source: ILO XI §1.3 (blueprint: def-trf-oriented-nearby-cycles). -/
instance second_finiteLimits {T B : Scheme.{u}} (f : T ⟶ B) :
    PreservesFiniteLimits (second.{u, v} f) := (projection_properties f).2.2.2

/-- The first projection from the actual vanishing topos.
Source: ILO XI §1.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def p₁ {T B : Scheme.{u}} (f : T ⟶ B) :=
  siteMorphism (etaleTopology.{u, v} T) (vanishingTopology f) (first f)

/-- The second projection from the actual vanishing topos.
Source: ILO XI §1.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def p₂ {T B : Scheme.{u}} (f : T ⟶ B) :=
  siteMorphism (etaleTopology.{u, v} B) (vanishingTopology f) (second f)

/-- The identity geometric morphism, with the identity adjunction.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def identity (E : Type (s + 1)) [Category.{s} E] : GeometricMorphism E E :=
  ⟨𝟭 E, 𝟭 E, Adjunction.id, inferInstance⟩

/-- A type-(c) covering becomes invertible in every sheaf.
Source: ILO XI Lemma 1.2(ii) (blueprint: def-trf-oriented-nearby-cycles).
Proof: its covering diagonal equalizes its two pullback projections. The sheaf
condition therefore makes the restriction bijective, hence invertible in `Type`. -/
theorem map_toFirst_isIso {T B : Scheme.{u}} (f : T ⟶ B)
    (H : VanishingTopos.{u, v} f) (V : EtaleSite.{u, v} B) :
    IsIso (H.obj.map (OrientedProduct.toFirst (etaleBaseChange f) (𝟭 _)
      (OrientedProduct.middle (etaleBaseChange f) (𝟭 _) V)).op) := by
  sorry

attribute [instance] map_toFirst_isIso

/-- The orientation is uniquely fixed by the two restriction maps of ILO XI §1.3.
It has the universal property of the recorded oriented-product theorem.
Source: ILO XI §1.3, Theorem 1.4 (blueprint: def-trf-oriented-nearby-cycles).
Proof: on a sheaf H the component is restriction to the middle triple followed by
inverse restriction to the first triple. Lemma 1.2 makes the latter invertible.
Restrictions commute with all site and sheaf maps, giving naturality and uniqueness.
Theorem 1.4 (lem-trf-oriented-product-universal) gives its universal property. -/
theorem orientation_existsUnique {T B : Scheme.{u}} (f : T ⟶ B) :
    ∃! τ : ((p₂.{u, v} f).comp (identity (Sheaf (etaleTopology B)
        (Type (max (u + 1) v))))).direct ⟶ ((p₁ f).comp (etaleMorphism f)).direct,
      (∀ (H : VanishingTopos.{u, v} f) (V : EtaleSite.{u, v} B),
        (τ.app H).hom.app (op V) =
          H.obj.map (OrientedProduct.toSecond (etaleBaseChange f) (𝟭 _)
            (OrientedProduct.middle (etaleBaseChange f) (𝟭 _) V)).op ≫
          inv (H.obj.map (OrientedProduct.toFirst (etaleBaseChange f) (𝟭 _)
            (OrientedProduct.middle (etaleBaseChange f) (𝟭 _) V)).op)) ∧
      OrientedProduct.IsUniversal.{max (u + 1) v, max (u + 1) v + 1, max (u + 1) v}
        (etaleMorphism f) (identity _) (p₁ f) (p₂ f) τ := by
  sorry

/-- The specified orientation, rather than an unspecified 2-morphism.
Source: ILO XI §1.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def orientation {T B : Scheme.{u}} (f : T ⟶ B) :=
  (orientation_existsUnique.{u, v} f).choose

/-- Universal property for the explicitly normalized oriented projections.
Source: ILO XI Theorem 1.4 (blueprint: def-trf-oriented-nearby-cycles).
Proof: the chosen orientation satisfies the second conjunct of the specifying predicate
in orientation_existsUnique. Extract this conjunct from its choice specification. -/
theorem orientation_universal {T B : Scheme.{u}} (f : T ⟶ B) :
    OrientedProduct.IsUniversal.{max (u + 1) v, max (u + 1) v + 1, max (u + 1) v}
      (etaleMorphism f) (identity _) (p₁ f) (p₂ f) (orientation f) := by
  sorry

/-- The coherent lift of a cone to the oriented product, including its identifying maps.
Source: ILO XI Theorem 1.4 (blueprint: def-trf-oriented-nearby-cycles). -/
structure Lift {T B : Scheme.{u}} (f : T ⟶ B)
    (E : Type (max (u + 1) v + 1)) [Category.{max (u + 1) v} E]
    (a : GeometricMorphism E (Sheaf (etaleTopology.{u, v} T) (Type (max (u + 1) v))))
    (b : GeometricMorphism E (Sheaf (etaleTopology.{u, v} B) (Type (max (u + 1) v))))
    (t : (b.comp (identity _)).direct ⟶ (a.comp (etaleMorphism f)).direct) where
  morphism : GeometricMorphism E (VanishingTopos.{u, v} f)
  first : (morphism.comp (p₁ f)).direct ≅ a.direct
  second : (morphism.comp (p₂ f)).direct ≅ b.direct
  compatible : OrientedProduct.paste (etaleMorphism f) (identity _)
    (p₁ f) (p₂ f) (orientation f) morphism a b first second = t

/-- The universal-property lift, not a choice of an unconstrained geometric morphism.
Source: ILO XI Theorem 1.4 (blueprint: def-trf-oriented-nearby-cycles). -/
def lift {T B : Scheme.{u}} (f : T ⟶ B)
    (E : Type (max (u + 1) v + 1)) [Category.{max (u + 1) v} E]
    (hE : IsGrothendieckTopos.{max (u + 1) v} E)
    (a : GeometricMorphism E (Sheaf (etaleTopology.{u, v} T) (Type (max (u + 1) v))))
    (b : GeometricMorphism E (Sheaf (etaleTopology.{u, v} B) (Type (max (u + 1) v))))
    (t : (b.comp (identity _)).direct ⟶ (a.comp (etaleMorphism f)).direct) :
    Lift f E a b t :=
  ⟨((orientation_universal f) E hE a b t).choose,
    ((orientation_universal f) E hE a b t).choose_spec.choose,
    ((orientation_universal f) E hE a b t).choose_spec.choose_spec.choose,
    ((orientation_universal f) E hE a b t).choose_spec.choose_spec.choose_spec.1⟩

/-- A sheaf category is a topos, using its actual small-site presentation.
Source: ILO XI §1.1 (blueprint: def-trf-oriented-nearby-cycles).
Proof: use this site and the identity equivalence in `IsGrothendieckTopos`. -/
theorem sheaf_isTopos {C : Type s} [SmallCategory C] (J : GrothendieckTopology C) :
    IsGrothendieckTopos.{s} (Sheaf J (Type s)) := by
  sorry

/-- The cone `(1_T,f,1_f)` defining the nearby-cycle morphism.
Source: ILO XI §4.3 (4.b) (blueprint: def-trf-oriented-nearby-cycles). -/
def psiLift {T B : Scheme.{u}} (f : T ⟶ B) :
    Lift.{u, v} f _ (identity _) (etaleMorphism f)
      ((Functor.rightUnitor (etaleMorphism.{u, v} f).direct).hom ≫
        (Functor.leftUnitor (etaleMorphism.{u, v} f).direct).inv) :=
  lift f _ (sheaf_isTopos _) (identity _) (etaleMorphism f) _

/-- The canonical nearby-cycle geometric morphism `ψ_f`.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def psi {T B : Scheme.{u}} (f : T ⟶ B) := (psiLift.{u, v} f).morphism

/-- Base-change associativity transported through the two `AsSmall` equivalences.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-nearby-cycles). -/
def etaleBaseChangeComp {T' T B : Scheme.{u}} (h : T' ⟶ T) (f : T ⟶ B) :
    etaleBaseChange.{u, v} (h ≫ f) ≅ etaleBaseChange f ⋙ etaleBaseChange h :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft AsSmall.down (MorphismProperty.Over.pullbackComp h f))
    AsSmall.up

/-- Composition of étale direct images, with the canonical fibre-product comparison.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-nearby-cycles). -/
def etaleComposition {T' T B : Scheme.{u}} (h : T' ⟶ T) (f : T ⟶ B) :
    ((etaleMorphism.{u, v} h).comp (etaleMorphism f)).direct ≅
      (etaleMorphism (h ≫ f)).direct :=
  letI := Functor.isContinuous_comp (etaleBaseChange.{u, v} f) (etaleBaseChange h)
    (etaleTopology B) (etaleTopology T) (etaleTopology T')
  (etaleBaseChange f).sheafPushforwardContinuousComp (etaleBaseChange h)
      (Type (max (u + 1) v)) (etaleTopology B) (etaleTopology T) (etaleTopology T') ≪≫
    Functor.sheafPushforwardContinuousIso (etaleBaseChangeComp h f).symm
      (Type (max (u + 1) v)) (etaleTopology B) (etaleTopology T')

/-- The set-topos commutation identification of a scheme square.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-nearby-cycles). -/
def squareDirect {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    ((etaleMorphism.{u, v} h).comp (etaleMorphism f)).direct ≅
      ((etaleMorphism f').comp (etaleMorphism g)).direct :=
  etaleComposition h f ≪≫ eqToIso (congrArg
    (fun k : T' ⟶ B ↦ (etaleMorphism.{u, v} k).direct) comm) ≪≫
      (etaleComposition f' g).symm

/-- Whisker the orientation by `g`, using precisely the commutation isomorphism of the square.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-nearby-cycles). -/
def squareOrientation {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    (((p₂.{u, v} f').comp (etaleMorphism g)).comp (identity _)).direct ⟶
      (((p₁ f').comp (etaleMorphism h)).comp (etaleMorphism f)).direct :=
  (Functor.rightUnitor _).hom ≫
    (Functor.isoWhiskerRight (Functor.rightUnitor (p₂ f').direct).symm
      (etaleMorphism g).direct).hom ≫
    Functor.whiskerRight (orientation f') (etaleMorphism g).direct ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (p₁ f').direct (squareDirect f f' h g comm).inv ≫
    (Functor.associator _ _ _).inv

/-- The lift inducing `v : V_f' → V_f`, together with its projection identifications.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-nearby-cycles). -/
def squareLift {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :=
  lift.{u, v} f (VanishingTopos f') (sheaf_isTopos _)
    ((p₁ f').comp (etaleMorphism h)) ((p₂ f').comp (etaleMorphism g))
    (squareOrientation f f' h g comm)

/-- The induced morphism of vanishing topoi, for an arbitrary commutative square.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-nearby-cycles). -/
def squareMorphism {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :=
  (squareLift.{u, v} f f' h g comm).morphism

/-- The first projection of the composite `v ψ_f'`, identified with `h`.
Source: ILO XI §1.9, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def squarePsiFirst {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    (((psi.{u, v} f').comp (squareMorphism f f' h g comm)).comp (p₁ f)).direct ≅
      (etaleMorphism h).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (psi f').direct (squareLift f f' h g comm).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (psiLift f').first (etaleMorphism h).direct ≪≫
    Functor.leftUnitor _

/-- The first projection of `ψ_f h`, identified with `h`.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def psiHFirst {T' T B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T) :
    (((etaleMorphism.{u, v} h).comp (psi f)).comp (p₁ f)).direct ≅
      (etaleMorphism h).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleMorphism h).direct (psiLift f).first ≪≫
    Functor.rightUnitor _

/-- The second projection of `v ψ_f'`, identified with `f h`.
Source: ILO XI §1.9, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def squarePsiSecond {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    (((psi.{u, v} f').comp (squareMorphism f f' h g comm)).comp (p₂ f)).direct ≅
      ((etaleMorphism h).comp (etaleMorphism f)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (psi f').direct (squareLift f f' h g comm).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (psiLift f').second (etaleMorphism g).direct ≪≫
    (squareDirect f f' h g comm).symm

/-- The second projection of `ψ_f h`, identified with `f h`.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def psiHSecond {T' T B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T) :
    (((etaleMorphism.{u, v} h).comp (psi f)).comp (p₂ f)).direct ≅
      ((etaleMorphism h).comp (etaleMorphism f)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleMorphism h).direct (psiLift f).second

/-- Universal-property uniqueness gives the projection-compatible square at `ψ`.
Source: ILO XI Theorem 1.4, §1.9, §4.3 (blueprint: def-trf-oriented-nearby-cycles).
Proof: both composites lift `(h,fh,1_fh)`. The identities in `psiLift` and
`squareLift` identify their orientations. Apply the uniqueness clause of
lem-trf-oriented-product-universal; both projection equations below are its equations. -/
theorem squarePsi_existsUnique {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    ∃! e : ((psi.{u, v} f').comp (squareMorphism f f' h g comm)).direct ≅
        ((etaleMorphism h).comp (psi f)).direct,
      Functor.isoWhiskerRight e (p₁ f).direct ≪≫ psiHFirst f h =
          squarePsiFirst f f' h g comm ∧
        Functor.isoWhiskerRight e (p₂ f).direct ≪≫ psiHSecond f h =
          squarePsiSecond f f' h g comm := by
  sorry

/-- The canonical square at the nearby-cycle morphisms, with both projections fixed.
Source: ILO XI §1.9, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def squarePsi {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :=
  (squarePsi_existsUnique.{u, v} f f' h g comm).choose



open CategoryTheory.AdicSites CategoryTheory.ConstantCompletion

/-- The transported étale site as the existing small-site datum.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def etaleDatum (X : Scheme.{u}) : Site.{max (u + 1) v} :=
  ⟨EtaleSite X, etaleTopology X⟩

/-- The concrete oriented triple site as the existing small-site datum.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def vanishingDatum {T B : Scheme.{u}} (f : T ⟶ B) : Site.{max (u + 1) v} :=
  ⟨VanishingSite f, vanishingTopology f⟩

/-- Lift a geometric inverse image to constant-coefficient modules by transporting all
algebraic operations, using the existing canonical constant-object identification.
Source: ILO XI §4.1; Stacks 03D2 (blueprint: def-trf-oriented-nearby-cycles). -/
def moduleMorphism (V U : Site.{s})
    (f : GeometricMorphism (Sheaf U.topology (Type s)) (Sheaf V.topology (Type s))) :
    Morphism V U :=
  letI := f.leftExact
  { inverse := f.inverse
    direct := f.direct
    adjunction := f.adj
    algebra := (inverseImageData_exists f.inverse f.direct f.adj).some }

/-- Universe transport of an arbitrary coefficient ring, along the canonical ring equivalence.
Source: ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev Coeff (Λ : Type v) [CommRing Λ] := ULift.{u + 1} Λ

/-- Unbounded derived étale module sheaves over the constant coefficient ring.
Source: ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev EtaleDerived (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] :=
  (etaleDatum.{u, v} X).derived (Coeff.{u, v} Λ)

/-- Unbounded derived module sheaves on the vanishing topos.
Source: ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev VanishingDerived {T B : Scheme.{u}} (f : T ⟶ B) (Λ : Type v) [CommRing Λ] :=
  (vanishingDatum.{u, v} f).derived (Coeff.{u, v} Λ)

/-- The existing bounded-object predicate for the standard derived t-structure.
Source: ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev IsBounded (S : Site.{s}) (A : Type s) [CommRing A] (L : S.derived A) : Prop :=
  DerivedCategory.TStructure.t.bounded L

/-- Boundedness means precisely cohomology supported in a finite interval.
Source: ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles).
Proof: for the standard derived t-structure, membership in degree at most b means
vanishing of cohomology in degrees greater than b, and membership in degree at least a
means vanishing in degrees less than a. Boundedness is the intersection of the unions
of these two predicates over integer bounds. Combine their bounds in each direction. -/
theorem isBounded_iff (S : Site.{s}) (A : Type s) [CommRing A] (L : S.derived A) :
    IsBounded S A L ↔ ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor (S.modules A) n).obj L) := by
  sorry

/-- Mathlib's bounded derived category of the actual constant-module category.
Source: ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev BoundedDerived (S : Site.{s}) (A : Type s) [CommRing A] :=
  DerivedCategory.Bounded (S.modules A)

/-- The nearby-cycle ringed-topos morphism with its exact constant-module inverse image.
Source: ILO XI §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def psiModules {T B : Scheme.{u}} (f : T ⟶ B) :=
  moduleMorphism (vanishingDatum.{u, v} f) (etaleDatum T) (psi f)

/-- The exact module inverse image attached to a scheme morphism.
Source: ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles). -/
def etaleModules {T B : Scheme.{u}} (f : T ⟶ B) :=
  moduleMorphism (etaleDatum.{u, v} B) (etaleDatum T) (etaleMorphism f)

/-- The exact module inverse image on the induced square of vanishing topoi.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-nearby-cycles). -/
def squareModules {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :=
  moduleMorphism (vanishingDatum.{u, v} f) (vanishingDatum f')
    (squareMorphism f f' h g comm)

/-- Unbounded nearby cycles, the existing K-injective right derived direct image.
Source: ILO XI §4.1, §4.3; Stacks 079P (blueprint: def-trf-oriented-nearby-cycles). -/
def nearbyCycles {T B : Scheme.{u}} (f : T ⟶ B) (Λ : Type v) [CommRing Λ] :
    EtaleDerived T Λ ⥤ VanishingDerived f Λ :=
  (psiModules f).push (Coeff.{u, v} Λ)

/-- The specified derived identification `ψ_f'^* v^* ≅ h^* ψ_f^*`: the existing
generator-normalized derived square of `lem-sp-completion-mate-comparison`, applied to
the inverse-image mate of `squarePsi`.
Source: ILO XI §1.9, §4.3 (blueprint: def-trf-oriented-nearby-cycles). -/
def nearbySquare {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g)
    (Λ : Type v) [CommRing Λ] :
    (squareModules f f' h g comm).pull (Coeff.{u, v} Λ) ⋙
        (psiModules f').pull (Coeff Λ) ≅
      (psiModules f).pull (Coeff Λ) ⋙ (etaleModules h).pull (Coeff Λ) :=
  CategoryTheory.AdicSites.derivedSquare (f := psiModules f) (g := squareModules f f' h g comm)
    (h := etaleModules h) (k := psiModules f')
    (GeometricMorphism.inverseIso (squarePsi f f' h g comm)).symm (Coeff Λ)

/-- Ordinary base change is the transpose of the square identification followed by the counit.
Source: ILO XI §4.1; Illusie §1.4 (blueprint: def-trf-oriented-nearby-cycles). -/
def baseChange {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g)
    (Λ : Type v) [CommRing Λ] (L : EtaleDerived T Λ) :
    ((squareModules f f' h g comm).pull (Coeff.{u, v} Λ)).obj ((nearbyCycles f Λ).obj L) ⟶
      (nearbyCycles f' Λ).obj (((etaleModules h).pull (Coeff Λ)).obj L) :=
  ((psiModules f').adj (Coeff Λ)).homEquiv _ _
    ((nearbySquare f f' h g comm Λ).hom.app ((nearbyCycles f Λ).obj L) ≫
      ((etaleModules h).pull (Coeff Λ)).map (((psiModules f).adj (Coeff Λ)).counit.app L))

/-- Ψ-goodness quantifies over every scheme base change, with no finiteness hypothesis.
Source: Illusie §1.4 (blueprint: def-trf-oriented-nearby-cycles). -/
def IsPsiGood {T B : Scheme.{u}} (f : T ⟶ B) (Λ : Type v) [CommRing Λ]
    (L : EtaleDerived T Λ) : Prop :=
  ∀ (B' : Scheme.{u}) (g : B' ⟶ B),
    IsIso (baseChange f (pullback.snd f g) (pullback.fst f g) g
      (pullback.condition (f := f) (g := g)) Λ L)



/-- The already localized K-flat tensor on a constant-coefficient ringed site.
Source: Stacks 06YS, 06YT; ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles). -/
abbrev derivedTensor (S : Site.{s}) (A : Type s) [CommRing A] :
    S.derived A × S.derived A ⥤ S.derived A :=
  SheafOfModules.wfSiteDerivedTensor S.topology (S.ring A)

/-- The existing ringed tensor corner for this very tensor functor.
Source: Stacks 07A4 (blueprint: def-trf-oriented-nearby-cycles). -/
def tensorCorner (S : Site.{s}) (A : Type s) [CommRing A] :
    SheafOfModules.RingedTensorCorner :=
  { site := S.objects
    topology := S.topology
    ring := S.ring A
    derived := Site.hasDerived S A
    tensor := derivedTensor S A }

/-- The precise flat-term K-flat representative subcategory.
Source: Stacks 06YS, 06YT (blueprint: def-trf-oriented-nearby-cycles). -/
def flatRepresentatives (S : Site.{s}) (A : Type s) [CommRing A] :
    ObjectProperty (CochainComplex (S.modules A) ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

/-- Localization of both flat-term K-flat arguments.
Source: Stacks 06YT (blueprint: def-trf-oriented-nearby-cycles). -/
def tensorInput (S : Site.{s}) (A : Type s) [CommRing A] :=
  ((flatRepresentatives S A).ι ⋙ DerivedCategory.Q).prod
    ((flatRepresentatives S A).ι ⋙ DerivedCategory.Q)

/-- The representative comparison, with its localization universal property.
Its data determine the tensor presentation up to the unique compatible isomorphism.
Source: Stacks 06YS, 06YT (blueprint: def-trf-oriented-nearby-cycles).
Proof: the recorded site tensor descent supplies its natural comparison on homotopy
K-flat objects. Restrict along the quotient of flat-term K-flat complexes and use
`quotientCompQhIso` to obtain i. Resolve both arguments by flat-term K-flat complexes.
The bijection for natural transformations in the same descent theorem extends every
comparison j uniquely to the derived categories; its inverse is the extension of the
inverse comparison. The two extensions compose to identities by uniqueness. -/
theorem tensorModel_exists (S : Site.{s}) (A : Type s) [CommRing A] :
    ∃ i : SheafOfModules.RingedTensorModel (tensorCorner S A),
      ∀ (F : S.derived A × S.derived A ⥤ S.derived A)
        (j : SheafOfModules.RingedTensorModel { tensorCorner S A with tensor := F }),
        ∃! e : derivedTensor S A ≅ F,
          i.representative.hom ≫ Functor.whiskerLeft (tensorInput S A) e.hom =
            j.representative.hom := by
  sorry

/-- The universal K-flat representative identification, retaining its normalization.
Source: Stacks 06YT (blueprint: def-trf-oriented-nearby-cycles). -/
def tensorModel (S : Site.{s}) (A : Type s) [CommRing A] :
    SheafOfModules.RingedTensorModel (tensorCorner S A) :=
  (tensorModel_exists S A).choose

/-- The actual scalar-extension functor has the recorded formula on module maps.
Source: Stacks 03D2 (blueprint: def-trf-oriented-nearby-cycles).
Proof: unfold ConstantCompletion.pull and change; functor composition gives the
scalar-extension map on every morphism. Both object equalities are reflexive, so the
two equality transports are identities. -/
theorem modulePull_map {V U : Site.{s}} (f : Morphism V U)
    (A : Type s) [CommRing A] {M N : V.modules A} (a : M ⟶ N) :
    (f.modulePull A).map a =
      eqToHom (rfl : (f.modulePull A).obj M =
        SheafOfModules.changeOfRings (constantMap f.algebra A)
          ((f.algebra.algebra (V.ring A)).modules.obj M)) ≫
      SheafOfModules.changeOfRingsHom (constantMap f.algebra A)
        ((f.algebra.algebra (V.ring A)).modules.obj M)
        ((f.algebra.algebra (V.ring A)).modules.map a) ≫
      eqToHom (rfl : SheafOfModules.changeOfRings (constantMap f.algebra A)
        ((f.algebra.algebra (V.ring A)).modules.obj N) = (f.modulePull A).obj N) := by
  sorry

/-- The specified inverse image as the existing ringed tensor edge. Its ordinary tensor
comparison is the unique one with the generalized pure-tensor and tensor-unit formulas.
Source: Stacks 03EL, 07A4 (blueprint: def-trf-oriented-nearby-cycles). -/
def tensorEdge {V U : Site.{s}} (f : Morphism V U) (A : Type s) [CommRing A] :
    SheafOfModules.RingedTensorEdge (tensorCorner V A) (tensorCorner U A) :=
  letI := f.finiteLimits
  { inverse := f.inverse
    direct := f.direct
    adjunction := f.adjunction
    finiteLimits := f.finiteLimits
    inverseRing := f.algebra.rings.obj (V.ring A)
    algebraic := f.algebra.algebra (V.ring A)
    ringMap := constantMap f.algebra A
    pullback := f.modulePull A
    object_eq := fun _ ↦ rfl
    map_eq := modulePull_map f A
    ordinaryTensor :=
      (SheafOfModules.canonicalRingedTensorComparison_existsUnique (V.ring A) (U.ring A)
        (f.algebra.rings.obj (V.ring A)) f.inverse (f.algebra.algebra (V.ring A))
        (constantMap f.algebra A) (f.modulePull A) (fun _ ↦ rfl) f.direct f.adjunction
        (modulePull_map f A)).1.some
    pushforward := f.modulePush A
    moduleAdjunction := f.moduleAdjunction A
    left := f.pull A
    epsilon := (f.modulePull A).mapDerivedCategoryFactorsh.hom
    isLeftDerived := Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (V.modules A) (ComplexShape.up ℤ))
        (f.pull A) (f.modulePull A).mapDerivedCategoryFactorsh
    right := f.push A
    derivedAdjunction := f.adj A }

/-- Canonical preservation of derived tensor, characterized on K-flat representatives.
Source: Stacks 07A4 (blueprint: def-trf-oriented-nearby-cycles). -/
def pullTensor {V U : Site.{s}} (f : Morphism V U) (A : Type s) [CommRing A] :
    derivedTensor V A ⋙ f.pull A ≅ ((f.pull A).prod (f.pull A)) ⋙ derivedTensor U A :=
  (tensorEdge f A).tensorComparison (tensorModel V A) (tensorModel U A)

/-- The lax tensor map is exactly the transpose of the tensor of the two counits.
Source: Illusie §§1.4--1.5; ILO XI §4.1 (blueprint: def-trf-oriented-nearby-cycles). -/
def laxTensor {T B : Scheme.{u}} (f : T ⟶ B) (Λ : Type v) [CommRing Λ]
    (L M : EtaleDerived T Λ) :
    (derivedTensor (vanishingDatum f) (Coeff.{u, v} Λ)).obj
        ((nearbyCycles f Λ).obj L, (nearbyCycles f Λ).obj M) ⟶
      (nearbyCycles f Λ).obj ((derivedTensor (etaleDatum T) (Coeff Λ)).obj (L, M)) :=
  ((psiModules f).adj (Coeff Λ)).homEquiv _ _
    ((pullTensor (psiModules f) (Coeff Λ)).hom.app
        ((nearbyCycles f Λ).obj L, (nearbyCycles f Λ).obj M) ≫
      (derivedTensor (etaleDatum T) (Coeff Λ)).map
        (Prod.mkHom (((psiModules f).adj (Coeff Λ)).counit.app L)
          (((psiModules f).adj (Coeff Λ)).counit.app M)))

/-- The structure map of the scheme fibre product, using the first projection.
Source: Illusie §2.1 (blueprint: def-trf-oriented-nearby-cycles). -/
def productMap {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B) :=
  pullback.fst f₁ f₂ ≫ f₁

/-- The first projection square of the fibre product.
Source: Illusie §2.1 (blueprint: def-trf-oriented-nearby-cycles).
Proof: the structure map is defined as q₁ followed by f₁; composing it with the
identity of B gives the same morphism by the right identity law. -/
theorem product_first_comm {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B) :
    pullback.fst f₁ f₂ ≫ f₁ = productMap f₁ f₂ ≫ 𝟙 B := by
  sorry

/-- The second projection square of the fibre product.
Source: Illusie §2.1 (blueprint: def-trf-oriented-nearby-cycles).
Proof: the fibre-product condition identifies q₂ f₂ with q₁ f₁, which is the
structure map; composing the latter with the identity does not change it. -/
theorem product_second_comm {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B) :
    pullback.snd f₁ f₂ ≫ f₂ = productMap f₁ f₂ ≫ 𝟙 B := by
  sorry

/-- The first induced map of vanishing topoi in the external product.
Source: Illusie §2.1 (blueprint: def-trf-oriented-nearby-cycles). -/
def productFirst {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B) :=
  squareModules.{u, v} f₁ (productMap f₁ f₂) (pullback.fst f₁ f₂) (𝟙 B)
    (product_first_comm f₁ f₂)

/-- The second induced map of vanishing topoi in the external product.
Source: Illusie §2.1 (blueprint: def-trf-oriented-nearby-cycles). -/
def productSecond {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B) :=
  squareModules.{u, v} f₂ (productMap f₁ f₂) (pullback.snd f₁ f₂) (𝟙 B)
    (product_second_comm f₁ f₂)

/-- The relative external product on the actual scheme fibre product.
Source: Illusie §2.1 (blueprint: def-trf-oriented-nearby-cycles). -/
def externalEtale {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B)
    (Λ : Type v) [CommRing Λ] (L₁ : EtaleDerived T₁ Λ) (L₂ : EtaleDerived T₂ Λ) :
    EtaleDerived (pullback f₁ f₂) Λ :=
  (derivedTensor (etaleDatum (pullback f₁ f₂)) (Coeff.{u, v} Λ)).obj
    (((etaleModules (pullback.fst f₁ f₂)).pull (Coeff Λ)).obj L₁,
      ((etaleModules (pullback.snd f₁ f₂)).pull (Coeff Λ)).obj L₂)

/-- The external product on the vanishing topos, using its two induced projections.
Source: Illusie §2.1 (blueprint: def-trf-oriented-nearby-cycles). -/
def externalVanishing {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B)
    (Λ : Type v) [CommRing Λ] (P₁ : VanishingDerived f₁ Λ) (P₂ : VanishingDerived f₂ Λ) :
    VanishingDerived (productMap f₁ f₂) Λ :=
  (derivedTensor (vanishingDatum (productMap f₁ f₂)) (Coeff.{u, v} Λ)).obj
    (((productFirst f₁ f₂).pull (Coeff Λ)).obj P₁,
      ((productSecond f₁ f₂).pull (Coeff Λ)).obj P₂)

/-- The oriented Künneth comparison: β₁ tensor β₂, followed by the specified lax tensor map.
No invertibility assertion or goodness assumption is included in this definition.
Source: Illusie §2.1 (blueprint: def-trf-oriented-nearby-cycles). -/
def kunneth {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B)
    (Λ : Type v) [CommRing Λ] (L₁ : EtaleDerived T₁ Λ) (L₂ : EtaleDerived T₂ Λ) :
    externalVanishing f₁ f₂ Λ ((nearbyCycles f₁ Λ).obj L₁) ((nearbyCycles f₂ Λ).obj L₂) ⟶
      (nearbyCycles (productMap f₁ f₂) Λ).obj (externalEtale f₁ f₂ Λ L₁ L₂) :=
  (derivedTensor (vanishingDatum (productMap f₁ f₂)) (Coeff.{u, v} Λ)).map
    (Prod.mkHom
      (baseChange f₁ (productMap f₁ f₂) (pullback.fst f₁ f₂) (𝟙 B)
        (product_first_comm f₁ f₂) Λ L₁)
      (baseChange f₂ (productMap f₁ f₂) (pullback.snd f₁ f₂) (𝟙 B)
        (product_second_comm f₁ f₂) Λ L₂)) ≫
    laxTensor (productMap f₁ f₂) Λ
      (((etaleModules (pullback.fst f₁ f₂)).pull (Coeff Λ)).obj L₁)
      (((etaleModules (pullback.snd f₁ f₂)).pull (Coeff Λ)).obj L₂)

end AlgebraicGeometry.OrientedNearbyCycles
