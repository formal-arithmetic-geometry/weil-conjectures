/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Canonical intrinsic finite-coefficient inverse image

Source: Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules;
blueprint ordinary pro-etale operations (blueprint: prose-03-02).

The existing arbitrary-ring and continuous-function interfaces are reexported.
Here the canonical fixed-scalar inverse image is transported through the published
intrinsic constant-ring realization, without choosing a coefficient identification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- The realization equivalence has its published additive functor.
Source: Stacks, Tag 00YV (blueprint: prose-03-02). -/
noncomputable instance sfIntrinsicModuleEquivalence_functor_additive (X : Scheme.{u}) :
    (sfIntrinsicModuleEquivalence X A).functor.Additive :=
  inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization X A).Additive

/-- Transport a fixed-scalar functor through the canonical realization equivalences.
Source: Stacks, Tag 00YV (blueprint: prose-03-02). -/
noncomputable def sfIntrinsicTransport {X Y : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A) :=
  (sfIntrinsicModuleEquivalence X A).inverse ⋙ F ⋙
    (sfIntrinsicModuleEquivalence Y A).functor

/-- Transport natural isomorphisms by the same coefficient realization.
Source: Stacks, Tag 00YV (blueprint: prose-03-02). -/
noncomputable def sfIntrinsicTransportIso {X Y : Scheme.{u}}
    {F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))} (e : F ≅ G) :
    sfIntrinsicTransport A F ≅ sfIntrinsicTransport A G :=
  isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
    (isoWhiskerRight e (sfIntrinsicModuleEquivalence Y A).functor)

/-- The composition comparison inserts the realization unit at the middle scheme.
Source: Stacks, Tag 00YV (blueprint: prose-03-02). -/
noncomputable def sfIntrinsicTransportComp {X Y Z : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (G : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    sfIntrinsicTransport A (F ⋙ G) ≅ sfIntrinsicTransport A F ⋙ sfIntrinsicTransport A G :=
  isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
    (isoWhiskerRight
      (isoWhiskerLeft F ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc G).symm)
      (sfIntrinsicModuleEquivalence Z A).functor)

/-- Exact inverse image with the intrinsic constant scalar action.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: prose-03-02). -/
noncomputable def sfIntrinsicPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  sfIntrinsicTransport A (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)

/-- Additivity of this canonical transport. Source: Stacks, Tag 04JC
(blueprint: prose-03-02). -/
noncomputable instance sfIntrinsicPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicPullback A f).Additive :=
  inferInstanceAs ((sfIntrinsicModuleEquivalence Y A).inverse ⋙
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
    (sfIntrinsicModuleEquivalence X A).functor).Additive

/-- Left exactness is preserved by the two realization equivalences.
Source: Stacks, Tag 04JC (blueprint: prose-03-02). -/
noncomputable instance sfIntrinsicPullback_preservesFiniteLimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) : PreservesFiniteLimits (sfIntrinsicPullback A f) :=
  inferInstanceAs (PreservesFiniteLimits ((sfIntrinsicModuleEquivalence Y A).inverse ⋙
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
    (sfIntrinsicModuleEquivalence X A).functor))

/-- Right exactness is preserved by the two realization equivalences.
Source: Stacks, Tag 04JC (blueprint: prose-03-02). -/
noncomputable instance sfIntrinsicPullback_preservesFiniteColimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) : PreservesFiniteColimits (sfIntrinsicPullback A f) :=
  inferInstanceAs (PreservesFiniteColimits ((sfIntrinsicModuleEquivalence Y A).inverse ⋙
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
    (sfIntrinsicModuleEquivalence X A).functor))

/-- Canonical pullback composition, with its actual coefficient transports.
Source: Stacks, Modules on Sites (blueprint: prose-03-02). -/
noncomputable def sfIntrinsicPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sfIntrinsicPullback A (f ≫ g) ≅ sfIntrinsicPullback A g ⋙ sfIntrinsicPullback A f :=
  sfIntrinsicTransportIso A
    (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g) ≪≫
    sfIntrinsicTransportComp A _ _

/-- Identity pullback, using the realization counit.
Source: Stacks, Modules on Sites (blueprint: prose-03-02). -/
noncomputable def sfIntrinsicPullbackId (X : Scheme.{u}) :
    sfIntrinsicPullback A (𝟙 X) ≅ 𝟭 _ :=
  sfIntrinsicTransportIso A
    (ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X) ≪≫
    (sfIntrinsicModuleEquivalence X A).counitIso

/-- The ordinary uncompleted unbounded derived inverse image, by exact termwise descent.
Source: Stacks, Section 0735 (blueprint: prose-03-02). -/
noncomputable abbrev sfIntrinsicDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A :=
  (sfIntrinsicPullback A f).mapDerivedCategory

end AlgebraicGeometry.Scheme
