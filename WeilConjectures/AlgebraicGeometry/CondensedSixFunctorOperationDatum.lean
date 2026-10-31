/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection

/-! # Operation data on ordinary condensed module categories

Source: latest blueprint def-fix-six-functor-datum, clauses (1)--(5)
(blueprint: def-fix-six-functor-datum).

The pullback, direct image, tensor, internal Hom, open extension, exchange and
projection maps are the existing module-object constructions. The only supplied
operation is the proper constructible right adjoint, supplied with its adjunction.
The exceptional functor is the composite of that right adjoint with open pullback.
This type makes no assertion that such data exist for arbitrary coefficients.

Only the constituent definitions are imported here. In particular the type of operation
data does not depend on theorems asserting existence, preservation or biduality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Functor CategoryTheory.Obj MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The constructible operation data for one coefficient and one compactification.
All categories are full subcategories of the ordinary derived category. The proper
right adjoint is specified by its adjunction, hence up to its unique adjunction-compatible
isomorphism. Open extension and pullback are restrictions of the actual ambient functors.
Source: latest blueprint def-fix-six-functor-datum (2),(4)
(blueprint: def-fix-six-functor-datum). -/
structure CondensedSixFunctorOperationDatum {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  /-- Preservation needed to restrict the proper direct image. -/
  properPreserves : ∀ K : ConstantModelBoundedConstructible Λ c.Z,
    constantModelBoundedConstructible Λ Y
      ((moduleObjectDerivedPushforward Λ c.g).obj K.obj)
  /-- Preservation needed to restrict the actual open extension. -/
  openPreserves : ∀ K : ConstantModelBoundedConstructible Λ X,
    constantModelBoundedConstructible Λ c.Z
      (((openImmersionLowerShriek Λ c.i).mapDerivedCategory).obj K.obj)
  /-- Preservation needed to restrict the actual open pullback. -/
  openPullPreserves : ∀ K : ConstantModelBoundedConstructible Λ c.Z,
    constantModelBoundedConstructible Λ X
      ((moduleObjectDerivedPullback Λ c.i).obj K.obj)
  /-- The right adjoint on constructible categories, never on the ambient category. -/
  properExceptional : ConstantModelBoundedConstructible Λ Y ⥤
    ConstantModelBoundedConstructible Λ c.Z
  /-- The proper constructible adjunction fixes its normalization. -/
  properAdjunction : (constantModelBoundedConstructible Λ Y).lift
    ((constantModelBoundedConstructible Λ c.Z).ι ⋙ moduleObjectDerivedPushforward Λ c.g)
      properPreserves ⊣ properExceptional

variable {Λ}
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The actual compactification composite, restricted to bounded constructible objects.
Source: latest blueprint def-fix-six-functor-datum (2)
(blueprint: def-fix-six-functor-datum). -/
def CondensedSixFunctorOperationDatum.support (S : CondensedSixFunctorOperationDatum Λ c) :
    ConstantModelBoundedConstructible Λ X ⥤ ConstantModelBoundedConstructible Λ Y :=
  ((constantModelBoundedConstructible Λ c.Z).lift
    ((constantModelBoundedConstructible Λ X).ι ⋙
      (openImmersionLowerShriek Λ c.i).mapDerivedCategory) S.openPreserves) ⋙
  ((constantModelBoundedConstructible Λ Y).lift
    ((constantModelBoundedConstructible Λ c.Z).ι ⋙ moduleObjectDerivedPushforward Λ c.g)
      S.properPreserves)

/-- Exceptional inverse image is open pullback after the proper constructible adjoint.
Source: latest blueprint def-fix-six-functor-datum (4)
(blueprint: def-fix-six-functor-datum). -/
def CondensedSixFunctorOperationDatum.exceptional (S : CondensedSixFunctorOperationDatum Λ c) :
    ConstantModelBoundedConstructible Λ Y ⥤ ConstantModelBoundedConstructible Λ X :=
  S.properExceptional ⋙ (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ c.Z).ι ⋙ moduleObjectDerivedPullback Λ c.i)
      S.openPullPreserves

/-- Restrict the original open adjunction along the two fully faithful inclusions.
Its unit and counit are fixed by the ambient adjunction, not additional choices.
Source: latest blueprint def-fix-six-functor-datum (4)
(blueprint: def-fix-six-functor-datum). -/
def CondensedSixFunctorOperationDatum.openAdjunction
    (S : CondensedSixFunctorOperationDatum Λ c) :
    (constantModelBoundedConstructible Λ c.Z).lift
      ((constantModelBoundedConstructible Λ X).ι ⋙
        (openImmersionLowerShriek Λ c.i).mapDerivedCategory) S.openPreserves ⊣
    (constantModelBoundedConstructible Λ X).lift
      ((constantModelBoundedConstructible Λ c.Z).ι ⋙ moduleObjectDerivedPullback Λ c.i)
        S.openPullPreserves :=
  (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ c.i).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- The composite Hom bijection defines the constructible exceptional adjunction.
Source: latest blueprint def-fix-six-functor-datum (4), displayed Hom chain
(blueprint: def-fix-six-functor-datum). -/
def CondensedSixFunctorOperationDatum.adjunction (S : CondensedSixFunctorOperationDatum Λ c) :
    S.support ⊣ S.exceptional :=
  S.openAdjunction.comp S.properAdjunction

/-- The exceptional image of the coefficient unit. For a structure morphism this is omega.
The unit is supplied as a constructible object together with its ambient identification
by the caller, not chosen from a bare existence statement.
Source: latest blueprint def-fix-six-functor-datum (5)
(blueprint: def-fix-six-functor-datum). -/
def CondensedSixFunctorOperationDatum.dualizing (S : CondensedSixFunctorOperationDatum Λ c)
    (N : ConstantModelBoundedConstructible Λ Y) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (S.exceptional.obj N).obj

/-- The actual relative internal Hom into the exceptional image of N.
Source: latest blueprint def-fix-six-functor-datum (5)
(blueprint: def-fix-six-functor-datum). -/
def CondensedSixFunctorOperationDatum.verdier (S : CondensedSixFunctorOperationDatum Λ c)
    (N : ConstantModelBoundedConstructible Λ Y) :
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))ᵒᵖ ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (derivedHom Λ X).flip.obj (S.dualizing N)

end AlgebraicGeometry.ProEtale.CondensedRing
