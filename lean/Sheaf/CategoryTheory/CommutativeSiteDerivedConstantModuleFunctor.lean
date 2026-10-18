/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# The commutative-coefficient presentation of exact constant realization

Source: Stacks Project, Modules on Sites, Tags 03CY and 093J; Cohomology on Sites,
paragraph preceding 09BD (blueprint: def-sfb-site-derived-constant-module-functor).
The ring sheaf here is the constant CommRingCat sheaf with commutativity forgotten.
The old interface uses constant RingCat sheafification instead. Their canonical
constantCommuteCompose isomorphism identifies the two presentations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v wR wS
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The usual constant commutative ring sheaf.
Source: Stacks 093J (blueprint: def-sfb-site-derived-constant-module-functor). -/
abbrev realizationRing (R : Type (max u v)) [CommRing R] :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R)

/-- The existing module category over its underlying ring sheaf.
Source: Stacks 03DA (blueprint: def-sfb-site-derived-constant-module-functor). -/
abbrev realizationModules (R : Type (max u v)) [CommRing R] :=
  SheafOfModules.{max u v} ((sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (realizationRing J R))

/-- The coefficient sheafification unit with commutativity forgotten.
Source: Stacks 03CY (blueprint: def-sfb-site-derived-constant-module-functor). -/
def realizationRingUnit (R : Type (max u v)) [CommRing R] :
    (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J R)).obj :=
  Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R)))
    (forget₂ CommRingCat RingCat)

/-- Forgetting commutativity retains the locally bijective sheafification unit.
Source: Stacks 03CY (blueprint: def-sfb-site-derived-constant-module-functor).
Proof: local injectivity and local surjectivity only concern the underlying functions
of sections and covering sieves. Forgetting commutativity changes none of them. -/
theorem realizationRingUnit_locallyBijective (R : Type (max u v)) [CommRing R] :
    Presheaf.IsLocallyInjective J (realizationRingUnit J R) ∧
      Presheaf.IsLocallySurjective J (realizationRingUnit J R) := by
  sorry

/-- The recorded constant module construction with the commutative coefficient
presentation: the same constant module presheaf followed by module sheafification.
Source: Stacks 03CY and 093J (blueprint: def-sfb-site-derived-constant-module-functor). -/
def commutativeSiteConstantModuleFunctor (R : Type (max u v)) [CommRing R] :
    ModuleCat.{max u v} R ⥤ realizationModules J R :=
  letI := (realizationRingUnit_locallyBijective J R).1
  letI := (realizationRingUnit_locallyBijective J R).2
  siteConstantModulePresheafGeneral (C := C) R ⋙
    PresheafOfModules.sheafification (realizationRingUnit J R)

/-- The commutative-coefficient presentation is additive and exact.
Source: Stacks 093J and 03CY (blueprint: def-sfb-site-derived-constant-module-functor).
Proof: constant presheaves preserve exact sequences sectionwise. Module sheafification
is additive and exact, so their composite preserves finite limits and finite colimits. -/
theorem commutativeSiteConstantModuleFunctor_exact (R : Type (max u v)) [CommRing R] :
    (commutativeSiteConstantModuleFunctor J R).Additive ∧
      PreservesFiniteLimits (commutativeSiteConstantModuleFunctor J R) ∧
      PreservesFiniteColimits (commutativeSiteConstantModuleFunctor J R) := by
  sorry

/-- Additivity supplied by exact constant realization.
Source: Stacks 093J (blueprint: def-sfb-site-derived-constant-module-functor). -/
instance commutativeSiteConstantModuleFunctor_additive
    (R : Type (max u v)) [CommRing R] :
    (commutativeSiteConstantModuleFunctor J R).Additive :=
  (commutativeSiteConstantModuleFunctor_exact J R).1

/-- Left exactness supplied by exact constant realization.
Source: Stacks 093J (blueprint: def-sfb-site-derived-constant-module-functor). -/
instance commutativeSiteConstantModuleFunctor_limits
    (R : Type (max u v)) [CommRing R] :
    PreservesFiniteLimits (commutativeSiteConstantModuleFunctor J R) :=
  (commutativeSiteConstantModuleFunctor_exact J R).2.1

/-- Right exactness supplied by exact constant realization.
Source: Stacks 093J (blueprint: def-sfb-site-derived-constant-module-functor). -/
instance commutativeSiteConstantModuleFunctor_colimits
    (R : Type (max u v)) [CommRing R] :
    PreservesFiniteColimits (commutativeSiteConstantModuleFunctor J R) :=
  (commutativeSiteConstantModuleFunctor_exact J R).2.2

/-- Forgetting commutativity preserves sheafification equivalences.
Source: Stacks 00WJ and 093J (blueprint: def-sfb-site-derived-constant-module-functor).
Proof: a morphism of ring presheaves is inverted by sheafification exactly when its
underlying functions are locally injective and locally surjective. The underlying
functions and covering sieves are unchanged by forgetting commutativity. Hence every
CommRingCat sheafification equivalence is a RingCat sheafification equivalence. -/
theorem realization_forget_preservesSheafification :
    J.PreservesSheafification (forget₂ CommRingCat.{max u v} RingCat.{max u v}) := by
  sorry

/-- The coefficient-forgetful sheafification instance.
Source: Stacks 093J (blueprint: def-sfb-site-derived-constant-module-functor). -/
instance realization_forget_preservesSheafification_instance :
    J.PreservesSheafification (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  realization_forget_preservesSheafification J

/-- The canonical comparison with the original RingCat coefficient presentation.
Source: Stacks 093J (blueprint: def-sfb-site-derived-constant-module-functor). -/
def realizationRingIso (R : Type (max u v)) [CommRing R] :
    (sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J R) ≅
      (constantSheaf J RingCat).obj (RingCat.of R) :=
  (constantCommuteCompose J (forget₂ CommRingCat RingCat)).app (CommRingCat.of R)

/-- The repaired presentation is the recorded constant-module functor after canonical
coefficient transport, rather than a second constant realization.
Source: Stacks 03CY and 093J (blueprint: def-sfb-site-derived-constant-module-functor).
Proof: constantCommuteCompose identifies the two ring-sheafification units. Transport
along this identification identifies their module-sheafification adjunctions. The
identity of constant module presheaves therefore extends uniquely to the displayed
natural isomorphism; its inverse is obtained using the inverse ring identification. -/
theorem commutativeSiteConstantModuleFunctor_transport
    (R : Type (max u v)) [CommRing R] :
    Nonempty (commutativeSiteConstantModuleFunctor J R ⋙
        SheafOfModules.restrictScalars (realizationRingIso J R).inv ≅
      siteConstantModuleFunctorGeneral J R) := by
  sorry

/-- Constant realization by exact-functor localization, at independent localization sizes.
Source: Stacks, paragraph before 09BD
(blueprint: def-sfb-site-derived-constant-module-functor). -/
def commutativeSiteDerivedConstantModuleFunctor (R : Type (max u v)) [CommRing R]
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wS} (realizationModules J R)] :
    DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (realizationModules J R) :=
  haveI := (commutativeSiteConstantModuleFunctor_exact J R).1
  haveI := (commutativeSiteConstantModuleFunctor_exact J R).2.1
  haveI := (commutativeSiteConstantModuleFunctor_exact J R).2.2
  (commutativeSiteConstantModuleFunctor J R).mapDerivedCategory

end CategoryTheory
