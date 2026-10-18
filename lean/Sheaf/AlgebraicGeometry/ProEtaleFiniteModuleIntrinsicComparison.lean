/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
/-!
# Finite-coefficient comparison in the intrinsic constant-ring presentation

Source: blueprint `def-weil-pbc-proetale-modules`, and Stacks Project, Tags 099R and 00YV
(blueprint: def-weil-pbc-proetale-modules).

The existing finite-coefficient comparison uses modules over sheafified continuous
functions. Intrinsic constructibility uses modules over the constant commutative ring
sheaf. The canonical associated-module-sheaf construction below supplies this second
presentation of the same exact inverse image, with constant scalar action fixed by the
sheafification unit. It does not choose an abstract equivalence or a new inverse image.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The constant-scalar unit into the underlying ring of the commutative constant sheaf.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientIntrinsicScalarMap (T : Scheme.{u})
    (B : Type u) [CommRing B] :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)) ⟶
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing T B)).obj :=
  Functor.whiskerRight
    (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

variable (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]

/-- Local injectivity for the canonical associated-module-sheaf construction.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientIntrinsicScalarMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology T)
      (finiteCoefficientIntrinsicScalarMap T B) :=
  (Scheme.proEtaleConstantRingUnit_locallyBijective T B).1

/-- Local surjectivity for the canonical associated-module-sheaf construction.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientIntrinsicScalarMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology T)
      (finiteCoefficientIntrinsicScalarMap T B) :=
  (Scheme.proEtaleConstantRingUnit_locallyBijective T B).2

/-- Canonical realization over the constant commutative coefficient sheaf: keep the
fixed-scalar module presheaf and sheafify it along the constant-scalar unit.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientIntrinsicRealization :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⥤
      Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B) :=
  sheafToPresheaf _ _ ⋙ finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} B) ⋙
    PresheafOfModules.sheafification (finiteCoefficientIntrinsicScalarMap T B)

/-- This is an additive exact equivalence of the two presentations of module sheaves.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules).
Proof: fixed scalar actions extend uniquely to locally constant scalar sections of the
constant ring sheaf. The local-bijection property of the scalar unit gives the inverse
by restriction of scalars, with the ordinary module sheafification unit and counit.
These maps preserve addition sectionwise. The equivalence preserves finite limits and
colimits. This is the same argument as `finiteCoefficientRealization_exact`, applied to
the canonical commutative constant-ring presentation rather than continuous functions. -/
theorem finiteCoefficientIntrinsicRealization_exact :
    (finiteCoefficientIntrinsicRealization T B).IsEquivalence ∧
    (finiteCoefficientIntrinsicRealization T B).Additive ∧
    PreservesFiniteLimits (finiteCoefficientIntrinsicRealization T B) ∧
    PreservesFiniteColimits (finiteCoefficientIntrinsicRealization T B) := by
  sorry

/-- Additivity of the canonical coefficient realization.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientIntrinsicRealization_additive :
    (finiteCoefficientIntrinsicRealization T B).Additive :=
  (finiteCoefficientIntrinsicRealization_exact T B).2.1

/-- Left exactness of the canonical coefficient realization.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientIntrinsicRealization_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientIntrinsicRealization T B) :=
  (finiteCoefficientIntrinsicRealization_exact T B).2.2.1

/-- Right exactness of the canonical coefficient realization.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientIntrinsicRealization_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientIntrinsicRealization T B) :=
  (finiteCoefficientIntrinsicRealization_exact T B).2.2.2

/-- The specified comparison inverse image, expressed over the intrinsic constant ring.
Source: Stacks, Tags 099R and 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientIntrinsicComparison :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⥤
      Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B) :=
  comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
    finiteCoefficientIntrinsicRealization T B

/-- The intrinsic comparison is additive.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientIntrinsicComparison_additive :
    (finiteCoefficientIntrinsicComparison T B).Additive :=
  inferInstanceAs (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
    finiteCoefficientIntrinsicRealization T B).Additive

/-- The intrinsic comparison is left exact.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientIntrinsicComparison_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientIntrinsicComparison T B) :=
  inferInstanceAs (PreservesFiniteLimits
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
      finiteCoefficientIntrinsicRealization T B))

/-- The intrinsic comparison is right exact.
Source: Stacks, Tag 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientIntrinsicComparison_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientIntrinsicComparison T B) :=
  inferInstanceAs (PreservesFiniteColimits
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
      finiteCoefficientIntrinsicRealization T B))

/-- The exact inverse image on derived categories, in the coefficient presentation of
intrinsic constructibility, obtained by applying the specified comparison termwise.
Source: Stacks, Tags 099R and 00YV (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientIntrinsicDerivedComparison :
    FiniteCoefficientEtaleDerivedCategory T (ULift.{u + 1, u} B) ⥤
      Scheme.proEtaleDerivedCategory T B :=
  (finiteCoefficientIntrinsicComparison T B).mapDerivedCategory

end AlgebraicGeometry.ProEtale
