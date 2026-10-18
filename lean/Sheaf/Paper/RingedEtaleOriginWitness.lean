/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.EtaleOriginWitness
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Specified etale-origin witnesses for constant pro-etale coefficients

Source: blueprint, proper base change, etale-origin witness; Stacks Project Tag 099R
(blueprint: def-weil-pbc-etale-origin-witness).

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleOriginWitness`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- Constant commutative coefficients in the module universe of the small site.
Source: Stacks Tag 099R (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable abbrev etaleOriginRing : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- Constant scalar sections into the specified constant commutative ring sheaf.
Source: Stacks Tags 00YV and 099R (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable def etaleOriginScalars :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (etaleOriginRing T Λ)).obj :=
  Functor.whiskerRight
    (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- Constant scalar sections are locally bijective also after forgetting commutativity.
Source: Stacks Tags 00YV and 00WJ (blueprint: def-weil-pbc-etale-origin-witness).
Proof: the sheafification unit is locally bijective. The forgetful functor preserves
finite limits and filtered colimits; its underlying section maps are the same set maps.
The local injectivity and local surjectivity conditions therefore remain unchanged. -/
theorem etaleOriginScalars_locallyBijective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (etaleOriginScalars T Λ) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (etaleOriginScalars T Λ) := by
  sorry

/-- Local injectivity for associated module sheafification.
Source: Stacks Tag 00WJ (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable instance etaleOriginScalars_isLocallyInjective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (etaleOriginScalars T Λ) :=
  (etaleOriginScalars_locallyBijective T Λ).1

/-- Local surjectivity for associated module sheafification.
Source: Stacks Tag 00WJ (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable instance etaleOriginScalars_isLocallySurjective :
    Presheaf.IsLocallySurjective (ProEt.topology T) (etaleOriginScalars T Λ) :=
  (etaleOriginScalars_locallyBijective T Λ).2

/-- Canonical realization of fixed-ring module sheaves over the constant ring sheaf.
The module presheaf is the recorded realization and the scalar map is constant sections.
Source: Stacks Tag 00YV (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable def etaleOriginRealization :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Λ) ⥤
      proEtaleRingModules T (etaleOriginRing T Λ) :=
  sheafToPresheaf _ _ ⋙ ProEtale.finiteCoefficientModulePresheaf T.ProEt Λ ⋙
    PresheafOfModules.sheafification (etaleOriginScalars T Λ)

/-- The realization is an exact additive equivalence.
Source: Stacks Tag 00YV (blueprint: def-weil-pbc-etale-origin-witness).
Proof: locally every section of the constant ring sheaf is a constant scalar, so a
fixed Λ-action extends uniquely to its local sections. Sheaf gluing gives the inverse
functor and its unit and counit. This equivalence preserves kernels, cokernels and addition. -/
theorem etaleOriginRealization_properties :
    (etaleOriginRealization T Λ).Additive ∧
      PreservesFiniteLimits (etaleOriginRealization T Λ) ∧
      PreservesFiniteColimits (etaleOriginRealization T Λ) ∧
      (etaleOriginRealization T Λ).IsEquivalence := by
  sorry

/-- Additivity of the constant-coefficient realization.
Source: Stacks Tag 00YV (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable instance etaleOriginRealization_additive :
    (etaleOriginRealization T Λ).Additive := (etaleOriginRealization_properties T Λ).1

/-- Left exactness of the constant-coefficient realization.
Source: Stacks Tag 00YV (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable instance etaleOriginRealization_preservesFiniteLimits :
    PreservesFiniteLimits (etaleOriginRealization T Λ) :=
  (etaleOriginRealization_properties T Λ).2.1

/-- Right exactness of the constant-coefficient realization.
Source: Stacks Tag 00YV (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable instance etaleOriginRealization_preservesFiniteColimits :
    PreservesFiniteColimits (etaleOriginRealization T Λ) :=
  (etaleOriginRealization_properties T Λ).2.2.1

/-- The specified comparison inverse image, with its canonical constant-ring realization.
Source: Stacks Tag 099R (blueprint: def-weil-pbc-etale-origin-witness). -/
noncomputable def etaleOriginComparison :
    DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (proEtaleRingModules T (etaleOriginRing T Λ)) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙
    etaleOriginRealization T Λ).mapDerivedCategory

/-- Reuse the recorded retained origin pair for every finite discrete ring, including
noncommutative rings. Both the input and its etale antecedent are bounded below.
Source: blueprint etale-origin witness, displayed pair; Stacks Tag 099R
(blueprint: def-weil-pbc-etale-origin-witness). -/
abbrev EtaleOriginWitness (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : ProEtale.FiniteCoefficientDerivedCategoryPlus T Λ) :=
  ProEtale.EtaleOriginWitness T Λ K

end AlgebraicGeometry.Scheme

@[expose] public noncomputable section
namespace AlgebraicGeometry.Scheme

/-- The finite constant coefficient sheaf in its published function presentation.
Source: Stacks 09BT (blueprint: def-weil-pbc-etale-origin-witness). -/
abbrev finiteOriginFunctionRing (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] := AdicCoefficients.coefficientRing T Λ

/-- Constants-to-functions is the canonical finite coefficient isomorphism.
Source: Stacks 09BT (blueprint: def-weil-pbc-etale-origin-witness).
Proof: a finite-discrete-valued continuous function is locally constant. Its level sets
cover the source by opens, so constant sections are locally bijective. Sheafification
therefore turns the constants map into an isomorphism, including for the zero ring. -/
theorem finiteOriginConstantComparison_isIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : IsIso (AdicCoefficients.constantComparison T Λ) := by
  sorry

/-- The constants-to-functions transport retains exactly the published section map.
Source: Stacks 09BT (blueprint: def-weil-pbc-etale-origin-witness). -/
def finiteOriginConstantIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : etaleOriginRing T Λ ≅ finiteOriginFunctionRing T Λ :=
  @asIso _ _ _ _ (AdicCoefficients.constantComparison T Λ)
    (finiteOriginConstantComparison_isIso T Λ)

/-- Canonical exact restriction from function coefficients to constant coefficients.
Source: Stacks 03DA, 09BT (blueprint: def-weil-pbc-etale-origin-witness). -/
abbrev finiteOriginToConstant (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    DerivedCategory (proEtaleRingModules T (finiteOriginFunctionRing T Λ)) ⥤
      DerivedCategory (proEtaleRingModules T (etaleOriginRing T Λ)) := by
  let a := (finiteOriginConstantIso T Λ).hom
  letI : PreservesFiniteLimits (proEtaleRingRestrictScalars a) :=
    (proEtaleRingRestrictScalars_properties a).1
  letI : PreservesFiniteColimits (proEtaleRingRestrictScalars a) :=
    (proEtaleRingRestrictScalars_properties a).2.1
  exact (proEtaleRingRestrictScalars a).mapDerivedCategory

/-- The same retained witness pair after the canonical finite coefficient transport.
It contains a specified bounded-below etale object and its isomorphism, not just existence.
Source: Stacks 099R, 09BT (blueprint: def-weil-pbc-etale-origin-witness). -/
structure FiniteEtaleOriginWitness (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (proEtaleRingModules T (finiteOriginFunctionRing T Λ))) where
  complex : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  iso : (etaleOriginComparison T Λ).obj complex.obj ≅ (finiteOriginToConstant T Λ).obj K

end AlgebraicGeometry.Scheme
