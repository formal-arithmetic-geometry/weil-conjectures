/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Coherence of a normalized Brown level realization

This module isolates the section, localization, and mate equations for supplied
realization data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

variable (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})

set_option maxHeartbeats 2000000 in
-- Checking section identities unfolds the two constant-scalar restriction constructions.
private def ordinaryRestrictionIso {m n : ℕ} (h : m ≤ n) :
    coefficientRestriction (J := W.smallEtaleTopology) O t h ⋙
      strictEtaleBrownConstant O t W n ≅
    strictEtaleBrownConstant O t W m ⋙
      Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun a ↦ by
      ext x
      change ((M.val.obj U).smul
          ((toSheafify W.smallEtaleTopology
            ((Functor.const W.Etaleᵒᵖ).obj
              (CommRingCat.of (strictEtaleBrownRing O t m)))).app U
                (strictEtaleBrownRingMap O t h a))).asHom.hom x =
        ((M.val.obj U).smul
          ((coefficientQuotientMap (J := W.smallEtaleTopology) O t h).hom.app U
            ((toSheafify W.smallEtaleTopology
              ((Functor.const W.Etaleᵒᵖ).obj
                (CommRingCat.of (strictEtaleBrownRing O t n)))).app U a))).asHom.hom x
      have hu := congrArg (fun f ↦ f.app U a)
        (toSheafify_naturality W.smallEtaleTopology
          ((Functor.const W.Etaleᵒᵖ).map
            (CommRingCat.ofHom (strictEtaleBrownRingMap O t h))))
      exact congrArg (fun r ↦ ((M.val.obj U).smul r).asHom.hom x) hu)
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

set_option maxHeartbeats 2000000 in
-- The normalization transports adjunctions between two concrete derived-category universes.
/-- Normalize the comparison maps while retaining the supplied derived functors and
factorizations. Arbitrary comparison isomorphisms are not automatically normalized.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CY, 06YY and 07A4.
(blueprint: lem-pur-etale-brown-level-realization-coherence).

Proof: naturality of the constant-ring sheafification unit makes the identity on
sections linear for scalar restriction. Lift that square through localization,
using the supplied factorization maps. The inverse mate is invertible because
both realization functors are equivalences. Use its inverse as the scalar
comparison. Its mate equation is the inverse law of the mate equivalence.
All arguments include identity quotient maps and the zero quotient ring. -/
theorem etaleBrownLevelRealizationCoherence_exists
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t)
    (R : StrictEtaleBrownRealizationData O t W P) :
    Nonempty (StrictEtaleBrownRealization O t W P) := by
  let := R.ordinaryAdditive
  let := R.equivalence
  have hd {m n : ℕ} (h : m ≤ n) := exists_derivedSquare_independentUniverses
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (strictEtaleBrownConstant O t W m) (strictEtaleBrownConstant O t W n)
    (Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (P.scalar h).restriction (R.derived m) (R.derived n)
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (P.scalar h).restrictionFactors (R.factors m) (R.factors n)
    (Sheaf.restrictScalars W.smallEtaleTopology
      (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors
    (ordinaryRestrictionIso O t W h)
  choose restriction hrestriction using @hd
  let scalar {m n : ℕ} (h : m ≤ n) :
      (P.scalar h).derived ⋙ R.derived m ≅
      R.derived n ⋙ Etale.scalarExtension (strictEtaleBrownRingMap O t h) W := by
    letI := isIso_inverseMate_of_equivalences (P.scalar h).derivedAdj
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h))) (restriction h)
    exact (asIso (((mateEquiv (P.scalar h).derivedAdj
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)))).symm
      (.mk _ _ _ _ (restriction h).hom)).natTrans)).symm
  let R' : StrictEtaleBrownRealizationData O t W P :=
    { ordinaryAdditive := R.ordinaryAdditive
      derived := R.derived
      factors := R.factors
      equivalence := R.equivalence
      ordinaryRestriction := ordinaryRestrictionIso O t W
      restriction := restriction
      scalar := scalar }
  refine ⟨⟨R', ?_⟩⟩
  change (∀ {m n : ℕ} (h : m ≤ n) (M : strictEtaleLevel W O t m)
      (U : W.Etaleᵒᵖ) (x : M.val.obj U),
      HEq (((ordinaryRestrictionIso O t W h).hom.app M).hom.app U x) x) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro m n h M U x
    exact HEq.rfl
  · exact hrestriction
  · intro m n h
    exact congrArg (fun s ↦ s.natTrans)
      ((mateEquiv (P.scalar h).derivedAdj
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
          (strictEtaleBrownRingMap O t h)))).apply_symm_apply
            (.mk _ _ _ _ (restriction h).hom))

end AlgebraicGeometry
