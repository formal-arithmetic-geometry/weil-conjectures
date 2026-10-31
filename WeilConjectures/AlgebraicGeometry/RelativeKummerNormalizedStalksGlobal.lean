/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKummerNormalizedStalkDefinitions

/-! Canonical total and bounded-below Kummer-edge coherence for the punctured line.
(blueprint: new-pur-relative-kummer-normalized-stalks-global). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Comparison of the relative total-derived edge map and bounded-below global edge germ.
Source: blueprint latest, prop-pur-gm-relative-kummer.proof.md, Step 2,
normalization and conservative-stalk paragraphs; Stacks Tags 03PL and 03Q9.
(blueprint: new-pur-relative-kummer-normalized-stalks-global).

Proof in words: For the edge identity, expand the derived adjunction defining the relative edge
and the constant-sheaf/sections adjunction defining the global class map. The
compatibility of total and bounded-below derived direct image and sections is
natural, and its Leray comparison agrees with composition of the two derived
adjunctions. Apply the exact stalk functor and its homology comparison. The two
adjunction triangle identities identify the resulting map with the global edge
germ. Shift coherence then identifies degree zero of the shifted Kummer class
with degree one, giving the displayed identity. This is a coherence statement
for the specified arrows and does not assert any strict-local comparison or
isomorphism. Empty schemes and zero coefficient rings cause no exception. -/
theorem relativeKummer_normalized_stalks_global
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {k : Type u} [Field k] (hmk : IsUnit (m : k))
    {B : Scheme.{u}} (p : B ⟶ Spec (.of k)) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso (ModuleCat.of A A)).inv ≫
        ((Scheme.pointSmallEtale s).sheafFiber
          (A := ModuleCat.{u + 1} A)).map
            (normalizedKummerRelativeGenerator A m hA p
              (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))) ≫
        ((Scheme.pointSmallEtale s).sheafFiber
          (A := ModuleCat.{u + 1} A)).map
            ((DerivedCategory.homologyFunctor _ 1).map
              ((lowerStar (ModuleCat.{u + 1} A)
                (normalizedKummerProjection p true)).rightDerivedFunctorPlusCompatibility.inv.app
                  (relativeKummerLinePlus A m hA _))) ≫
        (((Scheme.pointSmallEtale s).sheafFiber
          (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlusHomologyFunctorIso 1).hom.app
            (normalizedKummerImage A m hA (normalizedKummerProjection p true)) =
      normalizedKummerGeneratorPlusMap A m hA _
          (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))
          (Units.map (pullback.fst (KummerLine.structureMap k true) p).appTop.hom.toMonoidHom
            (KummerLine.coordinateUnit k)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 1).map
          (normalizedKummerEdgeGerm A m hA (normalizedKummerProjection p true) s)) := by
  sorry

end AlgebraicGeometry.Etale
