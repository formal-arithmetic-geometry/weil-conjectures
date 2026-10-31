/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKummerNormalizedStalkDefinitions

/-! Strict-local Kummer comparison before inversion of the geometric pullback.
Source: blueprint latest, relative Kummer calculation, Step 2.
(blueprint: new-pur-relative-kummer-normalized-stalks-local). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The specified strict-local comparison respects edge classes and constants,
and the two geometric pullbacks give the same coordinate Kummer class.
Source: blueprint latest, prop-pur-gm-relative-kummer.proof.md, Step 2; Stacks 03Q9 and 03PL.
(blueprint: new-pur-relative-kummer-normalized-stalks-local).

Proof: Write f for the family projection, g for the strict-local structural map,
and v for its base change. First, on ordinary module sheaves, the global germ followed
by moduleStrictLocalRestriction is global sections of the g-adjunction unit followed
by lowerStarCompGlobalSectionsIso. To check this, choose a pointed affine neighbourhood
in the stalk colimit. Its restriction is the inverse-image unit followed by the chosen
strict-local section. The section and the map to the terminal neighbourhood have the
same composite to the pulled-back terminal object, since that object is terminal.
Naturality of section restriction proves the equality on every colimit representative.
Derive this equality using right-derived extensionality and the defining unit equations
of the exact-stalk, exact-sections and composition comparisons. The exchange mate-unit
equation, followed by associativity of Leray, identifies EdgeGerm followed by Theta
with the specified v-pullback, including its root-line coefficient comparison. Apply
Hq to obtain the first assertion.
For constants, the constant-sheaf/sections unit followed by the ordinary global germ
is the inverse constant-stalk comparison: after evaluating at the terminal object,
this is the constant-presheaf germ equation and naturality of sheafification. Apply
the derived mate-unit equation to the untwisted unit, and use that coefficient
pullback sends zeta tensor a to zeta tensor a. The structure maps compose, so the
result is the absolute constant-section map followed by the specified h-pullback.
For the coordinate class, naturality of the ordinary Kummer connecting map identifies
the pullback of kappa(w) with kappa of the pulled-back unit. Coefficient insertion
commutes with pullback. Injectivity of the arbitrary-base ordinary class bijection,
using the general-degree class_pullback calculation, identifies the corresponding
normalized derived arrows. Transpose under the constant-sheaf/sections adjunction,
apply shifted homology, and use naturality of total/Plus compatibility. The two
coordinate units agree on the strict-local family by its projection equations,
which gives the third assertion. The affine-line clause is True. No invertibility,
prime-power, finite-free or algebraically closed base-field assumption is used. -/
theorem relativeKummer_normalized_stalks_local
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] (hmk : IsUnit (m : k)) {ζ : k}
    (hζ : IsPrimitiveRoot ζ m) {B : Scheme.{u}} (p : B ⟶ Spec (.of k)) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B) (b : Bool),
      (∀ q : ℕ,
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
            (normalizedKummerEdgeGerm A m hA (normalizedKummerProjection p b) s) ≫
          (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
            (normalizedKummerTheta A m hm hA hmk p b s) =
          (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
            (normalizedKummerV A m hm hA hmk p b s)) ∧
      (normalizedKummerUnitGerm A m hm hA hζ p (normalizedKummerProjection p b)
          (relativeKummerExponentUnit m hmk B p)
          (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)) s ≫
        normalizedKummerTheta A m hm hA hmk p b s =
        normalizedKummerGlobalSection A m hA _
            (normalizedKummerConstantMap A m hm hA hζ _ (KummerLine.structureMap k b)) ≫
          normalizedKummerH A m hm hA hmk p b s) ∧
      (match b with
      | false => True
      | true =>
        normalizedKummerGeneratorPlusMap A m hA _
            (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))
            (Units.map (pullback.fst (KummerLine.structureMap k true) p).appTop.hom.toMonoidHom
              (KummerLine.coordinateUnit k)) ≫
          (DerivedCategory.Plus.homologyFunctor _ 1).map
            (normalizedKummerV A m hm hA hmk p true s) =
        normalizedKummerGeneratorPlusMap A m hA _
            (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k true))
            (KummerLine.coordinateUnit k) ≫
          (DerivedCategory.Plus.homologyFunctor _ 1).map
            (normalizedKummerH A m hm hA hmk p true s)) := by
  sorry

end AlgebraicGeometry.Etale
