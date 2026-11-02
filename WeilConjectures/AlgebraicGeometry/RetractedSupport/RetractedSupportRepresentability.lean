/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportLocalizationComparison
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Representability of the supported-section inclusion on etale inputs

Source: the supported-Hom identification in the latest blueprint's proof of
`lem-pur-gysin-structure` (blueprint: lem-pur-retracted-support-representability).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.RetractedSupport

variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s]

/-- The ambient ordinary etale coefficient object.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportAmbientCoefficient : EtSheaves P X :=
  (constantSheaf X.smallEtaleTopology (Modules P)).obj (ModuleCat.of P.Coefficient P.Coefficient)

/-- The ordinary closed etale coefficient object.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportClosedCoefficient : EtSheaves P X :=
  (Etale.supportedCoefficients P.Coefficient s).obj (ModuleCat.of P.Coefficient P.Coefficient)

/-- The single-object realization before the epimorphism is used.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportSingle := DerivedCategory.singleFunctor (EtSheaves P X) 0

/-- Test objects are shifted ordinary bounded-below etale inputs, in the ambient category.
Source: fixed-degree Yoneda calculation
(blueprint: lem-pur-retracted-support-representability). -/
abbrev supportTests (q : ℤ) :=
  (DerivedCategory.Plus.ι : DerivedCategory.Plus (EtSheaves P X) ⥤ _) ⋙
    shiftFunctor (DerivedCategory (EtSheaves P X)) q

/-- The support groups, with the module structure forgotten only for Yoneda.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportValues (q : ℤ) :=
  nuPlus P X ⋙ Sheaf.supportHypercohomologyFunctor
    (Scheme.ProEt.topology X) (Modules P) (supportRestrictionArrow s) q ⋙ forget (Modules P)

/-- The ambient section groups in the same coordinates.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportAmbientValues (q : ℤ) :=
  nuPlus P X ⋙ Sheaf.sectionHypercohomologyFunctor
    (Scheme.ProEt.topology X) (Modules P) (Scheme.ProEt.mk (𝟙 X)) q ⋙ forget (Modules P)

/-- The actual supported-section inclusion, viewed as a transformation of sets.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
def supportForgetValues (q : ℤ) : supportValues P s q ⟶ supportAmbientValues P (X := X) q :=
  Functor.whiskerRight
    (Functor.whiskerLeft (nuPlus P X)
      (Sheaf.supportHypercohomologyInclusion (Scheme.ProEt.topology X) (Modules P)
        (supportRestrictionArrow s) q)) (forget (Modules P))

/-- Two ordinary Hom representations and the equation representing forgetting support.
This structure contains no comparison of exceptional functors and no Gysin morphism.
Source: closed-support Hom and the quotient normalization
(blueprint: lem-pur-retracted-support-representability). -/
structure SupportRepresentability (q : ℤ) where
  supported : supportValues P s q ≅
    supportTests P (X := X) q ⋙ coyoneda.obj (op ((supportSingle P).obj
      (supportClosedCoefficient P s)))
  ambient : supportAmbientValues P (X := X) q ≅
    supportTests P (X := X) q ⋙ coyoneda.obj (op ((supportSingle P).obj
      (supportAmbientCoefficient P (X := X))))
  quotient_epi : Epi (Etale.supportedCoefficientQuotient P.Coefficient s
    (ModuleCat.of P.Coefficient P.Coefficient))
  forget_eq : ∀ (B : DerivedCategory.Plus (EtSheaves P X))
    (x : (supportValues P s q).obj B),
    ambient.hom.app B ((supportForgetValues P s q).app B x) =
      (supportSingle P).map (Etale.supportedCoefficientQuotient P.Coefficient s
        (ModuleCat.of P.Coefficient P.Coefficient)) ≫ supported.hom.app B x

/-- Fixed-degree supported cohomology and ambient cohomology admit ordinary etale Hom
representations which turn forgetting support into precomposition by the coefficient
quotient. Source: `lem-pur-supported-hom.proof.md` and the second assertion of
`lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-retracted-support-representability).

Proof:
1. On a bounded-below injective complex, evaluation at one identifies supported sections
   with Hom from the ordinary closed constant coefficient object. The quotient
   normalization identifies the kernel inclusion with precomposition by the ambient
   constant quotient. Apply this degreewise and then pass to homology and localization.
2. The finite etale/pro-etale comparison is fully faithful on D+. The canonical closed
   direct-image mate identifies the pro-etale supported constant with the inverse image
   of the displayed etale coefficient. Its constant-unit equation fixes the scalar.
   The analogous constant comparison gives the ambient representation.
3. Derive the kernel-inclusion square. The derived-unit equations identify the two
   right-derived constructions on injectives, and naturality transports the square to
   every bounded-below input. Retain q as fixed throughout; no compatibility between
   arbitrarily chosen support isomorphisms in different degrees is asserted.
4. The ordinary quotient is the constant-sheaf image of the closed inverse-image unit.
   Its cokernel restricts to zero on both the closed part and its open complement;
   conservativity of the closed/open restrictions makes that cokernel zero. Hence the
   quotient is an epimorphism in sheaves, before applying the single functor.
   These constructions also apply to the zero coefficient module and empty schemes. -/
theorem supportRepresentability_exists [IsLocallyNoetherian X] (q : ℤ) :
    Nonempty (SupportRepresentability P s q) := by
  sorry

end AlgebraicGeometry.ProEtale.RetractedSupport
