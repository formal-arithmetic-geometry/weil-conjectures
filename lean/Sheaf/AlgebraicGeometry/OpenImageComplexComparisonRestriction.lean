/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.OpenImageComplexComparisonIso

/-! # Nested-open compatibility for the explicit comparison

Source: Stacks Project, Cohomology, Tags 08BS and 08BV.
(blueprint: lem-pc-open-image-complex-comparison-restriction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

/-- The constructed comparisons intertwine the fixed termwise restriction with
its derived adjunction mate, for one inclusion of opens.
Source: Stacks Project, Cohomology, Tag 08BV (lemma-exact-sequence-j-star),
first paragraph of the proof and the restriction arrow in its displayed sequence.

Proof: Write L_A for exact restriction and R_A for underived open direct image.
Restriction of I to A and W is K-injective by Tag 08BS, including after transport
along the open-site equivalences. The comparison before right-adjoint normalization
is the inverse computation isomorphism for R_A, followed by R_A of the inverse
exact-restriction localization isomorphism. The fixed underived restriction is the
mate under L_W adjoint to R_W of alpha inverse at R_A L_A I, followed by restriction
of the A-counit, followed by alpha at I. Apply Q to this formula. The derived-unit
and derived-counit factorization identities identify its transpose under the derived
W-adjunction with the same composite, now using derived counits and the derived
nested-restriction comparison. The characterizing factorization identities of
mapDerivedCategoryCompIso and mapDerivedCategoryNatIso identify the localization
of alpha with schemeDerivedOpenRestrictionCompIso. Thus the resulting mate is
schemeDerivedOpenDirectImageRestriction for the canonical derived adjunctions.
For each supplied adjunction normalize by beta_A, the canonical rightAdjointUniq
isomorphism. Its unit and counit identities give eta_supplied = eta_canonical beta_A
and L_A(beta_A) epsilon_supplied = epsilon_canonical. Substitution in the mate and
naturality of beta_W give beta_A rho_supplied = rho_canonical beta_W, exactly the
asserted equation after normalization. This uses no covering or termwise injectivity
hypothesis. For W=A the canonical identification is transported through the two
supplied adjunction comparisons; these adjunctions need not coincide. For W empty
both target objects vanish.
(blueprint: lem-pc-open-image-complex-comparison-restriction). -/
theorem schemeOpenModuleImageComplexComparison_restriction
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjW : (schemeOpenRestriction X W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι) :
    DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X i I) ≫
        (schemeOpenModuleImageComplexComparison X W I adjW).hom =
      (schemeOpenModuleImageComplexComparison X U I adjU).hom ≫
        schemeDerivedOpenDirectImageRestriction X i adjU adjW (DerivedCategory.Q.obj I) := by sorry

end AlgebraicGeometry
