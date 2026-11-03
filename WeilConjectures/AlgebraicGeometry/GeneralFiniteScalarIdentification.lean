/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFiniteDiagonalReductionSide

/-! # Identification of the live and adjunction-defined finite scalar functors

Source: sk-thm-purity-transport proof, Step 1, and sk-lem-sp-reduction.
The identification is constructed from the two adjunctions to the same exact restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

local instance (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The counit-preserving identification of the two actual derived scalar functors.
Source: Stacks 06YY and 07A4; the two adjunctions to exact scalar restriction.
(blueprint: def-pur-general-side-scalar-identification). -/
def sideScalarIdentification
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ T)] :
    sideScalar φ T ≅ Etale.FiniteSmoothPurity.proScalar φ T := by
  letI : Algebra A B := φ.toAlgebra
  exact (leftDerivedSheafExtendScalarsAdjunction A B T).leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ))

/-- The live scalar/site square agrees with the adjunction-defined square.
Source: sk-thm-purity-transport proof, Step 1 (canonical source identifications).
(blueprint: lem-pur-general-side-scalar-identification).

Proof: put F = nu_A^*, G = nu_B^*, E = etaleSheafExtendScalars phi T and
H = sheafExtendScalars phi T. Write R_e and R_p for exact scalar restrictions.
The underived isomorphism beta : E composed with G is isomorphic to F composed
with H is the balancing isomorphism. Its inverse has restriction mate the
canonical square R_e composed with F to G composed with R_p. This follows by
transposing the ordinary extension units, or equivalently by the iterated-mate
identity for the sectionwise coextension square.

Let s : D(F) composed with L(H) is isomorphic to L(E) composed with D(G) be the
mixed derived square used in sideComparisonReductionIso, before its etale scalar
adjoint identification. Its localization equation is s followed by the E/G mixed
counit equals the F/H mixed counit followed by Qh(beta inverse). The counits of
the derived scalar adjunctions, on Qh of a complex, are the scalar derived counit
followed by Qh of the ordinary scalar adjunction counit, with the exact restriction
comparison inserted. This is the derived-epsilon factorization and the exact
restriction right-derived comparison equation. For H this is the published
leftDerivedSheafExtendScalarsAdjunction_counit_app_Qh_obj; for E use the same
derived-epsilon factorization for its sheaf adjunction. Consequently
Adjunction.mateEquiv_leftDerived_inv_eq, with Lbeta = s inverse, says that the
restriction mate of s is precisely the exact derived restriction/site square.
The hypotheses of this calculation are exactly those already used to construct s:
comparison is exact and preserves K-flat complexes, and E and H have their total
left derived functors. No cohomological bound on the input is involved.

Finally, replace L(E) by the chosen etale scalar adjoint and L(H) by the chosen
pro-etale scalar adjoint. Both replacements are their specified leftAdjointUniq
isomorphisms, so mateEquiv_leftAdjointUniq preserves the just-computed restriction
mate. The resulting square is the mate defining pbcComparisonReduction. On the
other side it is, by definition, sideComparisonReductionIso. Injectivity of the
mate equivalence identifies these natural transformations. Evaluate at L to get
the displayed equation. No coefficient flatness is used. -/
theorem sideComparisonReduction_identification
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ T)]
    (L : Etale.DerivedCategoryModule A T) :
    (sideScalarIdentification φ T).hom.app
        ((Etale.FiniteSmoothPurity.comparison A T).obj L) ≫
        (pbcComparisonReduction T φ).hom.app L =
      (sideComparisonReductionIso (T := T) φ).hom.app L := by
  sorry

end AlgebraicGeometry.ProEtale
