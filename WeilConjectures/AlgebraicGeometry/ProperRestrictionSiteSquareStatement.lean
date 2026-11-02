/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar

/-!
# The finite-discrete restriction/site square

Source: the nested blueprint source
`literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/sec-n-change/`
`sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md`, (2) Formal properties,
restriction of scalars, and Finite rings, first paragraph; Stacks 03D2, 099R, 07A7.
(blueprint: lem-sf-proper-restriction-site-square).

We use the exact section-action equivalence for the pulled-back discrete condensed rings.
The displayed square is in its ordinary constant-coefficient coordinates. All four maps are
canonical: the scalar/site identity, the site counit mate, and the two geometric scalar mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The scalar/site identity on sheaves. Its right-adjoint conjugate is the sectionwise
identity: coextension of scalars is postcomposition and comparison direct image is
precomposition. This fixes the comparison, including its unit normalization.
Source: Stacks 03D2 (blueprint: lem-sf-proper-restriction-site-square). -/
def properRestrictionComparisonSheaf
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (T : Scheme.{u}) (φ : A →+* B) :
    Sheaf.restrictScalars T.smallEtaleTopology φ ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
      comparisonUpperStar (ModuleCat.{u + 1} B) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ :=
  (conjugateIsoEquiv
    ((comparisonAdjunction (ModuleCat.{u + 1} B) T).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ))
    ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).comp
      (comparisonAdjunction (ModuleCat.{u + 1} A) T))).symm (Iso.refl _)

/-- Exact termwise descent of the normalized scalar/site identity, restricted to D+.
Thus this is δ_T in the direction ν_A U^e → U^p ν_B.
Source: Stacks 03D2 and 015F (blueprint: lem-sf-proper-restriction-site-square). -/
def properRestrictionComparisonPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (T : Scheme.{u}) (φ : A →+* B) :
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        siteComparisonDerivedPullbackPlus T A ≅
      siteComparisonDerivedPullbackPlus T B ⋙
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (properRestrictionComparisonSheaf T φ) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _

/-- The inverse geometric pro-etale scalar mate c_p. The data is the specified sectionwise
base-change map `rightDerivedLowerStarRestrictScalars` (the right-derived mate of the identity
f_* ∘ res = res ∘ f_*), and its invertibility is the recorded upstream instance
`isIso_rightDerivedLowerStarRestrictScalars` (restricted injectives are f_*-acyclic), so
restriction is not required to preserve injectives.
Source: Stacks 0D6E and 015F (blueprint: lem-sf-proper-restriction-site-square). -/
def properRestrictionScalarPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus ≅
      (lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctorPlus ⋙
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryPlus :=
  (asIso (rightDerivedLowerStarRestrictScalars φ p)).symm

/-- The inverse of the recorded canonical counit mate β_C, entirely in D+.
Source: Stacks 099R and 07A7; blueprint direct-image proof, Finite rings
(blueprint: lem-sf-proper-restriction-site-square). -/
def properRestrictionBoundaryPlus
    (C : Type (u + 1)) [CommRing C] [Finite C]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p] :
    siteComparisonDerivedPullbackPlus X C ⋙
        (lowerStar (ModuleCat.{u + 1} C) p).rightDerivedFunctorPlus ≅
      Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} C) p ⋙
        siteComparisonDerivedPullbackPlus Y C :=
  (@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus C p)
    (isIso_fixedComparisonDirectImageMatePlus C p)).symm

/-- The normalized bounded-below scalar/site square for finite discrete condensed rings,
for arbitrary finite rings in the scalar universe u+1.

Source: the nested blueprint source
`literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/sec-n-change/`
`sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md`, (2) Formal properties,
restriction-of-scalars sentence, and Finite rings, first paragraph; Stacks 03D2, 099R, 07A7
(blueprint: lem-sf-proper-restriction-site-square).

Proof (the four DAG steps):
1. Use moduleObject_ordinary_coefficient_equivalence to identify internal modules over
p_T^* underline C with ordinary constant-C module sheaves. Restriction changes the action
only, a·m = φ(a)m. The scalar/site δ and geometric pullback α are the underlying canonical
inverse-image identifications with exactly this action, not arbitrary endpoint isomorphisms.
2. The inverse-image cube commutes before deriving: after forgetting the scalar action,
both paths are the canonical f_proet^{-1} ν_Y^{-1} → ν_X^{-1} f_et^{-1}. The two actions
both restrict through φ. Exact termwise localization carries this equality, and its
composition identifications, to D+. The site pullback face is the recorded comparison.
3. Normalize geometric mates with the computed bounded-below square-mate formula. The module
sheaf categories are Grothendieck abelian and have enough injectives. Restriction and inverse
image are exact; the ordinary direct-image scalar face is the sectionwise identity. Its
derived mate is the canonical resolution comparison, invertible by the recorded pro-etale
scalar theorem and the etale scalar comparison. Restriction need not preserve injectives.
The recorded fixedComparisonDirectImageMatePlus makes precisely β_C invertible for qcqs p
and finite C; apply it over A and B since restricted L remains bounded below.
4. Take geometric mates of the cube in step 2 and paste. This gives
ν_A(k_e); β_A U^e; G_A^p(δ_X) = δ_Y G_B^e; U^p(β_B); k_p ν_B.
Precompose with b_A U^e; ν_A(c_e), postcompose with c_p ν_B; U^p(b_B), and cancel the
adjacent inverse pairs. Evaluation at L gives the displayed equation. The full D+ inclusion
is faithful and inserts the canonical exact/right-derived inclusion comparisons on both paths.
-/
theorem properRestrictionSiteSquare_statement
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map
        ((properRestrictionComparisonPlus X φ).hom.app L) ≫
      (properRestrictionScalarPlus φ p).hom.app
        ((siteComparisonDerivedPullbackPlus X B).obj L) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryPlus.map
        ((properRestrictionBoundaryPlus B p).hom.app L) =
    (properRestrictionBoundaryPlus A p).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (siteComparisonDerivedPullbackPlus Y A).map
        ((Etale.derivedLowerStarRestrictScalarsIso φ p).inv.app L) ≫
      (properRestrictionComparisonPlus Y φ).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) p).obj L) := by
  sorry

end AlgebraicGeometry.ProEtale
