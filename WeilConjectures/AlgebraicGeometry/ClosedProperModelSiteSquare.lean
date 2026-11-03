/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedProperDerivedFactor
public import WeilConjectures.AlgebraicGeometry.ClosedProperEtaleDerivedFactor
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # The proper forget-supports square between the two sites

Source: the ordered exterior-product and comparison paragraphs of
sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The two explicit clopen-factor maps intertwine the site comparison for a closed map.
Source: blueprint latest, sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered compact-support composition;
parent node proof Step 3 (blueprint: lem-pur-closed-proper-model-site-square).

Proof: write the chosen compactification as X→[j]T→[p]Y. The open j is clopen because
f is proper. The canonical extension comparison is the left mate of restriction,
whereas the direct-image comparison is its right mate. Transpose the comparison
j_!→j_* under restriction/direct image. More explicitly, let e be extension comparison,
r restriction comparison and d the forward direct-image mate. Transpose
 e.inv ≫ ν(j_!→j_*) ≫ d under pro-etale restriction/direct image, and precompose
with the pro-etale open unit. The extension unit equation moves that unit past e.inv;
r.naturality moves the sheaf comparison past restriction comparison; the mate counit
equation then leaves ν applied to the etale open-unit/comparison/counit composite.
That composite is identity, so this transpose equals the transpose of the pro-etale
comparison. Cancel the invertible open unit and the adjunction Hom equivalence.
Derive this forward-mate square, using exact extension and comparison pullback, and
invert the bounded-below direct-image mate using the proper comparison theorem. The comparisons
with the bounded-below inclusions identify it with the ambient square. Paste the
proper factor p: the direct-image comparison respects composition, by the counit
mate composition law. The etale model map is D of the clopen sheaf comparison, the inverse exactness
comparison for j_*, then the direct-image compositor and transport along j;p=f. The pro-etale
path is exactly properModelComparison, by its definition. This argument is independent
of the two theorems identifying these models with the published proper comparisons.
Cancelling the inclusion comparisons gives the stated equality. The argument includes
identity immersions and zero coefficients, and uses no Noetherian hypothesis. -/
theorem closedProperModelSiteSquare (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [HasCompactification f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactSupportSiteComparison A (HasCompactification.compactification f)).hom.app K ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.properEtaleModelComparison A f).hom.app (DerivedCategory.Plus.ι.obj K)) =
    (properModelComparison A f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj K)) ≫
      (rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} A) f).hom.app K := by sorry
end AlgebraicGeometry.ProEtale
