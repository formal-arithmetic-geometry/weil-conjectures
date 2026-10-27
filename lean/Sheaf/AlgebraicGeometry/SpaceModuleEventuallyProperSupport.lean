/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence

/-! # Eventual properness of scheme-theoretic module support

Source: Stacks Project, Limits of Spaces, Tag 08K2, lemma-eventually-proper-support,
in Situation 084W, specialized to finitely presented spaces and modules over affine bases
(blueprint: lem-sfb-space-module-eventually-proper-support).

The base change squares specify the ordinary fibre products up to their unique comparison.
The support predicate retains the annihilator ideal on every affine open of every chart.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Properness of the annihilator support of a finitely presented module at the limit
holds at some stage, without flatness of either the module or the transition maps.
Source: Stacks Project, Limits of Spaces, Tag 08K2 and Situation 084W
(blueprint: lem-sfb-space-module-eventually-proper-support).

Proof:
1. Let W0 be the closed subspace defined by Ann(M0), using
   lem-sfb-space-module-proper-carrier-support. Finite generation and the affine
   localization criterion identify its point set with the module support; use
   lem-sfb-space-etale-chart-support on charts. Since the base is affine and the
   space is finitely presented, lem-sfb-space-qcqs-source-products makes X0 qcqs.
   A closed subspace of it is qcqs, and W0 is locally finite type over the base.
   No finite generation of the annihilator ideal is claimed.
2. At every stage and at the limit, the extended annihilator ideal annihilates the
   tensor pullback module. By lem-sfb-space-closed-ideal-correspondence this gives
   a closed immersion of the new annihilator support into the base change of W0.
   By lem-sfb-space-finite-type-support-pullback their point sets agree, so this
   immersion is a thickening. Annihilator ideals need not commute with base change.
3. At the limit, the support is proper by hypothesis. Apply
   lem-sfb-space-thickening-topological-properties to deduce separatedness,
   quasi-compactness and universal closedness of the base change of W0.
   Its locally finite type property is preserved by base change, so it is proper.
4. Apply lem-sfb-space-finite-type-eventually-proper to W0 to obtain a stage j
   at which its base change is proper. The fibre product over the original base
   is canonically the fibre product over X0, by the pullback universal property.
5. The annihilator support at j is a closed subspace of this proper space by step 2.
   Use lem-sfb-space-closed-subspace-proper and lem-sfb-space-proper-composition
   to conclude its properness over the stage base. -/
theorem module_eventually_hasProperAnnihilatorSupport
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (haff : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (htrans : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left)
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f₀ : X₀ ⟶ schemeSpace (D.obj (op i₀)))
    (hqc : MapIsQuasiCompact f₀.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f₀.hom.hom))
    (hlfp : MapIsLocallyOfFinitePresentation f₀)
    (M₀ : X₀.QCoh) (hM₀ : M₀.obj.IsFinitePresentation)
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (p : X ⟶ X₀) (f : X ⟶ schemeSpace c.pt)
    (sq : IsPullback p.hom f.hom f₀.hom
      (ObjectProperty.homMk ⟨yoneda.map (c.π.app (op i₀))⟩ :
        schemeSpace c.pt ⟶ schemeSpace (D.obj (op i₀))).hom)
    (Xᵢ : {j : I // i₀ ≤ j} → AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (pᵢ : ∀ j : {j : I // i₀ ≤ j}, Xᵢ j ⟶ X₀)
    (fᵢ : ∀ j : {j : I // i₀ ≤ j}, Xᵢ j ⟶ schemeSpace (D.obj (op j.val)))
    (sqᵢ : ∀ j : {j : I // i₀ ≤ j}, IsPullback (pᵢ j).hom (fᵢ j).hom f₀.hom
      (ObjectProperty.homMk ⟨yoneda.map (D.map (homOfLE j.property).op)⟩ :
        schemeSpace (D.obj (op j.val)) ⟶ schemeSpace (D.obj (op i₀))).hom)
    (hsupp : HasProperAnnihilatorSupport f ((moduleTensorPullback p).obj M₀.obj)) :
    ∃ j : {j : I // i₀ ≤ j},
      HasProperAnnihilatorSupport (fᵢ j) ((moduleTensorPullback (pᵢ j)).obj M₀.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
