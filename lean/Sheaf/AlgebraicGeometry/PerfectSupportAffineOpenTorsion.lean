/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison

/-! # Power torsion on an affine open

Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-perfect-support-affine-open-torsion).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Every local morphism from a restricted perfect source into a shift of a restricted
supported target is killed by a power of the global function on an affine open.
Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-perfect-support-affine-open-torsion).

Proof: Compare localized-site restriction with restriction to the open subscheme U.
Perfectness and quasi-coherence restrict, and the stalk comparison restricts the support
condition. Identify the affine U with Spec of its section ring and use the affine derived
equivalence and bounded finite-projective model. Induct on the number of nonzero terms
of the model, simultaneously for all shifts of the target. The stupid-truncation triangle
at the highest term gives an exact Hom sequence. Kill the image in its single-term Hom
by a power f^a; exactness lifts the resulting map from the shorter model. Induction kills
that lift by f^b, so f^(a+b) kills the original map. For a single projective term in degree
zero, Hom in the derived category is Hom into H^0 of the shifted target. This module
localizes to zero at f by the support hypothesis, so each element is killed by a power
of f. Finitely many generators of the source give one exponent for their images.
Transport back along the exact equivalences. Their compatibility with multiplication
identifies this action with precomposition by the restriction of f^n times identity.
The zero complex and the empty affine open give zero Hom groups. -/
theorem perfect_support_affine_open_torsion
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E E' : schemeDerivedQCohCategory X)
    (hE : X.IsPerfect E.obj)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (k : ℤ) (β : R.obj E.obj ⟶ R.obj (E'.obj⟦k⟧)),
      ∃ n : ℕ, R.map (schemeDerivedScalar X (f ^ n) (𝟙 E.obj)) ≫ β = 0 := by sorry

end AlgebraicGeometry.Scheme
