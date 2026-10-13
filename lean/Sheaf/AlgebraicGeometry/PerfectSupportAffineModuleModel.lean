/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison

/-! # Affine module models with supported cohomology

Source: Stacks Project, Tags 08EJ, 08EB and 06Z0.
(blueprint: lem-sc-perfect-support-affine-module-model).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Affine restriction admits a bounded finite-projective source model and a target
whose cohomology is elementwise power torsion. The comparison is full and additive
and intertwines the scalar identity of the source with restriction of global scalars.
Source: Stacks Project, Tag 08EJ, affine paragraph; Tags 08EB and 06Z0.
(blueprint: lem-sc-perfect-support-affine-module-model).

Proof: Compare localized-site restriction with restriction to the open subscheme U
using open_derived_restriction_comparison. Perfectness restricts: intersect each
strictly perfect neighbourhood with U and restrict the finite-free retractions.
Quasi-coherence and stalkwise support restrict by the comparison theorem, including
for the shifted target. Identify U with Spec of its section ring A using its affine
presentation. The affine derived equivalence, followed by transport through this
scheme isomorphism and the inverse localized-site comparison, gives F. These functors
are fully faithful and additive. The bounded-projective criterion applied to the
restricted perfect source gives P, its bounds, finite and projective terms, and eP.
Choose the inverse-equivalence image M of the restricted shifted target and the
counit isomorphism eM. Exactness identifies H^i(M) with the corresponding affine
module of the restricted cohomology sheaf. Its localization at the restricted f is
zero, since its stalks vanish on D(f). The localization zero criterion makes every
cohomology element power torsion. Finally, associated sheaf, open restriction and
scheme-isomorphism transport all act sectionwise, so multiplication by the component
of any global scalar a at U corresponds to restriction of schemeDerivedScalar X a.
This gives the displayed identity after composing with eP.hom. When U is empty, A is
the zero ring and all these categories are zero; the zero models give the same data.
No assertion about torsion of derived morphisms is used in this construction. -/
theorem perfect_support_affine_module_model
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
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ)
      (M : DerivedCategory (ModuleCat.{u} A))
      (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      F.Full ∧ F.Additive ∧
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Finite A (P.X i)) ∧
      (∀ i : ℤ, Module.Projective A (P.X i)) ∧
      (∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M),
        ∃ n : ℕ, (f.val (op U)) ^ n • m = 0) ∧
      ∃ (eP : F.obj (DerivedCategory.Q.obj P) ≅ R.obj E.obj)
        (eM : F.obj M ≅ R.obj (E'.obj⟦k⟧)),
        ∀ a : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}),
          F.map ((show A from a.val (op U)) • 𝟙 (DerivedCategory.Q.obj P)) ≫ eP.hom =
            eP.hom ≫ R.map (schemeDerivedScalar X a (𝟙 E.obj)) := by sorry

end AlgebraicGeometry.Scheme
