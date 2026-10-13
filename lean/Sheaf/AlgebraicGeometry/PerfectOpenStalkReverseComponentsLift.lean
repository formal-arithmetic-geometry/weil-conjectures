/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Lifting reverse-degree stalk components

Source: Stacks Project, Tags 09RE, 0BC7 and 01CP.
(blueprint: lem-sc-perfect-open-stalk-reverse-components-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Lift reverse-degree stalk components without imposing differential equations.
Source: Stacks Project, Tag 09RE, affine case (1); Tag 0BC7 (2);
Tag 01CP, finitely presented internal Hom comparison.
(blueprint: lem-sc-perfect-open-stalk-reverse-components-lift).

Proof: Choose the support interval and the finite-free retractions for P.
Restriction preserves zero terms and these retractions. There are only finitely
many reverse-degree pairs inside the support interval. Sandwich each given stalk
map between the stalk retractions, giving a finite matrix of structure-ring
stalk elements. Represent every entry by a section on a neighbourhood inside T
and intersect the finitely many neighbourhoods. Restrict the retractions and
sandwich the lifted matrices back to obtain k. Set k to zero outside the support
interval and outside the reverse-degree relation. The zero-source or zero-target
criterion proves agreement for every discarded pair. The open-subscheme stalk
comparison gives e: restriction to Z followed by the stalk equals the stalk on V.
Its naturality and preservation of the splitting identities prove the displayed
component equality. Empty support, rank zero, and non-Noetherian stalk rings
require no extra hypotheses. This constructs only components, not a homotopy. -/
theorem exists_perfect_open_stalk_reverse_components_lift
    (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (x : X) (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
    (T : X.Opens) (hTV : T ≤ V) (hxT : x ∈ T)
    (h : ∀ i j : ℤ,
      ((openModuleStalkFunctor X V ⟨x, hxV⟩).obj
        ((((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P).X i)) ⟶
      ((openModuleStalkFunctor X V ⟨x, hxV⟩).obj
        ((((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P).X j)))
    (hzero : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0) :
    ∃ (Z : X.Opens) (hZT : Z ≤ T) (hxZ : x ∈ Z),
      let PV := ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P
      let R := (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (hZT.trans hTV))).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X Z ⟨x, hxZ⟩).mapHomologicalComplex (.up ℤ)
      let F := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      ∃ (e : R ⋙ S ≅ F) (k : ∀ i j : ℤ, (R.obj PV).X i ⟶ (R.obj PV).X j),
        (∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → k i j = 0) ∧
        ∀ i j, (openModuleStalkFunctor X Z ⟨x, hxZ⟩).map (k i j) =
          (e.app PV).hom.f i ≫ h i j ≫ (e.app PV).inv.f j := by sorry

end
end AlgebraicGeometry.Scheme
