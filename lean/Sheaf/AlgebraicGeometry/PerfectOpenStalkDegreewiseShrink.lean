/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Killing the differential defects of a degreewise family

Source: Stacks Project, Tags 09RE and 01CP.
(blueprint: lem-sc-perfect-open-stalk-degreewise-shrink).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A degreewise family already defined near x becomes a chain map after shrinking
if its stalk commutes with the differentials. The second conclusion records the
stalks of the restricted components in the original comparison coordinates.

Source: Stacks Project, Tag 09RE, finite-presentation shrinking calculation, and
Tag 01CP, injectivity of the internal-Hom stalk comparison.
(blueprint: lem-sc-perfect-open-stalk-degreewise-shrink).

Proof: For each adjacent degree form the difference of g n followed by d_Q and
of d_P followed by g (n+1). The hypothesis says its stalk is zero. Finite
presentation of P.X n and injectivity of the internal-Hom stalk comparison say
that this is a zero germ of a local morphism. The germ equality criterion gives
a neighbourhood on which that morphism vanishes. Only degrees n in the bounded
support interval of P need checking; outside it the source P.X n is zero.
Intersect these finitely many neighbourhoods inside W and choose an affine V
containing x. Restrict the family to V, using transitivity of overMap to regard
its components as maps between the direct restrictions from U. This gives k
and all adjacent chain equations. The canonical comparison between the V stalk
and the W stalk after restriction, composed with e, gives eV. Naturality and
restriction transitivity give the displayed conjugation formula for k. The
comparison is natural for every complex, not just P and Q. With an empty support
interval or rank zero the corresponding equations and maps are unique. This
lemma extends no prescribed map: it starts with a family already defined on W.
No perfectness hypothesis on Q is needed. -/
theorem exists_affine_perfect_open_stalk_degreewise_shrink
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U)
    (e :
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ) ⋙
      (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ) ≅
      (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ))
    (g : ∀ n : ℤ,
      (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P).X n ⟶
      (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q).X n)
    (hcomm : ∀ n : ℤ,
      (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
        (((openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)).obj
          (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q)).d n (n + 1) =
      (((openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)).obj
        (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P)).d n (n + 1) ≫
        (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g (n + 1))) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (_hVW : V ≤ W) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      ∃ (eV : R ⋙ S ≅ T) (k : ∀ n : ℤ, (R.obj P).X n ⟶ (R.obj Q).X n),
        (∀ n : ℤ, k n ≫ (R.obj Q).d n (n + 1) =
          (R.obj P).d n (n + 1) ≫ k (n + 1)) ∧
        (∀ n : ℤ, (openModuleStalkFunctor X V ⟨x, hxV⟩).map (k n) =
          (eV.app P).hom.f n ≫ (e.app P).inv.f n ≫
            (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
              (e.app Q).hom.f n ≫ (eV.app Q).inv.f n) := by sorry

end
end AlgebraicGeometry.Scheme
