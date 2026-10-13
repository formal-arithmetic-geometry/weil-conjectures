/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # One finite-free open-site stalk map lifts on one neighbourhood

Source: Stacks Project, Modules Tag 01CP, and Sheaves Tag 00A0 (3).
(blueprint: lem-sc-open-stalk-free-map-one-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A single finite-free stalk map lifts on one smaller open. The comparison may
be chosen with this lift; no comparison family or further-restriction assertion is made.

Source: Stacks Project, Modules Tag 01CP (`lemma-stalk-internal-hom`), the
finite-generator part of the finite-presentation proof; Sheaves Tag 00A0 (3).
(blueprint: lem-sc-open-stalk-free-map-one-lift).

Proof: Use the slice/open-subspace equivalence to regard the source and target
as module sheaves on U.toScheme. This equivalence carries the rank-m free sheaf
to the rank-m free structure module, since its sectionwise restriction preserves
the unit sheaf and finite coproducts. The open-immersion stalk-ring map is an
isomorphism, so transport t from the ambient stalk ring to the stalk ring on U.
Apply t to the m standard basis germs and choose section representatives of their
images in N. Intersect their finitely many neighbourhoods in U to obtain V.
Restrict the representatives to V and extend the assignment of basis sections
by the free sheaf universal property, obtaining k. This is also the identity-source
case of finite-free local stalk-map lifting on the ringed space U.toScheme.
The stalk of k agrees with t on each basis germ, hence on every vector by linearity.
Transport k back through the slice equivalence. Take a to be the canonical
restriction-stalk comparison, whose germ formula identifies a restricted germ
with the original germ. The equality just proved is S(k) followed by a_N equals
 a_F followed by t; composing with a_N inverse gives the displayed formula.
For m=0 take V=U and the unique zero-source map; no representatives are needed.
No finiteness or quasicoherence of N is used. -/
theorem exists_open_stalk_free_map_one_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (m : ℕ) (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (t : (openModuleStalkFunctor X U ⟨x, hxU⟩).obj
      (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
      (openModuleStalkFunctor X U ⟨x, hxU⟩).obj N) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U),
      let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU)
      let S := openModuleStalkFunctor X V ⟨x, hxV⟩
      let F := SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))
      ∃ (a : R ⋙ S ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
        (k : R.obj F ⟶ R.obj N),
        S.map k = a.hom.app F ≫ t ≫ a.inv.app N := by sorry

end
end AlgebraicGeometry.Scheme
