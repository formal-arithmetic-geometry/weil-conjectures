/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Conservative families of points

Source: Stacks Project, Sites, Tags 00YK and 00YM, using Tags 00Y6 and 00Y8
(blueprint: lem-trf-point-family-conservative).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

namespace CategoryTheory

open Limits Opposite

/-- The sheaf morphism represented by a section of a sheaf on an object.
Source: Stacks, Tags 00Y6 and 00Y8 (blueprint: lem-trf-point-family-conservative). -/
noncomputable def sectionMorphism {C : Type u} [Category.{v} C] (J : Precoverage C)
    (F : Sheaf J.toGrothendieck (Type (max u v w))) (U : C) (t : F.obj.obj (op U)) :
    (presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
      (uliftYoneda.{max u v w, v}.obj U) ⟶ F :=
  ⟨sheafifyLift J.toGrothendieck (uliftYonedaEquiv.symm t) F.property⟩

/-- The image in a point fibre of a section class `[U,x,t]`.
Source: Stacks, Tags 00Y6 and 00Y8 (blueprint: lem-trf-point-family-conservative). -/
noncomputable def pointSectionImage {C : Type u} [Category.{v} C] (J : Precoverage C)
    (p : GeometricMorphism (Type (max u v w))
      (Sheaf J.toGrothendieck (Type (max u v w))))
    (F : Sheaf J.toGrothendieck (Type (max u v w))) (U : C)
    (x : p.inverse.obj ((presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
      (uliftYoneda.{max u v w, v}.obj U)))
    (t : F.obj.obj (op U)) : p.inverse.obj F :=
  (p.inverse.map (sectionMorphism J F U t)) x

/-- Section separation by a family of geometric-morphism points implies joint reflection of
isomorphisms. Source: Stacks, Tags 00YK and 00YM, with stalk identifications from Tags 00Y6
and 00Y8 (blueprint: lem-trf-point-family-conservative).

Proof: for a morphism whose inverse images are bijections, section separation gives injectivity
on every object. Form the pushout of the morphism with itself; inverse images preserve it because
they are left adjoints, and the same separation argument makes its coprojections equal. The
cokernel-pair criterion gives epimorphy, and the balanced mono-plus-epi property of sheaves of
sets gives an isomorphism. -/
lemma point_family_conservative
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (I : Type w')
    (p : I → GeometricMorphism (Type (max u v w))
      (Sheaf J.toGrothendieck (Type (max u v w))))
    (hsep : ∀ (F : Sheaf J.toGrothendieck (Type (max u v w)))
      (U : C) (s s' : F.obj.obj (op U)), s ≠ s' →
      ∃ (i : I) (x : (p i).inverse.obj
        ((presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
          (uliftYoneda.{max u v w, v}.obj U))),
        pointSectionImage J (p i) F U x s ≠ pointSectionImage J (p i) F U x s') :
    JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse) := by
  sorry

end CategoryTheory
