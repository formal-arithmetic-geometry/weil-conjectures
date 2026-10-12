/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
/-! # RefineNonzeroGerm

Source: blueprint `lem-weil-pbc-lisse-generic-kernel`, first proof step.
(blueprint: lem-weil-pbc-refine-nonzero-germ) -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
/-- Refinement of a pointed nonzero germ over a locally constant set sheaf.
Source: blueprint `lem-weil-pbc-locally-constant-nonzero-germs`, proof steps 2--4.
A trivialising etale cover and filtered-colimit equality refine the section so
that its germ is nonzero at every geometric point of the refinement.
(blueprint: lem-weil-pbc-refine-nonzero-germ)

Proof:
1. Choose a member of the trivialising etale cover through the marked geometric
   point; surjectivity of the geometric fibre gives a lift to that member.
   Pull back U along this member and restrict a and the zero section.
2. The set-sheaf trivialisation identifies their distinct marked germs with two
   distinct elements m and z of its constant value. Constant-sheaf stalks are
   this value, since sheafification preserves stalks and the pointed
   neighbourhood category is nonempty and connected.
3. Filtered-colimit equality yields pointed refinements on which a is the
   constant section m and zero is the constant section z. Take a common
   refinement V of these two refinements, and let r be its composite to U.
4. The retained marked point proves V is nonempty. At each geometric lift to V,
   the constant-sheaf stalk formula identifies the two restricted germs with
   m and z. They are distinct, so the germ of the restriction of a is nonzero.
   Only a set-sheaf trivialisation is used; addition need not be preserved. -/
theorem refine_section_nonzero_germs (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F))
    (U : X.Etale) (a : F.obj.obj (op U))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (v : (pointSmallEtale t).fiber.obj U)
    (ha : (pointSmallEtale t).toPresheafFiber U v F.obj a ≠ 0) :
    ∃ (V : X.Etale) (r : V ⟶ U), Nonempty V.left ∧
      ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
        (t' : Spec (.of Ω') ⟶ X) (v' : (pointSmallEtale t').fiber.obj V),
        (pointSmallEtale t').toPresheafFiber V v' F.obj
          (F.obj.map r.op a) ≠ 0 := by sorry
end AlgebraicGeometry.Scheme
