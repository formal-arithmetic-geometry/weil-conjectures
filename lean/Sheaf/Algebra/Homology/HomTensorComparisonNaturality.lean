/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.KFlat

/-!
# Naturality of the sheaf tensor comparison

Source: Stacks Project, Modules on Sites, Section 03EK.
(blueprint: lem-sc-hom-tensor-comparison-natural)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option maxHeartbeats 400000 in
-- Matching the identity scalar restriction in counit naturality needs extra reduction.
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the tensor comparison isomorphism.
Source: Stacks Project, Section 03EK and Lemma 03CY.
(blueprint: lem-sc-hom-tensor-comparison-natural)

Proof: Let S be module sheafification and epsilon its invertible counit.
The comparison is the tensor of the inverse counit components followed by
S's tensorator. Naturality of the inverse counit gives
f;epsilon(A) inverse = epsilon(A') inverse;S(f.val), and likewise for g.
The tensor interchange law combines these two identities. Tensorator
naturality then identifies the resulting composite with the comparison
at A',B' followed by S(f.val tensor g.val). Associativity gives the result.
No invertibility of f or g is used; identity and zero maps and zero objects
are included. This is the first step of the section-map naturality proof,
before forgetting and composing with the sheafification unit. -/
theorem homTensorComparison_natural {A A' B B' : Mod}
    (f : A' ⟶ A) (g : B' ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification A B).hom =
      (SheafOfModules.tensorObjIsoSheafification A' B').hom ≫
        (PresheafOfModules.sheafification
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
          (f.val ⊗ₘ g.val) := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have hf := (asIso adj.counit).inv.naturality f
  have hg := (asIso adj.counit).inv.naturality g
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    tensorIso_inv, Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural]
  simp only [← Category.assoc]
  congr 1
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1

end CategoryTheory
