/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.CategoryTheory.Sites.RingedSitePoint
public import Sheaf.Paper.RingedTopoiTensorSections

/-! # Extension of scalars at a topos point

Source: Stacks Project, Modules on Sites, Tags 05V5 and 03EL.
(blueprint: lem-sfb-point-scalar-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open SheafOfModules SheafOfModules.RingedTensor
open scoped TensorProduct ChangeOfRings

namespace CategoryTheory

/-- Taking a stalk commutes with extension of scalars, with its universal pairing.

Source: Stacks Project, Modules on Sites, Tag 05V5, lemma-pullback-stalk, proof;
Tag 03EL, lemma-tensor-product-pullback, proof.
(blueprint: lem-sfb-point-scalar-extension).

Proof: Transport the coefficient map c by p.inverse. The operation graph equations
of a and s show that its underlying map preserves addition, multiplication, zero
and one, hence give the ring homomorphism b with the displayed normalization.
Present Set as sheaves on the one-object site with its trivial topology. The
finite-product transport defining a is an algebraic inverse-image presentation
on this site. Compose p.inverse with the sheaf equivalence and transport its
adjunction and finite-limit preservation through that equivalence. Forgetting
from R-modules to A-modules identifies changeOfRings c N with the sheaf tensor
of restricted R and N: the sectionwise tensors followed by sheafification
represent the same sheaf bilinear maps. The graph equations identify the
A-module stalk of that forgotten object with s.modules(changeOfRings c N)
restricted along b, under their specified underlying-set isomorphisms.
Apply the inverse-image tensor comparison to the A-modules R
(restricted along c) and N. Its generalized-section formula identifies the
image of every pure pairing with the pairing of the image germs. The stalk of
the restricted module R is s.ring restricted along b: this follows by applying
the scalar graph equations to c and using the normalization of b. The tensor
comparison therefore gives s.ring tensor over a.ring with a.modules(N).
Compose with tensor symmetry to put s.ring last. The symmetry intertwines the
action on the first factor with the displayed action on the last factor.
Linearity follows from transporting the multiplication action of R on the
first factor; the two maps agree on the universal pure pairing, hence on the
tensor by its universal property. Naturality follows from the simultaneous
naturality of the tensor comparison and symmetry. Applying its generalized
section formula before symmetry gives exactly the final displayed equation.
The zero ring, zero module and empty site cause no exception: all operations
and comparisons use finite products and tensor universal properties only. -/
theorem RingedSitePoint.scalarExtension
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A R : Sheaf J CommRingCat.{u}) (c : A ⟶ R)
    (p : GeometricMorphism (Type u) (Sheaf J (Type u)))
    (a : RingedSitePoint A p) (s : RingedSitePoint R p) :
    ∃ b : a.ring →+* s.ring,
      (∀ x : p.inverse.obj ((sheafCompose J (forget CommRingCat.{u})).obj A),
        b (a.ringUnderlying.hom x) = s.ringUnderlying.hom
          (p.inverse.map ((sheafCompose J (forget CommRingCat.{u})).map c) x)) ∧
      letI : Algebra a.ring s.ring := b.toAlgebra
      ∃ e : ∀ N : ringedSiteModules.{u} (ringSheaf A),
        s.modules.obj (changeOfRings.{u, u, u} c N) ≃+
          TensorProduct a.ring (a.modules.obj N) s.ring,
        (∀ (N : ringedSiteModules.{u} (ringSheaf A)) (r : s.ring)
          (x : s.modules.obj (changeOfRings.{u, u, u} c N)),
          e N (r • x) = TensorProduct.comm a.ring s.ring (a.modules.obj N)
            (r • TensorProduct.comm a.ring (a.modules.obj N) s.ring (e N x))) ∧
        (∀ (N N' : ringedSiteModules.{u} (ringSheaf A)) (h : N ⟶ N')
          (x : s.modules.obj (changeOfRings.{u, u, u} c N)),
          e N' (s.modules.map (changeOfRingsHom.{u, u, u} c N h) x) =
            TensorProduct.map (a.modules.map h).hom (LinearMap.id : s.ring →ₗ[a.ring] s.ring)
              (e N x)) ∧
        ∀ (N : ringedSiteModules.{u} (ringSheaf A)) (T : Sheaf J (Type u))
          (r : T ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R)
          (m : T ⟶ (SheafOfModules.RingedTensor.underlying A).obj N)
          (z : T ⟶ (SheafOfModules.RingedTensor.underlying R).obj
            (changeOfRings.{u, u, u} c N)),
          (∀ (W : Cᵒᵖ) (x : T.obj.obj W),
            z.hom.app W x = ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
              (𝟙 (ringSheaf R).obj)).unit.app
                (changeOfRingsPresheaf.{u, u, u} c N)).app W
                  ((@id (R.obj.obj W) (r.hom.app W x))
                    ⊗ₜ[A.obj.obj W, (c.hom.app W).hom]
                      (@id (N.val.obj W) (m.hom.app W x)))) →
          ∀ x : p.inverse.obj T,
            e N ((s.moduleUnderlying.inv.app (changeOfRings.{u, u, u} c N))
              (p.inverse.map z x)) =
              ((a.moduleUnderlying.inv.app N) (p.inverse.map m x)) ⊗ₜ[a.ring]
                (s.ringUnderlying.hom (p.inverse.map r x)) := by sorry

end CategoryTheory
