/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

@[expose] public section
universe u
open CategoryTheory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- The three sectionwise formulas for the action and change-of-rings maps.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps-core)
-/
def ChangeOfRingsTensorActionFormulas (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right))
    (a d : tensorObj B.toModule (tensorObj C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P))
    (g : tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) ⟶
      (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
        (SheafOfModules.changeOfRings.{u, u, u} φ.right P)) : Prop :=
  (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
      (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
    a.app W (tmulSection (M := B.toModule) b
      (tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
      tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c (b • p)) ∧
  (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
      (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
    d.app W (tmulSection (M := B.toModule) b
      (tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
      tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)
        (φ.right.hom.app (op W) b * c) p) ∧
  (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
    g.app W (tmulSection (M := C.toModule)
      (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
        (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p))

/-- Existence of maps satisfying the three elementary section formulas.
Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps-core).

Proof: put P₀ = P restricted to O_Y and K = C.toModule.val tensor P₀.val.
On each open, give K the B-action on its second factor, b(c tensor p) =
c tensor bp, or the B-action on its first factor, b(c tensor p) =
φ(b)c tensor p. These actions descend through O_Y-balancing: the first
uses the scalar-tower identity on P, and the second uses
φ(B.hom(r)) = C.hom(r). They commute with restrictions by naturality
of the algebra maps and module restrictions, and restrict to the given
O_Y-action. This constructs two B-module presheaves with underlying
O_Y-module presheaf K. Sheafify each over B. Their underlying additive
sheaves are the associated additive sheaf of K, and their restricted
O_Y-actions agree with the action on the O_Y-sheafification of K:
both are the extensions of the same action on K. The sheafification
universal property therefore identifies each restriction with
S = C.toModule tensor P₀, preserving the sheafification unit.
Transport the two B-actions along these identifications. For either
action, the section maps (b,s) ↦ b • s are O_Y-bilinear and natural;
the presheaf tensor universal property and then sheafification give
O_Y-module morphisms B.toModule tensor S → S. The unit formula gives
the required formulas for a and d on b tensor (c tensor p).

For g, on each open send c tensor_O p to c tensor_B p and then apply
the B-to-C change-of-rings sheafification unit. This map is
O_Y-balanced since φ(B.hom(r)) = C.hom(r), is additive in both
variables, and commutes with restrictions by their pure-tensor
formulas and naturality of the unit. The tensor universal property
thus gives K → T.val. The O_Y-module sheafification adjunction
extends it uniquely to S → T, giving the required formula for g.
Only the construction and formulas are asserted here; equality of
a followed by g and d followed by g is proved separately. Empty
opens and zero modules cause no exception, since all maps above
are defined by universal properties valid also for zero objects.
-/
theorem exists_changeOfRings_tensor_action_maps_core (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    ∃ (a d : tensorObj B.toModule (tensorObj C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P))
      (g : tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) ⟶
      (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
        (SheafOfModules.changeOfRings.{u, u, u} φ.right P)),
      ChangeOfRingsTensorActionFormulas Y B C φ P a d g := by sorry

end AlgebraicGeometry.Scheme.Modules
