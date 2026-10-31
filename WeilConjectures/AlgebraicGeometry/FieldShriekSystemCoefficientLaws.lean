/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModels

/-! # Coefficient-system composition and identity laws

The quotient maps induced by nested finite coefficient fields compose, and the
self-map is the identity.  This is the coefficient-level part of the whole
system cocycle.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2), lines 14--19.
(blueprint: lem-route-field-shriek-system-coefficient-laws)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

attribute [local implicit_reducible] spCoefficientCommRings

private theorem coefficientMap_app (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F : Index P) (h : E ≤ F) (T : Scheme.{u})
    (n : ℕ) (U : T.ProEtᵒᵖ) :
    (coefficientMap P (D.coefficients E F h) T).hom.app (Opposite.op (n, U.unop)) =
      (((D.coefficients E F h).tower T).app (Opposite.op n)).hom.app U := by
  exact (SemilinearSections.systemMap_existsUnique
    (Scheme.ProEt.topology T)
    (SpTowerShriek.B P.coefficients.l E.val T)
    (SpTowerShriek.tau P.coefficients.l E.val T)
    (SpTowerShriek.B P.coefficients.l F.val T)
    (SpTowerShriek.tau P.coefficients.l F.val T)
    (fun n ↦ ((D.coefficients E F h).tower T).app (Opposite.op n))
    (fun n ↦ (((D.coefficients E F h).tower T).naturality
      (homOfLE (Nat.le_succ n)).op).symm)).exists.choose_spec n U

private theorem quotient_comp (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F L : Index P) (h : E ≤ F) (k : F ≤ L) (n : ℕ) :
    (D.coefficients E L (h.trans k)).quotient n =
      ((D.coefficients F L k).quotient n).comp ((D.coefficients E F h).quotient n) := by
  apply RingHom.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x =>
    change (D.coefficients E L (h.trans k)).quotient n (Ideal.Quotient.mk _ x) =
      (D.coefficients F L k).quotient n
        ((D.coefficients E F h).quotient n (Ideal.Quotient.mk _ x))
    rw [(D.coefficients E L (h.trans k)).quotient_mk,
      (D.coefficients E F h).quotient_mk, (D.coefficients F L k).quotient_mk]
    congr 1

private theorem quotient_id (P : PurityFiniteSetting.{u}) (D : Models P)
    (E : Index P) (n : ℕ) :
    (D.coefficients E E le_rfl).quotient n = RingHom.id _ := by
  apply RingHom.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x =>
    change (D.coefficients E E le_rfl).quotient n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ x
    rw [(D.coefficients E E le_rfl).quotient_mk]
    rfl

private theorem tower_comp (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F L : Index P) (h : E ≤ F) (k : F ≤ L) (T : Scheme.{u}) (n : ℕ) :
    ((D.coefficients E L (h.trans k)).tower T).app (Opposite.op n) =
      ((D.coefficients E F h).tower T).app (Opposite.op n) ≫
        ((D.coefficients F L k).tower T).app (Opposite.op n) := by
  rw [(D.coefficients E L (h.trans k)).tower_app,
    (D.coefficients E F h).tower_app, (D.coefficients F L k).tower_app,
    ← CategoryTheory.Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact congrArg ULift.up (RingHom.congr_fun (quotient_comp P D E F L h k n) x.down)

private theorem tower_id (P : PurityFiniteSetting.{u}) (D : Models P)
    (E : Index P) (T : Scheme.{u}) (n : ℕ) :
    ((D.coefficients E E le_rfl).tower T).app (Opposite.op n) = 𝟙 _ := by
  rw [(D.coefficients E E le_rfl).tower_app, quotient_id]
  convert (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_id
    (CommRingCat.of (ULift.{u + 1, u} (SpTowerShriek.R P.coefficients.l E.val n))) using 1 <;> rfl

/-- Composition and identity for the actual whole-system coefficient maps.
Source: blueprint field-extension towers (2), lines 14--19
(blueprint: lem-route-field-shriek-system-coefficient-laws). -/
structure CoefficientLaws (P : PurityFiniteSetting.{u}) (D : Models P) : Prop where
  composition : ∀ (E F L : Index P) (h : E ≤ F) (k : F ≤ L) (T : Scheme.{u}),
    coefficientMap P (D.coefficients E L (h.trans k)) T =
      coefficientMap P (D.coefficients E F h) T ≫
        coefficientMap P (D.coefficients F L k) T
  identity : ∀ (E : Index P) (T : Scheme.{u}),
    coefficientMap P (D.coefficients E E le_rfl) T = 𝟙 _

/-- The quotient-map composition and identity laws for a `Models` datum.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2), lines 14--19.
Proof: evaluate the tower maps on each residue-class section.  The two
composites send a quotient class to the image under the composite intermediate
field inclusion, while the self-map sends it to the same class.  Quotient
induction and extensionality identify the induced ring-system maps, and the
universal property of `systemMap` identifies the resulting coefficient maps.
The proof is intentionally isolated because it is independent of compactification
and of derived comparison mates.
(blueprint: lem-route-field-shriek-system-coefficient-laws)
-/
theorem field_shriek_system_coefficient_laws
    (P : PurityFiniteSetting.{u}) (D : Models P) :
    Nonempty (CoefficientLaws P D) := by
  refine ⟨⟨?_, ?_⟩⟩
  · intro E F L h k T
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (coefficientMap P (D.coefficients E L (h.trans k)) T).hom.app U =
      (coefficientMap P (D.coefficients E F h) T).hom.app U ≫
        (coefficientMap P (D.coefficients F L k) T).hom.app U
    rw [coefficientMap_app P D E L (h.trans k) T U.unop.1 (Opposite.op U.unop.2),
      coefficientMap_app P D E F h T U.unop.1 (Opposite.op U.unop.2),
      coefficientMap_app P D F L k T U.unop.1 (Opposite.op U.unop.2)]
    exact congrArg (fun z ↦ z.hom.app (Opposite.op U.unop.2))
      (tower_comp P D E F L h k T U.unop.1)
  · intro E T
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rw [coefficientMap_app P D E E le_rfl T U.unop.1 (Opposite.op U.unop.2),
      tower_id]
    rfl

end AlgebraicGeometry.ProEtale.FieldShriekSystem
