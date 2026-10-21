/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf

/-! # Ring-valued presentations of internal abelian ring sheaves

Source: Stacks Project, Modules on Sites, Tag 00YV.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open CategoryTheory.InternalAbelianSheafModule
open scoped TensorProduct CategoryTheory.Obj

namespace CategoryTheory

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private noncomputable def recoveredMonIso (R : Mon Ab.{u}) :
    RingCat.toMonAb.obj (monToRing.obj R) ≅ R := by
  let h : @IsMonHom Ab.{u} _ _ _ _
      (RingCat.toMonAb.obj (monToRing.obj R)).mon R.mon (𝟙 R.X) := by
    constructor
    · ext n
      change (n.down : monToRing.obj R) = (η[R.X]).hom n
      rw [← zsmul_one]
      change n.down • (η[R.X]).hom (ULift.up 1) = (η[R.X]).hom n
      have hn : n = n.down • (ULift.up (1 : ℤ)) := by
        apply ULift.ext
        change n.down = n.down • (1 : ℤ)
        simp
      conv_rhs => rw [hn, map_zsmul]
    · apply AddCommGrpCat.hom_ext_toIntLinearMap
      apply TensorProduct.ext'
      intro a b
      rfl
  exact Mon.mkIso (M := RingCat.toMonAb.obj (monToRing.obj R)) (N := R)
    (Iso.refl R.X) h.one_hom h.mul_hom

private noncomputable def recoveredMonNatIso :
    monToRing.{u} ⋙ RingCat.toMonAb ≅ 𝟭 (Mon Ab.{u}) :=
  NatIso.ofComponents recoveredMonIso (fun f ↦ by ext; rfl)

/-- Every internal ring in abelian sheaves has a ring-valued sheaf presentation.
Source: Stacks Project, Modules on Sites, Tag 00YV
(blueprint: lem-zl-internal-ring-sheaf-presentation).

Proof: evaluate the internal presheaf ring at each object, using the tensor unit
for one and multiplication on pure tensors for multiplication. Restriction maps
are ring homomorphisms. Forgetting gives the original abelian sheaf, so the ring
presheaf is a sheaf. The reconstructed monoid is isomorphic to the original:
this is checked objectwise on the integer unit and pure tensors, then lifted
along the monoidal sheafification adjunction. No commutativity is required. -/
theorem internal_ring_sheaf_presentation
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, u}] [HasSheafify J Ab.{u}]
    [(J.W (A := Ab.{u})).IsMonoidal]
    (R : Mon (Sheaf J Ab.{u})) :
    ∃ A : Sheaf J RingCat.{u},
      Nonempty (Mon.mk ((sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj A) ≅ R) := by
  let P := presheafRings ((sheafToPresheaf J Ab.{u}).obj R.X)
  have hsheaf : Presheaf.IsSheaf J P := by
    let : CategoryTheory.Limits.PreservesLimitsOfSize.{w, max v w}
        (forget₂ RingCat.{u} Ab.{u}) :=
      CategoryTheory.Limits.preservesLimitsOfSize_of_univLE.{max v w, max v w} _
    apply (Presheaf.isSheaf_iff_isSheaf_comp J P (forget₂ RingCat.{u} Ab.{u})).2
    change Presheaf.IsSheaf J R.X.obj
    exact R.X.property
  let A : Sheaf J RingCat.{u} := ⟨P, hsheaf⟩
  let E := Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u}
  let M := (sheafToPresheaf J Ab.{u}).mapMon.obj R
  let k : (P.toMonAb) ≅ M :=
    E.inverse.mapIso (Functor.isoWhiskerLeft (E.functor.obj M) recoveredMonNatIso) ≪≫
      E.unitIso.symm.app M
  let z := (presheafToSheaf J Ab.{u}).mapMon.mapIso k
  let h : @IsMonHom (Sheaf J Ab.{u}) _ _ _ _
      ((presheafToSheaf J Ab.{u}).mapMon.obj M).mon R.mon
      ((sheafificationAdjunction J Ab.{u}).counit.app R.X) :=
    (sheafificationAdjunction J Ab.{u}).isMonHom_counitAlgHom R.X
  let a : (presheafToSheaf J Ab.{u}).mapMon.obj P.toMonAb ≅
      Mon.mk ((sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj A) :=
    Mon.mkIso (Sheaf.sheafifyRingPresheafIso J A)
      (Sheaf.isMonHom_sheafifyRingPresheafIso_hom J A).one_hom
      (Sheaf.isMonHom_sheafifyRingPresheafIso_hom J A).mul_hom
  let b : (presheafToSheaf J Ab.{u}).mapMon.obj M ≅ R :=
    Mon.mkIso (asIso ((sheafificationAdjunction J Ab.{u}).counit.app R.X))
      h.one_hom h.mul_hom
  exact ⟨A, ⟨a.symm ≪≫ z ≪≫ b⟩⟩

end CategoryTheory
