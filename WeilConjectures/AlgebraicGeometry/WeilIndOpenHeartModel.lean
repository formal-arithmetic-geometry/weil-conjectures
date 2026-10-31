/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
import all WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
import all WeilConjectures.AlgebraicGeometry.WeilIndProperHigherRepresentability

/-! # Heart model for represented open extension

Source: Bhatt--Scholze, §6.7--6.8.
(blueprint: lem-zl-ind-open-heart-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Endofunctor
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/--
The geometric open-extension construction has a represented heart model before it
is identified with the selected ambient left adjoint.  The functor `J` is the
common-stage open extension transported through the normalized ind construction;
its adjunction is with the canonical inverse image, and every represented input
has a represented output.  This is the heart-level content of exact extension by
zero.  The remaining comparison with the chosen left adjoint is formal uniqueness
of left adjoints and is proved in the consuming module.

Source: Bhatt--Scholze, 6.7.6--6.8.11.
(blueprint: lem-zl-ind-open-heart-model).

Proof: extension by zero on the constructible geometric heart is exact and left
adjoint to inverse image.  Transport it to the small common-stage category,
extend it along the Yoneda Kan extension, and equip it with the normalized
Frobenius mate.  The Kan unit is invertible on representables, so the resulting
functor sends each represented Weil sheaf to another represented Weil sheaf.
The mate equations give the fixed-pair adjunction with `zlIndWeilPull`.
For a represented input with small carrier A, the inverse Kan unit identifies the
output carrier with Yoneda of L(A). Full faithfulness of Yoneda lifts the output
Frobenius structure to L(A); the small-pair presentation then recovers a common-stage
Weil sheaf. This is the proved `represented_carrier_lifts` helper from the higher
proper-image module; no proper-image theorem is used here. Empty
opens, the identity open, and the zero object are included by the same formulas.
-/
theorem zlIndWeilOpenShriek_heart_model {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :
    ∃ J : zlIndWeilHeart D l hl Ω X₀ ⥤ zlIndWeilHeart D l hl Ω Y₀,
      Nonempty (J ⊣ zlIndWeilPull D l hl Ω j₀) ∧
        ∀ F : sfCommonStageWeilSheaf D l hl X₀ Ω,
          ∃ G : sfCommonStageWeilSheaf D l hl Y₀ Ω,
            Nonempty ((zlWeilIndEmbedding D l hl Ω Y₀).obj G ≅
              J.obj ((zlWeilIndEmbedding D l hl Ω X₀).obj F)) := by
  -- Retain the underlying heart functor to compute its ind-extension on Yoneda.
  obtain ⟨H, _, _, ⟨aH⟩⟩ := zlHeartPull_openAdjunction D l hl Ω j₀
  let eX : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ≌
      zlSmallHeart D l Ω hl X₀ := AsSmall.equiv
  let eY : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω ≌
      zlSmallHeart D l Ω hl Y₀ := AsSmall.equiv
  let L := eX.inverse ⋙ H ⋙ eY.functor
  let aL : L ⊣ zlSmallPull D l hl Ω j₀ :=
    eX.symm.toAdjunction.comp (aH.comp eY.toAdjunction)
  let aI := zlIndMap_adjunction aL
  let := (zlIndFrobenius_exact D l hl Ω X₀).2.2.2
  let := (zlIndFrobenius_exact D l hl Ω Y₀).2.2.2
  let eR := zlIndSquare (zlSmallPull D l hl Ω j₀)
    (zlSmallFrobenius D l hl Ω Y₀) (zlSmallFrobenius D l hl Ω X₀)
    (zlSmallSquare D l hl Ω j₀)
  let m := ((mateEquiv aI aI).symm (TwoSquare.mk _ _ _ _ eR.hom)).natTrans
  let : IsIso m := isIso_inverseMate_of_equivalences aI aI eR
  let eL := (asIso m).symm
  have hm : (mateEquiv aI aI (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom :=
    congrArg TwoSquare.natTrans ((mateEquiv aI aI).apply_symm_apply
      (TwoSquare.mk _ _ _ _ eR.hom))
  refine ⟨IsoAlgebra.mapOfNatIso eL,
    ⟨IsoAlgebra.mapOfNatIsoAdjunction aI eL eR hm⟩, ?_⟩
  -- Only the carrier comparison is needed: full faithfulness recovers the Weil action.
  intro F
  let A := ((zlWeilSmallPairs D l hl Ω X₀).obj F).carrier
  exact represented_carrier_lifts D l hl Ω Y₀ _ (L.obj A)
    ((zlIndMapIso L).app A).symm

end WeilConjectures
