/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Sheaf.Paper.WeilIndSheafCategory

/-! # Heart model for represented open extension

Source: SGA 4, XVII, §5.1; Bhatt--Scholze, §6.7--6.8.
(blueprint: lem-zl-ind-open-heart-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

Source: SGA 4, XVII, 5.1; Bhatt--Scholze, 6.7.6--6.8.11.
(blueprint: lem-zl-ind-open-heart-model).

Proof: extension by zero on the constructible geometric heart is exact and left
adjoint to inverse image.  Transport it to the small common-stage category,
extend it along the Yoneda Kan extension, and equip it with the normalized
Frobenius mate.  The Kan unit is invertible on representables, so the resulting
functor sends each represented Weil sheaf to another represented Weil sheaf.
The mate equations give the fixed-pair adjunction with `zlIndWeilPull`.  Empty
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
  sorry

end WeilConjectures
