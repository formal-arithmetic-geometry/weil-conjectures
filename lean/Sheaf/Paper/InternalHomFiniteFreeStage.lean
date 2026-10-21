/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData

/-! # Finite-free calculation for the strict internal-Hom roof -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SfbHomFilteredColimit
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]

/-- A finite-free coefficient module gives quasi-isomorphisms in the strict Hom roof.
Source: Bhatt--Scholze, Remark 6.8.15, finite-free case of the conditional ring-sheaf
argument; Stacks Project, Tags 08J9 and 079P.
(blueprint: lem-sfb-internal-hom-finite-free-stage).

Proof: choose the given isomorphism with a finite power of the unit. Tensoring by this
module is naturally a finite direct sum of the identity, and therefore exact. Its tensor
with the augmentation of L is a quasi-isomorphism, which the functorial derived Hom
representative preserves. This proves the denominator assertion. Finite direct sums of
the chosen K-injective replacement of L are K-injective, and internal Hom commutes with
these finite sums. Under these identifications the normalized comparison is the finite
sum of the identity followed by the target augmentation. Applying Hom to the resulting
quasi-isomorphism between K-injectives gives a quasi-isomorphism. The evaluation formula
fixes this identification independently of the chosen basis. For rank zero all complexes
and maps are zero, and both assertions still hold. No boundedness is required. -/
theorem internalHom_finiteFree_stage (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R)
    (hfree : ∃ d : ℕ, Nonempty
      (T ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    QuasiIso ((comparison.{u, v, r} J R P L).app T) ∧
      QuasiIso (roofDenominator.{u, v, r} J R P L T) := by
  sorry

end WeilConjectures.SfbHomFilteredColimit
