/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData

/-! Identity normalization of finite exceptional compact-support comparisons.

Source: the equal-index specialization of the quotient cocycle in
`lem-sf-finite-exceptional-quotient-coherence`.
(blueprint: lem-sf-finite-exceptional-quotient-coherence)

Proof: specialize the quotient cocycle at m = n = t and identify every scalar
associator with the tensor identity unitor. Conjugate the resulting component of
q by the source and target `selfReduction` unitors. The conjugated endomorphism is
idempotent, while q is an isomorphism by the compact-support comparison
construction; composing the idempotence equation with its inverse gives that the
endomorphism is the identity. Undo the conjugation, rewrite the inverse unitor as
the chosen `selfReduction.inv`, and obtain the displayed component formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

/-- The equal-level compact-support comparison is normalized by the tensor unit.
Source: blueprint lem-sf-finite-exceptional-quotient-coherence, proof paragraph 2.
-/
theorem support_map_identity (n : ℕ) :
    ∀ (L : (domain l E Y n).FullSubcategory),
      (q l E D hl f c (le_refl n)).hom.app ((G l E D hl f c n).obj L) =
        (selfReduction l E Y n).hom.app
          ((F l E D hl f c n).obj ((G l E D hl f c n).obj L)) ≫
          (F l E D hl f c n).map
            ((selfReduction l E X n).inv.app ((G l E D hl f c n).obj L)) := by
  sorry

end WeilConjectures.FiniteExceptional
