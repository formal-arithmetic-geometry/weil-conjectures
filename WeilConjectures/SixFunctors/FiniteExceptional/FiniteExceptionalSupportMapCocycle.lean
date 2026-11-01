/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData

/-! Finite exceptional compact-support comparison cocycle.

Source: the successive finite-reduction comparison square in
`lem-sf-finite-exceptional-quotient-coherence`.
(blueprint: lem-sf-finite-exceptional-quotient-coherence)

Proof: expand each q as the compact-support comparison conjugated by the chosen
finite-image isomorphism. Apply `PurCompactSupport.comparison_composition` to the
successive coefficient changes A_m → A_n → A_t, whose coefficient ring maps
compose by definition. Rewrite its tensor-composition component by the canonical
balanced scalar associator. Naturality of the finite-image isomorphisms moves the
three conjugating maps to the endpoints; the two intermediate inverse pairs
cancel. Apply the full-subcategory inclusion to this equality and use functoriality
of `Q`, `F`, and the associator. The resulting component equality is exactly the
displayed q cocycle. The finite-image transport and its naturality squares are the
substantial categorical calculation represented by this split theorem.
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

/-- The compact-support comparison maps satisfy the quotient cocycle on finite-Tor.
Source: blueprint lem-sf-finite-exceptional-quotient-coherence, proof paragraph 2.
-/
theorem support_map_cocycle :
    ∀ {m n t : ℕ} (h : n ≤ m) (k : t ≤ n)
      (K : (domain l E X m).FullSubcategory),
      (Q l E Y k).map ((q l E D hl f c h).hom.app K) ≫
          (q l E D hl f c k).hom.app ((Q l E X h).obj K) ≫
          (F l E D hl f c t).map ((reassoc l E X h k).hom.app K) =
        (reassoc l E Y h k).hom.app ((F l E D hl f c m).obj K) ≫
          (q l E D hl f c (k.trans h)).hom.app K := by
  sorry

end WeilConjectures.FiniteExceptional
