/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Canonical proper/open comparison for higher ind-images

Source: SGA 4, exposé XVII, 5.1.5--5.1.6; Bhatt--Scholze 6.7--6.8.
(blueprint: lem-zl-ind-proper-open-higher-comparison-q7).
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

/-- The canonical proper/open exchange comparison is invertible on every higher
right-derived image.  This is the mate comparison before it is packaged as a
`Nonempty` isomorphism in `zlIndWeilProperOpenHigher`.

Source: SGA 4, exposé XVII, 5.1.5--5.1.6; Bhatt--Scholze 6.7--6.8.
Proof: construct the proper/open exchange on the common-stage heart, transport it
through the normalized Yoneda ind-extension, and apply the Grothendieck
right-derived comparison to the resulting acyclic open extension.  Proper base
change identifies the restriction over the open with the identity and the
restriction to its closed complement with zero; the open and closed restrictions
detect isomorphisms.  The mate is Frobenius-equivariant by the normalization of
the pullback squares, and finite coefficient extension preserves it.
(blueprint: lem-zl-ind-proper-open-higher-comparison-q7). -/
theorem zlIndWeilProperOpenHigher_comparison
    {X₀ Z₁ Z₂ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
    [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₁ : X₀ ⟶ Z₁) (j₂ : X₀ ⟶ Z₂)
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (p₁ : Z₁ ⟶ Y₀) (p₂ : Z₂ ⟶ Y₀)
    [IsProper p₁.left] [IsProper p₂.left]
    (r : Z₁ ⟶ Z₂) [IsProper r.left]
    (_hi : j₁ ≫ r = j₂) (_hp : r ≫ p₂ = p₁)
    (n : ℕ) (K : zlIndWeilHeart D l hl Ω X₀) :
    ∃ e :
      ((zlIndWeilPush D l hl Ω p₁).rightDerived n).obj
          ((zlIndWeilOpenShriek D l hl Ω j₁).obj K) ⟶
        ((zlIndWeilPush D l hl Ω p₂).rightDerived n).obj
          ((zlIndWeilOpenShriek D l hl Ω j₂).obj K),
      IsIso e := by
  sorry

end WeilConjectures
