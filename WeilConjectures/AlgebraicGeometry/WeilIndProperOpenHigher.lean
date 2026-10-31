/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
import WeilConjectures.AlgebraicGeometry.WeilIndProperOpenHigherComparison
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Proper/open interchange for higher ind-images

Source: SGA 4, XVII, §5; Bhatt--Scholze, §6.7--6.8.
(blueprint: lem-zl-ind-proper-open-higher).
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

/-- A proper map which identifies the two distinguished open copies of X gives the
same higher proper image after extension by zero. No compactification is selected.
Source: SGA 4, XVII, 5.1.5--5.1.6, followed by proper-image transitivity 5.1.4
(blueprint: lem-zl-ind-proper-open-higher).

Proof: proper/open interchange for the square with top map id_X and vertical proper
map r identifies Rr_* j₁! with j₂!. On the open X, proper base change identifies this
map with the identity: the copy of X in r⁻¹(X) is both open and proper, hence closed,
and extension by zero is zero on its complement. On the closed complement of X in Z₂,
proper base change identifies the restriction of Rr_* j₁! with the direct image of
zero, hence zero. The two restrictions jointly detect isomorphisms. Thus j₁!F is
r_*-acyclic and its ordinary r-image is j₂!F. All maps are the adjunction mates of the
prescribed inverse-image squares, so the comparison commutes with Frobenius.
Exact inverse image makes proper ordinary image preserve injectives. Applying the
composite derived-image comparison, or its Grothendieck spectral sequence with the
r-acyclic input j₁!F, identifies Rⁿp₂_* j₂!F with Rⁿ(p₂ r)_* j₁!F.
Use r p₂ = p₁ to obtain the displayed result. Finite coefficient extension preserves
the proper/open comparisons, and the Yoneda Kan normalization transports them to the
ambient equivariant ind-categories. The empty open and identity r are included. -/
theorem zlIndWeilProperOpenHigher
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
    (n : ℕ) (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    Nonempty
      (((zlIndWeilPush D l hl Ω p₁).rightDerived n).obj
          ((zlIndWeilOpenShriek D l hl Ω j₁).obj
            ((zlWeilIndEmbedding D l hl Ω X₀).obj F)) ≅
        ((zlIndWeilPush D l hl Ω p₂).rightDerived n).obj
          ((zlIndWeilOpenShriek D l hl Ω j₂).obj
            ((zlWeilIndEmbedding D l hl Ω X₀).obj F))) := by
  obtain ⟨e, he⟩ := zlIndWeilProperOpenHigher_comparison D l hl Ω j₁ j₂ p₁ p₂ r _hi _hp n
    ((zlWeilIndEmbedding D l hl Ω X₀).obj F)
  let _ : IsIso e := he
  exact ⟨asIso e⟩

end WeilConjectures
