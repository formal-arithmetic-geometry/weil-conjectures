/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Vanishing of Hom in a transfinite union of subcomplexes

Source: Stacks Project, `injectives.tex`, Lemma `lemma-characterize-K-injective`, limit step
(Homology Lemma `lemma-ML-over-ordinals`, Tag 0AAT)
(blueprint: lem-pur-kinjective-homotopy-limit-vanishing).
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, `injectives.tex`, Lemma `lemma-characterize-K-injective`,
proof at the limit step (blueprint: lem-pur-kinjective-homotopy-limit-vanishing).
Let `λ` be a limit ordinal and `K` a well-order-continuous system of complexes indexed by
`β < λ` with monomorphic transition maps and colimit cocone `c` (so `c.pt` is `K_λ`). If `I`
is termwise injective and every map from a shift `K_β⟦n⟧` to `I` is null-homotopic
(`Hom_{K(A)}(K_β[n], I) = 0`), then every map `c.pt⟦n⟧ ⟶ I` is null-homotopic.

Proof: (1) Let `Hom^•(K, I)` be the Hom complex, `Hom^n = ∏_j Hom(K^j, I^{j+n})`. Its
degree-`n` cohomology is `Hom_{K(A)}(K[-n], I)`, so the hypothesis says each
`Hom^•(K_β, I)` is acyclic. Colimits of complexes are termwise, so
`Hom^•(K_λ, I) = lim_{β<λ} Hom^•(K_β, I)`. For `β < λ` the map
`colim_{γ<β} K_γ ⟶ K_β` is a monomorphism (zero at `β = 0`, a transition map at a
successor, an isomorphism by continuity at a limit); by injectivity of each `I^{j+n}`,
`Hom^n(K_β, I) ⟶ lim_{γ<β} Hom^n(K_γ, I)` is surjective.
(2) Apply `lem-pur-kinjective-ML-ordinals` with `α = λ` to this inverse system: the limit
`Hom^•(K_λ, I)` is acyclic, i.e. `Hom_{K(A)}(K_λ[-n], I) = 0` for every `n`. -/
theorem homotopyLimitVanishing
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    (lam : Ordinal.{w}) (h_limit : Order.IsSuccLimit lam)
    (K : lam.ToType ⥤ CochainComplex A ℤ) [K.IsWellOrderContinuous]
    (h_mono : ∀ ⦃β γ : lam.ToType⦄ (h : β ≤ γ), Mono (K.map (homOfLE h)))
    (c : Cocone K) (hc : IsColimit c)
    (I : CochainComplex A ℤ) (hinj : ∀ n : ℤ, Injective (I.X n))
    (hvanish : ∀ (β : lam.ToType) (n : ℤ) (f : (K.obj β)⟦n⟧ ⟶ I), Nonempty (Homotopy f 0)) :
    ∀ (n : ℤ) (f : c.pt⟦n⟧ ⟶ I), Nonempty (Homotopy f 0) := by
  sorry

end CategoryTheory
