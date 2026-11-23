/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions

/-!
# Compatible injective resolutions of a short exact sequence

## References

* [Stacks Project, Tag 013T](https://stacks.math.columbia.edu/tag/013T)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

/-- A short exact sequence in an abelian category with enough injectives admits three
compatible injective resolutions with short exact rows in every nonnegative degree.
The middle terms can be identified with biproducts so that the row maps are the first
inclusion and second projection. Natural-number indexing represents extension by zero
in every negative degree. The augmentation equalities are equalities of complex maps;
their only nonzero source component is in degree zero.

Source: Stacks Project, Derived Categories, Lemma 13.18.9 (Tag 013T), parts (2)-(3). -/
theorem exists_horseshoe_resolutions
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∃ (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
      (IC : InjectiveResolution S.X₃)
      (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex),
      IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι ∧
      IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι ∧
      ∃ (hαβ : α ≫ β = 0), ∀ n : ℕ,
        ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact ∧
        ∃ e : IB.cocomplex.X n ≅ IA.cocomplex.X n ⊞ IC.cocomplex.X n,
        α.f n ≫ e.hom = biprod.inl ∧ β.f n = e.hom ≫ biprod.snd := by
  let IA : InjectiveResolution S.X₁ := InjectiveResolution.of S.X₁
  let IC : InjectiveResolution S.X₃ := InjectiveResolution.of S.X₃
  obtain ⟨IB, α, β, hα, hβ, hrows⟩ :=
    InjectiveResolution.exists_horseshoe_prescribed_resolutions S hS IA IC
  exact ⟨IA, IB, IC, α, β, hα, hβ, hrows⟩

end CategoryTheory.InjectiveResolution
