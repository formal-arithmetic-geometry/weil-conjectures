/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An exhaustive filtration by subcomplexes gives the mapping telescope triangle.
Source: Stacks Project, More on Algebra, Remark 15.60.11 (Tag 09PB), displayed triangle.
(blueprint: lem-pc-derived-module-filtration-telescope).

Proof: form the termwise direct sum `S₀` of the `F n`. Let `s` send summand `n` to
summand `n+1` via `step n`, and let `p : S₀ ⟶ L` be induced by the compatible `ι n`.
In each degree the sequence `0 → S₀ → S₀ → L → 0`, with maps `1-s` and `p`, is exact.
Injectivity of `1-s` follows by inspecting components successively starting at zero.
Surjectivity of `p` is exhaustiveness. If a finitely supported tuple is in its kernel,
choose a filtration stage beyond its support. Moving each component to that stage
changes the tuple by an element of the image of `1-s`; the resulting component is zero
because the inclusion of that stage into `L` is injective. Thus `ker p = im (1-s)`.
Apply `DerivedCategory.triangleOfSES_distinguished` to this short exact sequence.
Use `derivedModuleDirectSums` to make `Q(S₀)` a coproduct of the `Q(F n)`.
Reindex this coproduct along the equivalence `ULift ℕ ≃ ℕ` to place its index in the
module universe. This supplies `S`, `j`, and the distinguished triangle in the conclusion.
This construction uses neither free modules nor a property of derived objects. -/
theorem derivedModuleFiltrationTelescope (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} R) ℤ)
    (ι : ∀ n, F n ⟶ L) (step : ∀ n, F n ⟶ F (n + 1))
    (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : L.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x) :
    ∃ (S : DerivedCategory (ModuleCat.{max u v} R))
      (j : ∀ n : ULift.{max u v} ℕ, DerivedCategory.Q.obj (F n.down) ⟶ S),
      Nonempty (IsColimit (Cofan.mk S j)) ∧
      ∃ (a : S ⟶ S) (b : S ⟶ DerivedCategory.Q.obj L)
        (c : DerivedCategory.Q.obj L ⟶ S⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk a b c ∈ Pretriangulated.distinguishedTriangles := by
  sorry

end CategoryTheory
