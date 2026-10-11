/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

/-!
# Finite acyclic resolutions and right derived functors

Source: Stacks Project, Derived Categories, Proposition 13.16.8 (Tag 05TA)
(blueprint: lem-pc-derived-acyclic-resolution).
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open CategoryTheory

/-- (blueprint: lem-pc-derived-acyclic-resolution) Let `F : C ⥤ D` be left exact and
additive between abelian categories with enough injectives. An augmented finite
resolution `0 → M → I⁰ → ⋯ → Iⁿ → 0` is represented by the quasi-isomorphism `ι`
from `M` concentrated in degree zero to `I`, with zero terms above `n`.
If its terms through degree `n` are `F`-acyclic, then the cohomology of `F(I)`
is isomorphic to `R^q F(M)` in every degree `q`.

For the proof, pad the finite complex with zero objects in higher degrees. These
are `F`-acyclic and the augmentation remains a quasi-isomorphism. Apply the
acyclic-resolution criterion `Functor.rightDerivedObjIsoOfResolution` to the
padded complex, and reverse its comparison isomorphism. The resulting cohomology
is that of the displayed finite complex (Stacks, Tag 05TA). -/
theorem nonempty_homology_iso_rightDerived_of_finite_acyclic_resolution
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    (M : C) (n : ℕ) (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj M ⟶ I) [QuasiIso ι]
    (hfinite : ∀ i : ℕ, n < i → Limits.IsZero (I.X i))
    (hacyclic : ∀ i : ℕ, i ≤ n → F.rightAcyclic (I.X i))
    (q : ℕ) :
    Nonempty (((F.mapHomologicalComplex _).obj I).homology q ≅
      (F.rightDerived q).obj M) := by
  sorry

end CategoryTheory.Functor
