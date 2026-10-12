/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import Sheaf.CategoryTheory.QuotientJShriek

/-!
# Compatible flat replacements of good truncations

Source: Stacks Project, Cohomology on Sites, Lemma 077J
(`sites-cohomology-lemma-resolution-by-direct-sums-extensions-by-zero`), using
Derived Categories, `lemma-special-direct-system`
(blueprint: lem-pc-flat-truncation-tower).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Good truncations admit a strictly compatible tower of bounded-above flat replacements.
Source: Stacks Project, Lemma 077J and Derived Categories, `lemma-special-direct-system`
(blueprint: lem-pc-flat-truncation-tower).

Proof: Use flat module sheaves as the resolving class. Zero and finite sums are flat.
Every module has a flat epimorphic cover: use the canonical section-indexed sum of
extension-by-zero modules `j_{U!} O_U` from Modules on Sites, Lemma 03EW, whose
summands are flat by extension-by-zero flatness and whose sum is flat by coproduct
flatness. The bounded-above flat replacement theorem resolves any bounded-above
complex in this class.
Start with a bounded-above resolution of the zeroth good truncation. Inductively form
its cone over the next truncation and take a bounded-above resolution of that cone.
The triangle construction in `lemma-special-direct-system` gives the next resolution
as an extension of the previous one by the new cone resolution, split in each degree.
Lift and subtract the homotopy of the augmentation square along these splittings;
this makes the square commute strictly. Add a contractible two-term complex of
flat objects covering G in degree n, as in the last paragraph of that lemma.
Its map in degree n is the chosen cover, and its map in degree n+1 covers the
boundaries. The augmentation is already surjective on cohomology in degree n+1,
so adding these boundaries makes it epimorphic on cycles, which are the last term
of the next good truncation. This gives epimorphisms in both new degrees n and n+1;
in all other degrees they follow from the previous augmentation. The five lemma
shows that the augmentation before this contractible addition is a quasi-isomorphism,
and the contractible addition preserves that property. Finite sums of resolving objects
remain flat, and all complexes in this induction are bounded above. Compose the
commuting squares with the truncation inclusions into G to obtain the displayed
compatibility. Starting the induction at zero rather than one changes no argument. -/
theorem exists_flat_truncation_tower
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    ∃ (E : ℕ → CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : ∀ n : ℕ, E n ⟶ E (n + 1))
      (q : ∀ n : ℕ, E n ⟶ G.truncLE (n : ℤ)),
      (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) ∧
      (∀ n : ℕ, QuasiIso (q n)) ∧
      (∀ (n : ℕ) (i : ℤ), Epi ((q n).f i)) ∧
      (∀ n : ℕ, t n ≫ q (n + 1) ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) =
        q n ≫ G.ιTruncLE (n : ℤ)) := by sorry

end CochainComplex
