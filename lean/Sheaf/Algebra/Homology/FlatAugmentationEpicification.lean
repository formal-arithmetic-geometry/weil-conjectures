/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits

import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-!
# Making a bounded flat augmentation termwise epic using identity disks

Source: Stacks Project, Derived Categories, Lemma 06XX, contractible-disk step.
(blueprint: lem-pc-flat-augmentation-epicification).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- Adding bounded-above flat identity disks makes any augmentation to a
bounded-above complex epic without changing the source up to quasi-isomorphism.

Source: Stacks Project, Derived Categories, Lemma 06XX, final contractible-disk
addition (https://stacks.math.columbia.edu/tag/06XX), applied in every degree.
(blueprint: lem-pc-flat-augmentation-epicification).

Proof: Choose a bound N for H. In each degree i <= N choose a flat epic cover
p_i : P_i -> H^i using hcover; put P_i = 0 for i > N. Construct the direct
sum D of identity disks on P_i in degrees i,i+1. Explicitly D^j is the finite
sum P_j plus P_(j-1), its differential sends the first summand identically to
the second summand in degree j+1 and kills the second. This complex has a
contracting homotopy sending the second summand to the first in degree j-1.
The maps p_i and p_i >> d_H assemble to a chain map a : D -> H. Each component
is epic, since its restriction to P_i is p_i when i <= N, and H^i is zero
otherwise. Set F = E plus D, let s be the first inclusion, and g = [f,a].
Then s >> g = f strictly, g is termwise epic, and s is a homotopy equivalence
because D is contractible, hence a quasi-isomorphism. The terms of F are finite
sums of flat objects, including zero terms, so are flat. Both E and D are
bounded above; D vanishes above N+1. Thus F is bounded above. No assumption on
the cohomology or the components of f is used. Zero H allows D = 0; arbitrary
bounds and negative N are covered by the same construction. -/
theorem exists_boundedAbove_flat_epicification
    (hcover : ∀ M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ∃ (P : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (p : P ⟶ M),
        SheafOfModules.IsFlat P ∧ Epi p)
    (E H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hH : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (H.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i)) :
    ∃ (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (s : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (F.X i)) ∧ QuasiIso s ∧
      (∀ i : ℤ, Epi (g.f i)) ∧ s ≫ g = f := by
  sorry

end CochainComplex
