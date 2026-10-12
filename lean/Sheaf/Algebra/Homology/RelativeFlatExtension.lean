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
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct

/-!
# A relative flat replacement before imposing termwise epimorphy

Source: Stacks Project, Derived Categories, Lemma 06XX, triangle and homotopy
correction part of the induction step.
(blueprint: lem-pc-relative-flat-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- A flat replacement of a mapping cone gives a relative flat replacement,
strictly as chain maps.
Termwise epimorphy of the new resolution is not asserted here.

Source: Stacks Project, Derived Categories, Lemma 06XX, triangle construction
and homotopy correction (https://stacks.math.columbia.edu/tag/06XX).
(blueprint: lem-pc-relative-flat-extension).

Proof: The prescribed quasi-isomorphism r : Q -> Cone(f), followed by the
cone projection to E[1], determines a triangle
E -> F -> Q -> E[1]. Realize it by the shifted cone of this composite; the
sequence E -> F -> Q is degreewise split and F^i is E^i plus Q^i. Thus F is
bounded above and flat by finite coproduct flatness. The cone triangle and this
triangle give a morphism of triangles with identity on E and Q -> C on the
third term. The middle map g : F -> H is a quasi-isomorphism by the long exact
cohomology sequences. The square with E commutes up to homotopy. Extend the
homotopy degreewise from E to F using the split retractions and subtract its
homotopy differential from g. This changes neither its cohomology maps nor its
chain-map property and gives t >> g = f strictly. Neither f nor its components
need be quasi-isomorphisms or epimorphisms. For E = 0 the given Q resolves H;
for H = 0 the cone construction still applies. Bounds on E and Q may differ. -/
theorem exists_relative_boundedAbove_flat_extension
    (E H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i))
    (Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (r : Q ⟶ mappingCone f)
    (hQ : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (Q.X i))
    (hflatQ : ∀ i : ℤ, SheafOfModules.IsFlat (Q.X i)) (hr : QuasiIso r) :
    ∃ (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (t : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (F.X i)) ∧ QuasiIso g ∧ t ≫ g = f := by
  sorry

end CochainComplex
