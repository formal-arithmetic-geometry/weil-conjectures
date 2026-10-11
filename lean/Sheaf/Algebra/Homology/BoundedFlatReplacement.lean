/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Functorial bounded-above flat replacements on a ringed site

Source: Stacks Project, Cohomology on Sites, Lemma 06YS, via Lemma 077J;
Derived Categories, Lemma 05T7 (1); Modules on Sites, Lemma 03EW (3), (4)
(blueprint: lem-pc-kflat-bounded-flat-replacement).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Bounded-above complexes on a ringed site have functorial termwise epimorphic
quasi-isomorphisms from flat complexes with the same upper bound.
The full subcategory below consists of complexes whose terms vanish above `N`.
Epimorphisms here are epimorphisms of sheaves, hence locally surjective maps.
Source: Stacks Project, Lemma 06YS via 077J and 06XX, using the cycle-pullback
construction of Lemma 05T7 (1) and the canonical flat covers of Lemma 03EW (3), (4)
(blueprint: lem-pc-kflat-bounded-flat-replacement).

Proof: (1) For a module sheaf `M`, take the canonical epimorphism `Q(M) → M`
indexed by pairs `(U,s)` of an object and a section, using
lem-pc-sites-modules-quotient-j-shriek. Its summands are flat by
lem-pc-sites-modules-j-shriek-flat, and its coproduct is flat by
lem-pc-sites-modules-coproduct-flat. Start at degree `N` and descend, applying `Q`
to `F^i ×_{F^{i+1}} Z(E^{i+1})`. The projections give the augmentation and a
differential landing in cycles, so the square of the differential is zero.
The map on cycles is epimorphic inductively (lift a cycle by the pair `(z,0)`),
so each pullback projects epimorphically onto `F^i`. Set all terms above `N` to zero.
(2) Every cycle in the kernel of the augmentation lifts through the pair `(0,k)`
in the preceding pullback. Thus this kernel is acyclic, and the short exact
sequence gives a quasi-isomorphism, by def-pc-quasi-iso-modules.
(3) The canonical indexed generators send `(U,s)` to `(U,f(s))` under a module map.
Inductively this induces maps of the pullbacks and of their flat covers,
commuting with the differentials and augmentations. Identities and compositions
are respected, giving the functor and natural transformation asserted here. -/
theorem exists_functorial_boundedAbove_flat_replacement
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (N : ℤ) :
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    let P : ObjectProperty (CochainComplex A ℤ) :=
      fun F => ∀ (i : ℤ), N < i → IsZero (F.X i)
    ∃ Q : P.FullSubcategory ⥤ CochainComplex A ℤ,
      ∃ ε : Q ⟶ P.ι,
        ∀ F : P.FullSubcategory,
          (∀ (i : ℤ), SheafOfModules.IsFlat ((Q.obj F).X i)) ∧
          (∀ (i : ℤ), N < i → IsZero ((Q.obj F).X i)) ∧
          (∀ (i : ℤ), Epi ((ε.app F).f i)) ∧ QuasiIso (ε.app F) := by
  sorry

end CochainComplex
