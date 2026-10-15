/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso

/-!
# K-flat replacements of strict diagrams

Source: Stacks Project, Cohomology on Sites, Tags 077J, 0G7E and 06YY,
applied to the small diagram site (blueprint: lem-weil-pbc-diagram-kflat-replacements).

A strict diagram of complexes is a functor into cochain complexes. Its maps are natural
transformations, so the replacements include the transition maps, not just objects of
derived categories. Module pullback is specified by its adjunction to the induced module
direct image: this characterizes the usual inverse image followed by extension of scalars.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

/-- Strict diagrams admit objectwise K-flat resolutions with flat terms.
Source: Stacks Project, Tags 077J and 06YS on the diagram site
(blueprint: lem-weil-pbc-diagram-kflat-replacements).

Proof:
1. Realize strict diagrams as module sheaves on the small site `J.op × C`, by
   `lem-weil-pbc-diagram-site-realization`. Transport the entire complex to this site.
2. Apply `lem-pc-kflat-resolution` there, and transport its degreewise epimorphic
   quasi-isomorphism back through the exact module equivalence.
3. Evaluation is exact, so the augmentation is degreewise epimorphic and a
   quasi-isomorphism at every object. Evaluation is also ringed-topos pullback;
   `lem-weil-pbc-ringed-topos-kflat-pullback` makes each evaluated complex K-flat
   with flat terms. All maps remain natural transformations of strict diagrams. -/
theorem exists_diagram_isKFlatResolution
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    (R : Sheaf T CommRingCat.{u}) {J : Type u} [SmallCategory J]
    (M : J ⥤ CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ∃ (P : J ⥤ CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) (p : P ⟶ M),
      (∀ j : J, (P.obj j).IsKFlat) ∧
      (∀ (j : J) (q : ℤ), SheafOfModules.IsFlat ((P.obj j).X q)) ∧
      (∀ j : J, QuasiIso (p.app j)) ∧
      (∀ (j : J) (q : ℤ), Epi ((p.app j).f q)) := by
  sorry

/-- Ringed-topos pullback preserves objectwise quasi-isomorphisms between K-flat
strict diagrams with flat terms. Source: Stacks Project, Tags 0G7E and 06YY
(blueprint: lem-weil-pbc-diagram-kflat-replacements).

The adjunction identifies `E` with module pullback, hence with inverse image followed
by the change of rings of `def-pur-sheaf-tensor-product`. Its additive structure is the
usual one; any choice of this left adjoint gives the same assertion.

Proof:
1. Apply `lem-weil-pbc-ringed-topos-kflat-pullback` to inverse image before scalar
   extension. The inverse images of both evaluated complexes are K-flat.
2. Inverse image is exact, so it preserves the evaluated quasi-isomorphism.
3. Apply `lem-pur-change-of-rings-kflat-quasi-iso` to the structural ring map and
   this quasi-isomorphism. This gives the desired quasi-isomorphism at each object.
4. Applying the functor `E` to the naturality, composition and differential equations
   preserves them, so these maps form a strict diagram morphism. -/
theorem diagram_pullback_quasiIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (T : GrothendieckTopology C) (T' : GrothendieckTopology D)
    (R : Sheaf T CommRingCat.{u}) (R' : Sheaf T' CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj R')
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
    (E : ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj R'))
    [E.Additive] (adj : E ⊣ f.modules)
    {J : Type u} [SmallCategory J]
    {P Q : J ⥤ CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (α : P ⟶ Q)
    (hP : ∀ j : J, (P.obj j).IsKFlat)
    (hQ : ∀ j : J, (Q.obj j).IsKFlat)
    (hPf : ∀ (j : J) (q : ℤ), SheafOfModules.IsFlat ((P.obj j).X q))
    (hQf : ∀ (j : J) (q : ℤ), SheafOfModules.IsFlat ((Q.obj j).X q))
    (hα : ∀ j : J, QuasiIso (α.app j)) :
    ∀ j : J, QuasiIso
      ((Functor.whiskerRight α (E.mapHomologicalComplex (ComplexShape.up ℤ))).app j) := by
  sorry

end CochainComplex
