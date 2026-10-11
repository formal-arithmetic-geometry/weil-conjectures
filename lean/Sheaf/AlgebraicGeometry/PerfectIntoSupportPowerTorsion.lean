/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Maps from perfect complexes into principal support

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.13.9, Tag 08EJ
(blueprint: lem-sc-perfect-into-support-on-T).

Global functions are encoded as compatible families of local sections. On the Zariski
site, evaluation at the top open identifies this ring with the usual global section ring.
The action on derived morphisms is the localization of the sectionwise scalar action.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Maps from a perfect complex into a quasi-coherent complex supported on `V(f)` are
annihilated by a power of `f`. Source: Stacks Project, Tag 08EJ
(blueprint: lem-sc-perfect-into-support-on-T).

Proof. First take an affine scheme `Spec A`. The affine derived equivalence
[lem-pc-affine-qcoh-derived-equivalence] and the finite-projective model
[lem-pc-perfect-affine-bounded-projective] represent the source by a bounded complex of
finite projectives. Induct on its length using the stupid-truncation triangle at its
highest nonzero term. Exactness of Hom means that killing the image in the single-term
Hom group makes the map lift from the shorter complex; the two killing exponents add.
After shifting, the single-term case is a map from a finite projective module `P` into
`H⁰(M)`. Vanishing on `D(f)` says every element of `H⁰(M)` is killed by a power of `f`.
One exponent kills the images of finitely many generators of `P`.

For globalization, induct on quasi-compact opens [lem-sc-invert-s-cohomology-induction].
For `W = U ∪ V`, choose an exponent killing both restrictions. Mayer--Vietoris for Hom
[lem-sc-derived-hom-mayer-vietoris] lifts the resulting map from a morphism on `U ∩ V`
into the shifted target. The overlap is quasi-compact by quasi-separatedness. Induction
kills that lift by another power. Linearity of the boundary map makes the sum of the
exponents kill the original map. Restrictions preserve perfectness and support, and
shifting preserves support, so the induction applies throughout. -/
theorem exists_pow_smul_eq_zero_of_perfect_supported
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E E' : schemeDerivedQCohCategory X) (α : E ⟶ E')
    (hE : X.IsPerfect E.obj)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x))) :
    ∃ n : ℕ, schemeDerivedScalar X (f ^ n) α.hom = 0 := by
  sorry

end AlgebraicGeometry.Scheme
