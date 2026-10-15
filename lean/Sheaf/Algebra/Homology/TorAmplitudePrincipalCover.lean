/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolution
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.KFlatModuleBaseChange
import Sheaf.RingTheory.HomologyVanishingLocalizationSpan

/-!
# Tor amplitude descends from a finite principal cover

Source: Stacks Project, More on Algebra, Tag 066N, lemma-glue-tor-amplitude
(blueprint: lem-weil-pbc-tor-amplitude-principal-cover-glue).
-/

@[expose] public section

universe w₁ w₂ u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Tor amplitude in a fixed interval descends from a finite principal localization cover.
Source: Stacks Project, More on Algebra, Tag 066N, lemma-glue-tor-amplitude.
(blueprint: lem-weil-pbc-tor-amplitude-principal-cover-glue).

The termwise `extendScalars` is ordinary localization of the complex. The derived tensor in
`torAmplitudeIn` is tested against every module in degree zero, without a flatness condition;
it is computed on K-flat models by `QObjTensorQObjIsoOfKFlatLeft`. This is the ordinary-module
specialization of change of rings on the singleton site with the trivial topology.

Proof: Fix a module M and a degree n outside [a,b]. Choose a K-flat resolution P of K
(lem-pc-kflat-resolution). The complex C = P tensor M computes K tensor-derived M by
lem-pc-source-kflat-module-tensor-model. Localization is flat
(lem-weil-pbc-localization-flat), so exactness of flat tensor
(lem-weil-pbc-flat-tensor-exact) identifies localized cycles, boundaries and cohomology;
in particular P localized remains a resolution of K localized. By
lem-pc-kflat-extension-of-scalars, P localized is K-flat over the localized ring. Applying
lem-pc-source-kflat-module-tensor-model over that ring identifies C localized with the tensor
of P localized and M localized: on pure tensors the comparison multiplies the two scalar
factors, with inverse putting the scalar in the first factor and 1 in the second. These
maps respect balancing and commute with the differential. The assumed local amplitude
therefore kills H^n(C localized). Finally lem-pc-homology-vanishing-localization-span kills
H^n(C), since the f i generate the unit ideal. Vary M and n. For an empty family the
unit-ideal condition forces the zero ring, so the same vanishing argument applies. -/
theorem torAmplitudeIn_of_principal_cover
    {R : Type u} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (_hab : a ≤ b)
    (r : ℕ) (f : Fin r → R)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{u} (Localization.Away (f i)))]
    (_hf : Ideal.span (Set.range f) = ⊤)
    (_hlocal : ∀ i : Fin r,
      torAmplitudeIn (ModuleCat.{u} (Localization.Away (f i))) a b
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap R (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj K))) :
    torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj K) := by
  sorry

end DerivedCategory
