/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat

/-! # The flat single-cohomology open locus

Source: the cohomology-sheaf gluing paragraph of the perfect-locus proof
(blueprint: lem-pc-derived-single-open-locus).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A connective derived object locally concentrated in one finite locally free degree
on a set of points is a flat single object on an open neighbourhood of that set.

Source: blueprint lem-pc-perfect-locus, cohomology-sheaf gluing paragraph; the first
step of lem-pc-derived-pullback-single-cohomology.
(blueprint: lem-pc-derived-single-open-locus).

Proof: take W to be the union of all opens satisfying the local hypothesis. Every point
of the given set lies in W. Exact open restriction preserves negative vanishing. In
nonnegative degrees other than i the cohomology sheaves vanish on the covering opens,
hence on W by the sheaf condition. The degree-i sheaf is locally finite free on this
cover and therefore flat: tensoring is exact locally, hence exact globally. Exactness
of open restriction identifies these sheaves with the cohomology of L(W.ι)^* E.
Standard truncations of an object with cohomology in degree i only give its isomorphism
to its degree-i cohomology placed in degree i. This construction uses no uniform rank,
and works on the empty open and with the zero sheaf. -/
theorem exists_flat_single_open_locus
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T : Scheme.{u}} (S : Set T) (E : schemeDerivedCategory T) (i : ℕ)
    (hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E))
    (hloc : ∀ t ∈ S, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ,
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E)) i r) :
    ∃ W : T.Opens, S ⊆ W ∧
      SheafOfModules.IsFlat ((Modules.restrictFunctor W.ι).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E)) ∧
      Nonempty ((derivedPullback W.ι).obj E ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj
            ((Modules.restrictFunctor W.ι).obj ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E))) := by sorry

end AlgebraicGeometry.Scheme.Modules
