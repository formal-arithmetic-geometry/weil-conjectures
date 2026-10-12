/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # A global derived model for relatively flat higher direct images

Source: Stacks Project, Tag 0B91(2), and the injective-resolution definition of
higher direct images (blueprint: lem-pc-higher-direct-image-derived-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Higher direct images of a finitely presented relatively flat module have one global
connective derived model, with cohomology computing every cartesian base change.

Source: Stacks Project, Tag 0B91(2); Tag 079V for computation by injective resolutions.
(blueprint: lem-pc-higher-direct-image-derived-model).

Proof: take E = Rf_*(F[0]). Resolve F by an injective resolution in nonnegative degrees.
The resulting bounded-below complex of injectives is K-injective after embedding
into integer complexes.
Applying f_* computes the unbounded derived direct image and its degree-q cohomology is
exactly the right derived functor defining higherDirectImage f q. Its negative cohomology
vanishes because this resolution is nonnegative. Relative flatness and finite presentation
allow Tag 0B91(2) to identify Lg^*E with Rf'_*(g'^*F[0]) for every cartesian square.
For a chosen square rather than the standard categorical pullback, transport this
isomorphism along sq.isoPullback and the pullback composition isomorphisms. Take degree-q
cohomology and use the same injective-resolution comparison on X' to obtain the last
clause. These are global derived isomorphisms, so their cohomology identifications are
compatible on overlaps, rather than choices of unrelated local free trivializations. -/
theorem exists_derived_model_higherDirectImage
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation] (hF : F.IsFlatOver f) :
    ∃ E : schemeDerivedCategory T,
      (∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E)) ∧
      (∀ q : ℕ, Nonempty ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E ≅
          (higherDirectImage f q).obj F)) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g → ∀ q : ℕ,
        Nonempty ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) q).obj
            ((derivedPullback g).obj E) ≅
              (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
