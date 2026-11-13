/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageFibreCohomologyNegative
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageFibreCohomologyZero
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Fibre Betti numbers for a descended line bundle

Source: Stacks Project, Tag 0BF2, derived fibre equality preceding the first complex;
Tags 0BF0 and 0B91(2).
(blueprint: lem-sc-picard-direct-image-fibre-betti)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A descended marked fibre has no negative Betti numbers and Betti number one in degree zero.
Source: Stacks Project, Tag 0BF2, the displayed derived fibre equality; Tags 0BF0 and 0B91.
(blueprint: lem-sc-picard-direct-image-fibre-betti)

Proof: The universal structure adjunction unit at Spec kappa(s) excludes an empty
source fibre, since its source has nonzero global sections. The pullback of L is
invertible. Transport invertibility through the given descent isomorphism and
apply nonempty_iso_unit_of_invertible_field_pullback to the finite locally free N.
Its rank is one; pull its trivialization to the source fibre. Since k is an
immersion, kappa(w) and kappa(s) are canonically isomorphic. The canonical residue
map factors through Spec of this field isomorphism, so L is also trivial on the
fibre over Spec kappa(w). Invertible coefficients are finitely presented and flat
relative to the flat f. Proper relatively flat derived base change identifies
the derived residue of R(f_W)_*(L_W[0]) with the right-derived direct image of
this trivial fibre bundle. A right-derived functor on a degree-zero sheaf has
zero negative cohomology. In degree zero it is ordinary pushforward. The tensor
pullback structure isomorphism followed by the assumed adjunction unit identifies
this pushforward with the structure module on Spec kappa(w). Global sections and
GammaSpecIso identify its scalar module with kappa(w), of dimension one. This
uses neither any target family nor injectivity in degree one. -/
theorem picard_directImage_fibre_betti
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    (∀ j : ℤ, j < 0 → derivedFiberBetti W E j w = 0) ∧
      derivedFiberBetti W E 0 w = 1 := by
  constructor
  · intro j hj
    have hz := picard_directImage_fibre_cohomology_negative f L W k w j hj
    let : Subsingleton (derivedFiberCohomology W _ j w) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    exact Module.finrank_zero_of_subsingleton
  · obtain ⟨e⟩ := picard_directImage_fibre_cohomology_zero f hO L W k w s hw hLs
    exact e.toLinearEquiv.finrank_eq.trans (Module.finrank_self _)

end AlgebraicGeometry.Scheme
