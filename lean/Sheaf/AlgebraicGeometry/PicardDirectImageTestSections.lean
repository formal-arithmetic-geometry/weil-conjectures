/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

public import Sheaf.AlgebraicGeometry.PicardDerivedModelSections

import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare

/-! # Derived test sections of a base-changed direct image

Source: Stacks Project, Tags 0B91 and 08HY.
(blueprint: lem-sc-picard-direct-image-test-sections)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Arbitrary base change identifies derived test sections of the direct image with
sections upstairs, and the identification respects the canonical fibre restriction.
This assertion has no perfect model, scalar basis, differential, or cycle hypothesis.
Source: Stacks Project, Tag 0B91, arbitrary base change; Tag 08HY, canonical mate;
Tag 01IQ, residue fibre image.
(blueprint: lem-sc-picard-direct-image-test-sections)

Proof: Put E=R(f_W)_*(L_W[0]). Invertible L is finitely presented and flat relative to
f, since f is flat; these properties survive arbitrary base change. Tag 0B91 identifies
Lt^*E with R(f_T)_*(L_T[0]), using the canonical base-change map and tensor-pullback
composition. The pulled-back degree-zero structure sheaf is canonically the structure
sheaf of T. Derived adjunction and full faithfulness of the single functor identify
morphisms from it to R(f_T)_*(L_T[0]) with ordinary global sections of L_T. All these
identifications are additive; denote their composite by q t. Factor the residue point
through V using picardResidueLift, and form the cartesian comparison j:Y -> X_V. The
image of j is exactly the fibre over w, by the residue-field fibre description; every
point above w lifts. Tensor-pullback composition supplies e:j^*L_V -> L_Y. The canonical
mate square, after H0 and evaluation on the top open, identifies pullback of a derived
test section with the adjunction unit on q V ξ followed by e. Composition comparisons
are canonical, so this is the conjugation defining picardDerivedModelRestriction.
The unit at top is restricted along j inverse top = top, giving exactly the displayed
expression. Empty fibres yield zero section groups; no nonempty-fibre assumption is used. -/
theorem picard_direct_image_test_sections
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) (w : W) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∃ q : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        picardDerivedModelSections E t ≃+
          Γ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L, ⊤),
      ∀ (V : W.Opens) (hwV : w ∈ V),
        ∃ j : pullback f (W.fromSpecResidueField w ≫ k) ⟶ pullback f (V.ι ≫ k),
          (∀ x : (pullback f (V.ι ≫ k) : Scheme.{v}),
            (pullback.snd f (V.ι ≫ k)) x = (⟨w, hwV⟩ : V.toScheme) →
              ∃ y, j y = x) ∧
          ∃ e : (Modules.tensorPullback j).obj
              ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L) ≅
              (Modules.tensorPullback
                (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L,
            ∀ ξ : picardDerivedModelSections E V.ι,
              e.hom.app ⊤
                (((Modules.tensorPullback j).obj
                  ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).presheaf.map
                    (homOfLE j.preimage_top.ge).op
                      (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                        ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).val.app
                          (Opposite.op ⊤) (q V.ι ξ))) =
                q (W.fromSpecResidueField w)
                  (picardDerivedModelRestriction E (picardResidueLift W w V hwV) V.ι
                    (W.fromSpecResidueField w) (picardResidueLift_comp W w V hwV) ξ) := by sorry

end AlgebraicGeometry.Scheme
