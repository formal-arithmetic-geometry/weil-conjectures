/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.Picard.RationalPointBaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization

/-!
# Projective curve realization of two fibres of a line family

Source: Charles--Poonen, Corollary 1.9, printed p.4; Milne, Abelian Varieties,
Chapter I, Lemma 3.5(a), printed p.18; Stacks, Tags 0BD9 and 0AG0.
The assertion assembles curve interpolation, completion, and extension of invertible modules.
(blueprint: lem-sfb-line-family-projective-curve-interpolation).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Two fibres of an invertible module over a smooth connected parameter scheme admit a
realization over a smooth projective geometrically integral curve. The fibres are tensor
pullbacks along the base-changed rational points, with the factors reordered by symmetry.

Source: Charles--Poonen, Corollary 1.9, printed p.4; Milne, Abelian Varieties,
I.3.5(a), printed p.18; Stacks, Tags 0BD9 and 0AG0.
(blueprint: lem-sfb-line-family-projective-curve-interpolation).

Proof:
1. By lem-weil-pbc-smooth-scheme-over-field-regular, the parameter scheme is regular;
   lem-sc-regular-connected-integral makes it integral. Apply
   lem-sfb-integral-variety-smooth-curve-interpolation through the two given points.
   This yields a smooth connected separated curve D mapping to S, with lifts d0,d1.
   Reuse the same lift if the points agree. Pull L back to Z times D using
   lem-weil-pbc-invertible-pullback-tensor (1).
2. By lem-sc-compactification, complete D to a smooth proper connected curve C.
   Use lem-sc-curves-quasi-projective and lem-weil-pbc-projective-space-proj-separated
   to embed C locally closed into projective space. By lem-weil-pbc-proper-to-separated
   and lem-weil-pbc-proper-immersion-closed this immersion is closed, so C is projective.
3. By lem-weil-geometrically-connected-algebraic-closure C is geometrically connected.
   By lem-trf-smooth-geometrically-normal it is geometrically normal. Apply
   lem-trf-geonormal-geoconnected-finite-type-integral to get geometric integrality.
4. The inclusion Z times D into Y = Z times C is open by
   lem-weil-pbc-open-immersion-base-change. By lem-pc-proper-base-change and
   lem-trf-smooth-composition Y is smooth over k, hence regular and locally Noetherian
   by lem-weil-pbc-smooth-scheme-over-field-regular. Use
   lem-weil-pbc-regular-local-localization and
   lem-trf-regular-local-ufd-boundary-factorization with r = 0 at every local ring.
   Then lem-sfb-invertible-extension-factorial-complement extends the line on Z times D
   to an invertible E on Y. No integrality or connectedness of Z is needed.
5. Take a,b to be the images of d0,d1. The composites of the fibre inclusions with
   the restriction maps are the original inclusions at s0,s1. Composition of tensor
   pullback (lem-weil-pbc-invertible-pullback-tensor (2)) identifies E_a with L_s0
   and E_b with L_s1. This also applies when a = b or Z is empty. -/
theorem exists_projectiveCurve_lineFamily_fibres
    (k : Type u) [Field k] [IsAlgClosed k]
    (Z S : Scheme.{u}) [Z.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [Smooth (Z ↘ Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [Smooth (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [ConnectedSpace S]
    (s0 s1 : (S ↘ Spec (.of k)).fieldPoints k)
    (L : (pullback (Z ↘ Spec (.of k)) (S ↘ Spec (.of k))).Modules)
    [Scheme.Modules.IsInvertible L] :
    ∃ (C : Scheme.{u}) (f : C ⟶ Spec (.of k)),
      IsSmoothProjectiveCurve f ∧ GeometricallyIntegral f ∧
      ∃ (a b : f.fieldPoints k)
        (E : (pullback (Z ↘ Spec (.of k)) f).Modules),
        Scheme.Modules.IsInvertible E ∧
        Nonempty
          ((Scheme.Modules.tensorPullback
            (f.fieldPointBaseChange a (Over.mk (Z ↘ Spec (.of k))) ≫
              (pullbackSymmetry f (Z ↘ Spec (.of k))).hom)).obj E ≅
           (Scheme.Modules.tensorPullback
            ((S ↘ Spec (.of k)).fieldPointBaseChange s0 (Over.mk (Z ↘ Spec (.of k))) ≫
              (pullbackSymmetry (S ↘ Spec (.of k)) (Z ↘ Spec (.of k))).hom)).obj L) ∧
        Nonempty
          ((Scheme.Modules.tensorPullback
            (f.fieldPointBaseChange b (Over.mk (Z ↘ Spec (.of k))) ≫
              (pullbackSymmetry f (Z ↘ Spec (.of k))).hom)).obj E ≅
           (Scheme.Modules.tensorPullback
            ((S ↘ Spec (.of k)).fieldPointBaseChange s1 (Over.mk (Z ↘ Spec (.of k))) ≫
              (pullbackSymmetry (S ↘ Spec (.of k)) (Z ↘ Spec (.of k))).hom)).obj L) := by
  sorry

end AlgebraicGeometry
