/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

/-! # Uniform geometric fibre bound for an étale scheme chart

Source: Stacks Project, Decent Algebraic Spaces, Tags 03JX (lemma-bounded-fibres),
(eta) implies (delta), and 03JT (lemma-U-universally-bounded)
(blueprint: lem-sfb-space-qc-etale-fibre-bound).

A geometric fibre is specified by a representing scheme pullback square of presheaves.
Absolute quasi-separatedness uses the existing affine-test criterion, so the base scheme
is arbitrary. The chart need not be surjective, separated, or quasi-separated.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale map from a quasi-compact scheme to an absolutely quasi-separated algebraic
space has finite discrete geometric fibres with a single bound on their numbers of points.
The scheme `F`, its maps `p` and `q`, and the pullback condition specify the actual geometric
fibre; `IsFinite p.left` asserts finiteness over the geometric field.
Source: Stacks Project, Decent Algebraic Spaces, Tags 03JX and 03JT
(blueprint: lem-sfb-space-qc-etale-fibre-bound).

Proof:
1. Choose a finite affine open cover `V_j` of `U`, using
   [lem-weil-pbc-affine-opens-basis] and compactness. Allow the empty cover of the empty
   scheme. By [lem-sfb-space-qcqs-permanence](1), `U → X` is quasi-compact because `U`
   is quasi-compact and `X` is absolutely quasi-separated. Thus `R_j = U ×_X V_j` is
   a quasi-compact scheme, without requiring quasi-separatedness of `U`.
2. Its projection `R_j → V_j` is étale by [def-trf-algebraic-space] and
   [lem-trf-space-fibre-products-etale-covers]. Étale implies unramified by
   [def-weil-etale-morphism]; [lem-weil-pbc-unramified-quasi-finite-at-points] makes
   this projection locally quasi-finite.
3. Apply [lem-weil-pbc-lqf-qc-source-bounded-fibres] to obtain bounds `d_j`.
   By [lem-weil-pbc-fibre-degree-bound-field-points], every field pullback of this
   projection is finite with dimension of global sections at most `d_j`. Set
   `d = ∑ j, d_j`, which is zero for the empty cover.
4. For a geometric point `x`, represent `U ×_X Spec Ω` by a scheme `F`, using the
   representable étale hypothesis. It is étale over `Ω`. By
   [lem-weil-pbc-etale-fibre-discrete-separable-points] it is a disjoint union of
   spectra of finite separable extensions of `Ω`. Algebraic closedness makes these
   extensions equal to `Ω`: each minimal polynomial has a root and is irreducible,
   hence linear. Therefore `F` is discrete, and each point gives an `Ω`-section.
5. If `F` is nonempty, choose such a section and its image `u : Spec Ω → U`.
   It factors through some `V_j`. Pullback reassociation, from
   [lem-trf-space-fibre-products-etale-covers], identifies `F` with the field fibre
   of `R_j → V_j` at this lift. On any test over `Ω`, both sides are precisely maps
   `z` into `U` satisfying `a z = x`; the other coordinate is forced by the lift.
   Thus `F → Spec Ω` is finite and its section dimension is at most `d_j ≤ d`.
6. A finite scheme over `Ω` is quasi-compact. Its discrete open point components
   therefore form a finite family of `r` copies of `Spec Ω`; global sections are
   `Ω^r`, of dimension `r`. Consequently `Nat.card F ≤ d`. If `F` is empty its
   projection is finite and its cardinality is zero. This also gives `d = 0` for
   the empty chart. -/
theorem exists_uniform_geometricFibre_bound {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hX : IsAbsolutelyQuasiSeparated X) (U : Over S) [CompactSpace U.left]
    (a : yoneda.obj U ⟶ X.obj.obj) (ha : IsEtale a) :
    ∃ d : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ S)
      (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj),
      ∃ (F : Over S) (p : F ⟶ Over.mk s) (q : yoneda.obj F ⟶ yoneda.obj U),
        IsPullback q (yoneda.map p) a x ∧ IsFinite p.left ∧
          DiscreteTopology F.left ∧ Nat.card F.left ≤ d := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
