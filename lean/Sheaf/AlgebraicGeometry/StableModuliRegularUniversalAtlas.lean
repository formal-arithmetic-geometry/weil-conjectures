/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

import Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-! # A regular arithmetic universal atlas for stable curves

Source: Stacks Project, moduli-curves.tex, Tag 0E9C, with Tags 0E79, 0E7A,
0E9A, 0E9B and 0E87; Algebra, Tag 07NF
(blueprint: lem-sfb-stable-moduli-regular-universal-atlas).

Products in the total category of stable families encode scheme presentations of
the 2-fibre products: a cone is a common family with cartesian arrows to its factors.
The cartesian arrows retain the universal curve isomorphism. Their universal
property tests every family and every base, including non-Noetherian schemes.
The integer spectrum uses the harmless universe lift `ULift ℤ`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The universal curve comparison associated to two cartesian family arrows.
It is an isomorphism over the common base, with no choice of a curve identification.
Source: Stacks Project, algebraic.tex, 2-fibre-product convention, and
moduli-curves.tex, Tag 0E9A
(blueprint: lem-sfb-stable-moduli-regular-universal-atlas). -/
def stableAtlasCurveComparison {S : Scheme.{u}} {g : ℕ}
    {X Y T : StablePointedModuli S g 0} (a : T ⟶ X) (b : T ⟶ Y) :
    Over.mk (pullback.snd X.projection a.base.left) ≅
      Over.mk (pullback.snd Y.projection b.base.left) :=
  (Over.isoMk (f := Over.mk T.projection)
    (g := Over.mk (pullback.snd X.projection a.base.left))
    a.square.isoPullback a.square.isoPullback_hom_snd).symm ≪≫
    Over.isoMk (f := Over.mk T.projection)
      (g := Over.mk (pullback.snd Y.projection b.base.left))
      b.square.isoPullback b.square.isoPullback_hom_snd

/-- Stable genus-`g` curves admit a smooth finite-type arithmetic atlas, with
regular Noetherian nerve schemes, dense smooth-family opens, universal arbitrary-base
scheme presentations, and the canonical overlap cocycle.
Source: Stacks Project, moduli-curves.tex, Tag 0E9C; Algebra, Tag 07NF
(blueprint: lem-sfb-stable-moduli-regular-universal-atlas).

Proof:
1. The arithmetic nodal stack is smooth and its stable locus is open and quasi-compact
   (`lem-sfb-arithmetic-nodal-curve-stack-smooth`,
   `lem-sfb-arithmetic-stable-open-bounded`). Its diagonal is unramified by the finite
   unramified Isom theorem (`lem-sfb-arithmetic-stable-isom-finite`). Apply
   `lem-sfb-unramified-diagonal-etale-atlas`; compose charts using
   `lem-sfb-stack-chartwise-smooth-etale-calculus` and open immersions being etale.
2. Affine opens cover the atlas (`lem-pc-fppf-affine-open-cover`). Their images in the
   stack are open (`lem-sfb-stack-point-topology-flat-lfp-open`). Quasi-compactness
   selects finitely many. Their coproduct is affine and quasi-compact by
   `lem-weil-pbc-scheme-coproduct-family`,
   `lem-weil-pbc-finite-affine-coproduct-spectrum`, and
   `lem-weil-pbc-affine-scheme-qcqs`. The chart calculus makes its map smooth over Z
   and etale surjective onto the stack. Smoothness and quasi-compactness give finite type.
3. For any stable family X/S, the finite Isom scheme over S times U represents
   S times over the moduli stack U (`lem-sfb-arithmetic-stable-isom-finite`). Its
   universal curve and two cartesian arrows form the limiting binary fan below.
   Chartwise base change makes its projection to S etale surjective, without any
   Noetherian assumption on S. The two pullback comparisons give the universal iso.
4. Iterate this construction to obtain the limiting (n+1)-fans. Their bases are
   affine: the Isom scheme is finite over the affine product, using
   `lem-weil-pbc-fibre-product-affine-spectra` and
   `lem-weil-pbc-finite-morphism-permanence`. Finite maps are finite type and
   `lem-sfb-finite-type-composition-base-change` gives finite type over Z.
   Every projection is etale by base change and permutation of the factors;
   etaleness and composition give smoothness over Z.
5. `lem-weil-pbc-finite-type-over-noetherian` gives Noetherianity. The local rings
   of Z are Q at (0) and the one-dimensional regular local rings Z_(p) at (p).
   Use `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` and
   `lem-weil-pbc-regular-ring-smooth-ascent` on the affine nerve, then
   `def-weil-regular-scheme` gives its regularity.
6. The smooth-family open is supplied by the arithmetic nodal-stack theorem.
   Over each algebraically closed field, the stable stack is DM: stack descent
   comes from the algebraic stable open, the diagonal from finite Isom, and the
   atlas from step 3 after field base change. Apply
   `lem-sfb-stable-curve-framed-trait-smoothing` and
   `lem-sfb-trait-specialization-etale-chart-density` to each etale nerve chart.
   Lift any arithmetic point to a geometric point in its field fibre. Continuity
   then gives density in the entire arithmetic nerve, not just in field fibres.
7. Each cartesian arrow identifies the nerve curve with the pulled-back universal
   curve. The comparison from factor i to j is the inverse i-identification
   followed by the j-identification. Cancellation and associativity give the
   displayed cocycle, including on the overlap and triple overlap. -/
theorem stableModuli_regular_universal_atlas (g : ℕ) (hg : 2 ≤ g) :
    ∃ U : StablePointedModuli (Spec (.of (ULift.{u} ℤ))) g 0,
      Smooth U.base.hom ∧ LocallyOfFiniteType U.base.hom ∧ QuasiCompact U.base.hom ∧
      (∀ X : StablePointedModuli (Spec (.of (ULift.{u} ℤ))) g 0,
        ∃ (T : StablePointedModuli (Spec (.of (ULift.{u} ℤ))) g 0)
          (a : T ⟶ X) (b : T ⟶ U),
          Nonempty (IsLimit (BinaryFan.mk a b)) ∧ Etale a.base.left ∧
            Surjective a.base.left) ∧
      (∀ n : ℕ,
        ∃ (N : StablePointedModuli (Spec (.of (ULift.{u} ℤ))) g 0)
          (p : Fin (n + 1) → (N ⟶ U)),
          Nonempty (IsLimit (Fan.mk N p)) ∧
          Smooth N.base.hom ∧ LocallyOfFiniteType N.base.hom ∧ QuasiCompact N.base.hom ∧
          IsNoetherian N.base.left ∧ IsRegularScheme N.base.left ∧
          (∀ i : Fin (n + 1), Etale (p i).base.left) ∧
          (∃ V : N.base.left.Opens, Dense (V : Set N.base.left) ∧
            ∀ (T : Over (Spec (.of (ULift.{u} ℤ)))) (a : T ⟶ N.base),
              Smooth (pullback.snd N.projection a.left) ↔
                Set.range a.left ⊆ (V : Set N.base.left)) ∧
          ∀ i j k : Fin (n + 1),
            stableAtlasCurveComparison (p i) (p j) ≪≫
                stableAtlasCurveComparison (p j) (p k) =
              stableAtlasCurveComparison (p i) (p k)) := by
  sorry

end AlgebraicGeometry
