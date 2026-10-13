/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-! # K-injective section homology from affine-basis acyclicity

Source: Stacks Project, Tag 08C2, singleton cover; Tag 071B, compatible resolution tower.
(blueprint: lem-sc-affine-basis-kinjective-sections-preserves-homology).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Sections preserve homology of a K-injective complex with acyclic homology
on an affine basis of V.
Source: Stacks Project, Tag 08C2, unbounded comparison via Tag 071B;
Tag 08D4, its tower argument adapted using the basis hypothesis of Tag 071B.
(blueprint: lem-sc-affine-basis-kinjective-sections-preserves-homology).

Proof: Restrict F to V; exact extension by zero shows this preserves K-injectivity.
Use the affine basis contained in V. The positive cohomology of every homology
sheaf vanishes on each member, giving uniform cohomological bound zero on this
family. For bounded-below truncations the hypercohomology spectral sequence has
only its p=0 row, so derived sections of each truncation have homology equal to
sections of its homology sheaves. For the unbounded complex use the compatible
resolution tower of Tag 071B: sections commute with its inverse limit, the
transition maps are degreewise surjective, and the degree-r homology systems are
eventually constant. The Milnor exact sequence therefore identifies degree-r
limit homology with sections of H^r(F). This reuses the tower argument of
Tag 08D4, not its quasi-coherent statement: Tag 071B supplies convergence here,
and the assumed vanishing on the actual homology sheaves supplies the bound.
Upper truncation in degree n
preserves degree-n raw sections homology by left exactness; its map to H^n(F)[-n]
is the quotient from cycles. Naturality of raw-to-derived sections, invertible
for K-injectives, identifies the resulting isomorphism with this cycle-class
map, not just with an arbitrary isomorphism. Hence sections of the quotient
from cycles are surjective and their kernel is the section differential image.
Sections preserve the cycle kernel, so this is exactly preservation of left
homology data. Underlying abelian-sheaf cohomology computes module sections:
injective module sheaves are flasque and exact forgetting reflects exactness.
Empty V gives zero modules, and all integer degrees and zero complexes are covered. -/
theorem affineBasisKInjectiveSections_preservesLeftHomology
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F : CochainComplex X.Modules ℤ) [F.IsKInjective]
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1))) (n : ℤ) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    S.PreservesLeftHomologyOf (F.sc n) := by sorry

end AlgebraicGeometry
