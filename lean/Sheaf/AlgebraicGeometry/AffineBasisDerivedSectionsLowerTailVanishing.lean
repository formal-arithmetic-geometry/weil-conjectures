/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! # Derived sections vanish above a lower tail with basis-acyclic homology

Source: Stacks Project, Tag 0BKT (cohomology-over-U-trivial), applied to the
strictly lower tail; Tags 071B and 0D64 for its tower reconstruction.
(blueprint: lem-sc-affine-basis-derived-sections-lower-tail-vanishing).
-/

@[expose] public section

universe u wC wD
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Derived sections of the part strictly below `a` vanish in degrees at least `a`.
This is a statement about the lower tail only, without K-injectivity or a raw
cycle-class map.

Source: Stacks Project, Tag 0BKT, lemma-cohomology-over-U-trivial, applied to
the strictly lower tail; its proof uses Tag 0D64 and the bounded-below
hypercohomology spectral sequence. Tag 071B gives the compatible resolution model.
(blueprint: lem-sc-affine-basis-derived-sections-lower-tail-vanishing).

Proof: Restrict the derived lower tail to V. Affine opens W contained in V form
an open basis, including V itself. Its homology in degrees r < a is the restriction
of H^r(F); in degrees r >= a it is zero. Thus all its homology sheaves have
vanishing positive cohomology on this basis. Apply the compatible bounded-below
injective resolution tower of Tag 071B, after a shift of the cutoff if necessary.
Tag 0D64 identifies its limit with the lower tail. Its transitions are split
surjections degreewise, with injective kernels; applying sections preserves these
surjections and commutes with the inverse limit. For each bounded-below truncation,
the convergent hypercohomology spectral sequence has only its sections row:
positive cohomology of the actual homology sheaves vanishes also on V. Hence its
cohomology in degree i >= a is zero, and in degree i-1 the groups and transition
maps stabilize once the lower cutoff is below i-1. Apply the Milnor exact sequence.
The first derived limit in degree i-1 vanishes since its transitions are eventually
isomorphisms; the degree-i inverse limit is zero. Thus limit cohomology in degree i
is zero. This proves the claim for the canonical derived sections functor, not
for a chosen unrelated cohomology object. The exact module-to-abelian cohomology
comparison converts the stated source H vanishings to module sections vanishings;
forgetting modules reflects zero objects. Empty V yields the zero module category;
zero complexes and arbitrary integer a and i obey the same argument. No termwise
acyclicity, differential-cokernel acyclicity, or boundedness of F is assumed. -/
theorem affineBasisDerivedSections_lowerTail_isZero
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V)))]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a i : ℤ) (hai : a ≤ i) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (S.rightDerivedFunctor.obj
        ((DerivedCategory.TStructure.t.truncLT a).obj (DerivedCategory.Q.obj F)))) := by sorry

end AlgebraicGeometry
