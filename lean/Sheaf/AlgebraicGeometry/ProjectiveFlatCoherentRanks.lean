/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Constructible
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover
import Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel
import Sheaf.AlgebraicGeometry.FiniteFreeComplexHomologyUpperSemicontinuous
import Sheaf.AlgebraicGeometry.ProjectiveNoetherianDirectImagePerfect
import Sheaf.AlgebraicGeometry.ProjectiveNoetherianPerfectBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.RfPerfect
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover

/-! # Constructible geometric fibre dimensions of coherent cohomology

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
lem-fin-projective-flat-coherent-ranks; Stacks Project, Tags 0BDN and 0BDI
(blueprint: lem-fin-projective-flat-coherent-ranks).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Geometric fibre coherent cohomology dimensions of a coherent module flat over a
Noetherian base of a projective morphism form a constructible function: its range is finite
and every level set is constructible. The scalar action is restricted from global functions
on the geometric fibre along its structure morphism to the algebraic closure.
Source: blueprint lem-fin-projective-flat-coherent-ranks; Stacks, Tags 0BDN and 0BDI
(blueprint: lem-fin-projective-flat-coherent-ranks).

Proof:
1. A locally Noetherian quasi-compact scheme has a Noetherian underlying space: choose
finitely many Noetherian affine charts and use lem-sc-affine-noetherian-underlying-space.
Every open is retrocompact, so finite unions of locally closed sets are constructible.
2. By lem-pc-projective-noetherian-rf-perfect the direct image is perfect. Use
 def-pc-perfect-complex and lem-weil-pbc-finite-projective-standard-free-cover to represent
it on a finite affine cover by bounded finite free complexes.
3. By cor-pc-projective-noetherian-rf-perfect-base-change, geometric fibre cohomology is
computed by the derived fibre of this model. Use lem-pc-localized-pullback-perfect-model
and def-pc-module-pullback to identify this with termwise tensoring with the algebraic
closure. Global sections on the spectrum of a field are exact; pqf-def-cohomology
identifies the resulting homology with coherent cohomology. Splitting cycles and boundaries
over the residue field shows that extending to its algebraic closure preserves dimension.
4. Apply lem-sc-finite-free-complex-homology-upper-semicontinuous on each chart. A level
set is the difference of two open sublevel sets, hence locally closed. Its dimension is
bounded by the finite rank of the term in degree r.
5. Take the finite union over the affine cover: each global level set is constructible
and only finitely many values occur. For an empty base the range is empty. -/
theorem projectiveFlatCoherent_geometricCohomology_constructible
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProjective f]
    [IsLocallyNoetherian S] [CompactSpace S]
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hflat : G.IsFlatOver f) (r : ℕ) :
    ∃ β : S → ℕ,
      (∀ s : S, β s = Module.finrank (AlgebraicClosure (S.residueField s))
        ((RingedSpace.moduleCohomology
          (pullback f
            (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
                S.fromSpecResidueField s)).toRingedSpace r ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (S.residueField s)))).inv ≫
              (pullback.snd f
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
                    S.fromSpecResidueField s)).appTop).hom).obj
          ((Scheme.Modules.tensorPullback
            (pullback.fst f
              (Spec.map (CommRingCat.ofHom
                (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
                  S.fromSpecResidueField s))).obj G))) ∧
      (Set.range β).Finite ∧
      ∀ n : ℕ, Topology.IsConstructible {s : S | β s = n} := by
  sorry

end AlgebraicGeometry
