/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
import Sheaf.AlgebraicGeometry.AmpleFibreSectionLifting
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace

/-! # Lifted coordinates for an embedding of an ample proper fibre

Source: Stacks Project, Cohomology of Schemes, Tag 0D2N, first paragraph of
lemma-ample-in-neighbourhood, using Tag 0D2M.
(blueprint: lem-trf-fibre-embedding-lifted-coordinates).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A positive power of a fibre-ample line bundle has embedding coordinates that all lift
on one affine neighbourhood. Their fibre values use the fixed recursive tensor-power
comparison. The twist isomorphism carries each pulled-back coordinate to that fibre value.

Source: Stacks Project, Cohomology of Schemes, Tag 0D2N, first paragraph of
lemma-ample-in-neighbourhood, using Tag 0D2M; Morphisms Tags 01VT and 01W6;
Constructions Tags 01NE and 01NF.
(blueprint: lem-trf-fibre-embedding-lifted-coordinates).

Proof, following the five steps of the node:
1. Apply lem-trf-ample-fibre-section-lifting and let a be its bound. Proper base change
(lem-pc-proper-base-change) makes the fibre proper, hence of finite type. Its pulled-back
line bundle is invertible by lem-weil-pbc-invertible-pullback-tensor. Apply
lem-trf-affine-eventual-power-immersion over the residue field and let b >= 1 be its bound.
Choose d = max a b and an immersion with its twist isomorphism.
2. Projective space is separated by lem-weil-pbc-projective-space-proj-separated.
Then lem-weil-pbc-proper-to-separated makes the immersion proper, and
lem-weil-pbc-proper-immersion-closed makes it a closed immersion.
3. Transport the homogeneous coordinates through its twist isomorphism. In each standard
chart the corresponding coordinate is a basis, so these sections generate. The comparison
lem-trf-free-projective-bundle-base-change-space fixes the coordinates and their standard
frames. The uniqueness in lem-weil-pbc-projective-space-functor-of-points identifies the
resulting map with homOfGeneratingSections of the transported sections. The same twist
isomorphism is compatible with every coordinate and hence with the quotient.
4. Lift each of these finitely many sections using the same exponent d and the lifting
lemma. Its normalized section map and the recursion of boundaryPullbackPowIso give
exactly the prescribed comparison p_j(L,d), with no rescaling of any coordinate.
5. Intersect the finitely many base neighbourhoods and choose an affine neighbourhood
inside their intersection by lem-weil-pbc-affine-opens-basis. Restrict all the lifts to it.
Restriction commutes with the normalized section pullback, so all fibre values persist.
No generation on the complement of the fibre is required. -/
theorem exists_fiber_embedding_lifted_coordinates {Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsProper f] [IsLocallyNoetherian S] [CompactSpace S]
    (L : Z.Modules) [L.IsInvertible] (s : S) [Nonempty (f.fiber s)]
    (hL : @IsAmple (f.fiber s) ((tensorPullback (f.fiberι s)).obj L)
      ((invertible_pullback_tensor (f.fiberι s)).1 L).2) :
    ∃ d r : ℕ, 0 < d ∧ ∃ U : S.Opens, IsAffineOpen U ∧ ∃ hs : s ∈ U,
      ∃ (u : ULift.{u} (Fin (r + 1)) → Γ(L.tensorPow d, f ⁻¹ᵁ U))
        (t : ULift.{u} (Fin (r + 1)) →
          (((tensorPullback (f.fiberι s)).obj L).tensorPow d).sections),
        (∀ k : ULift.{u} (Fin (r + 1)),
          (boundaryPullbackPowIso (f.fiberι s) L d).hom.app ⊤
            (((tensorPullback (f.fiberι s)).obj (L.tensorPow d)).val.map
              (homOfLE (fun x _ ↦ Eq.mpr
                (congrArg (fun y : S ↦ y ∈ U) (f.fiberHomeo s x).property) hs)).op
              (tensorPullbackSection (f.fiberι s) (L.tensorPow d) (f ⁻¹ᵁ U) (u k))) =
            (t k).val (op ⊤)) ∧
        ∃ ht : Epi ((((tensorPullback (f.fiberι s)).obj L).tensorPow d).freeHomEquiv.symm t),
          ∃ i : f.fiber s ⟶ ProjectiveSpace (ULift.{u} (Fin (r + 1)))
              (Spec (S.residueField s)),
            i = @ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin (r + 1)))
              inferInstance (f.fiber s) (Spec (S.residueField s))
              (f.fiberToSpecResidueField s) (((tensorPullback (f.fiberι s)).obj L).tensorPow d)
              (@IsInvertible.tensorPow (f.fiber s) ((tensorPullback (f.fiberι s)).obj L)
                ((invertible_pullback_tensor (f.fiberι s)).1 L).2 d) t ht ∧
            IsClosedImmersion i ∧
            ∃ e : (tensorPullback i).obj
                (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) (Spec (S.residueField s)) 1) ≅
                  ((tensorPullback (f.fiberι s)).obj L).tensorPow d,
              ∀ k : ULift.{u} (Fin (r + 1)), e.hom.app ⊤
                (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                  (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1)))
                    (Spec (S.residueField s)) 1)).val.app (op ⊤)
                      (ProjectiveSpace.twistOneSection (ULift.{u} (Fin (r + 1)))
                        (Spec (S.residueField s)) k)) = (t k).val (op ⊤) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
