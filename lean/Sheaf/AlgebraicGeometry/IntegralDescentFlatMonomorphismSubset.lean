/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Topology.Sheaves.Functors
import Sheaf.AlgebraicGeometry.RingedSubspace
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget

/-! # Integral descent of a subset represented by a quasi-compact flat monomorphism

Source: Raynaud, Un critère d'effectivité de descente, §3, Theorem 3.3(ii)
(heading 3.4 in the scan), printed pp.12–13, and §1, Proposition 1.2 and Corollary 1.3.
(blueprint: lem-sfb-integral-descent-flat-monomorphism-subset)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A subset whose inverse image under an integral surjection is represented by a
quasi-compact flat monomorphism has such a representative over a locally Noetherian target.
The representative pulls back to the given one, with both projection compatibilities.
Source: Raynaud, §3, Theorem 3.3(ii) (scan heading 3.4), pp.12–13;
§1, Proposition 1.2 and Corollary 1.3.
(blueprint: lem-sfb-integral-descent-flat-monomorphism-subset).

Proof (the eight DAG steps):
1. Put H' = q⁻¹(H). By lem-sfb-qc-flat-monomorphism-ringed-image it is generalization
   stable. For a generalization z of h in H, choose y over z. Integral closedness
   (pqf-lem-integral-univclosed) gives a specialization of y over h, so y lies in H'.
   Thus H is generalization stable. Above an affine open D of Z the integral cover is
   affine, so the inverse image in F' is quasi-compact and its image H ∩ D is compact.
   Finite affine covers of quasi-compact opens give retrocompactness of H.
2. Identify F' with the induced ringed subspace Y|H'. The affine-neighbourhood lemma
   lem-sfb-qc-flat-monomorphism-affine-neighbourhood supplies an open U' containing H'
   over which j' is affine. The closed set q(Y ∖ U') misses H. Shrink Z to its complement
   W. For each affine open D of W, both Y_D and F'_D are affine, using integral
   affineness and lem-weil-pbc-affine-morphism-permanence.
3. Form E_D = D|(H ∩ D), using def-a1-ringed-subspace, and its canonical affine
   envelope E_D → V → D from lem-sfb-generalizing-subset-affine-envelope. Its boundary
   image B misses H. If B is nonempty, lem-sfb-subset-maximal-generalization supplies a
   point b with no strict generalization in B, since the affine D is Noetherian.
4. Localize at b using lem-weil-pbc-spec-local-ring-canonical-morphism. The envelope
   localizes, and its boundary image becomes the closed singleton over b, disjoint
   from the inverse image of H. The envelope boundary criterion makes E_T a scheme
   with a quasi-compact flat monomorphism to T = Spec O_(D,b).
5. Base change Y_D and F'_D to T, obtaining Y_T and P. Integral and surjective base
   change (lem-sbc-integral-morphism-base-change, lem-weil-pbc-surjective-base-change)
   make Y_T affine. Affine permanence makes P affine. Quasi-compactness, flatness,
   and monicity persist under base change (lem-pc-quasi-compact-base-change,
   lem-weil-pbc-flat-morphism-base-change, def-pc-fibre-product). The image of P in
   Y_T is the inverse image of H_T. The unique-factorization criterion for ringed
   images identifies P with Y_T ×_T E_T.
6. Hence P → E_T is integral and surjective. Since P is affine,
   lem-weil-pbc-surjective-universally-closed-affine-target makes E_T affine. The
   envelope criterion makes E_T → V_T an isomorphism, contradicting its nonempty
   boundary. Thus B is empty and each E_D is an affine scheme.
7. The induced ringed subspace Z|H is a scheme by these affine charts, which share
   the same restricted structure sheaf. Its inclusion j has isomorphic local rings,
   hence is flat (def-weil-flat-morphism). It is monic by the inverse-image
   adjunction (def-weil-pbc-topological-inverse-image), has image H, and is
   quasi-compact by the compact intersections in step 1. No global compactness is used.
8. For every test scheme L, a map to Y lifts uniquely to F' exactly when its image
   lies in q⁻¹(H), exactly when its composite to Z lifts uniquely to F. This gives p
   and the pullback universal property (def-pc-fibre-product), hence the compatible
   isomorphism. Flatness of q, finite fibres, and Noetherianity of Y are never used.
-/
theorem integral_descent_flat_monomorphism_subset
    {Z Y F' : Scheme.{u}} [IsLocallyNoetherian Z]
    (q : Y ⟶ Z) [IsIntegralHom q] [Surjective q] (H : Set Z)
    (j' : F' ⟶ Y) [QuasiCompact j'] [Flat j'] [Mono j']
    (himage : Set.range j' = q ⁻¹' H) :
    ∃ (F : Scheme.{u}) (j : F ⟶ Z),
      QuasiCompact j ∧ Flat j ∧ Mono j ∧ Set.range j = H ∧
      ∃ (p : F' ⟶ F), IsPullback j' p q j ∧
        ∃ (e : F' ≅ pullback q j),
          e.hom ≫ pullback.fst q j = j' ∧ e.hom ≫ pullback.snd q j = p := by
  sorry

end AlgebraicGeometry
