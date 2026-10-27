/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Sheaf.AlgebraicGeometry.AffineActionStackPresentation
public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic

/-! # Power lifting gives an adequate affine quotient

Source: Alper, arXiv:1005.2398v3, Lemma 9.2.5, Remark 9.2.4(1),
Lemma 9.2.8(3), Theorem 9.1.4 and Remark 9.1.5
(blueprint: lem-sfb-power-lifting-adequate-affine-quotient).

Rational algebra actions are written as scheme actions on their affine spectra.
Their coordinate coactions and equalizer rings are the recorded constructions.
The canonical quotient map is characterized by its composite with the atlas.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.SchemeAction

/-- Power lifting along equivariant surjections of finite-type rational algebras
makes the canonical affine invariant quotient an adequate moduli space. Rational
actions are encoded as scheme actions via affine duality and group inversion.
Equivariance below uses the recorded swapped coordinate maps; inversion changes
neither the invariant equalizers nor the equivariance condition.
The canonical morphism is any representative of the unique vertical-isomorphism
class characterized in `affine_action_stack_invariant_spectrum`.
Source: Alper, arXiv:1005.2398v3, Lemma 9.2.5 (3-prime and 3-double-prime),
Remark 9.2.4(1), Lemma 9.2.8(3), Theorem 9.1.4 and Remark 9.1.5
(blueprint: lem-sfb-power-lifting-adequate-affine-quotient).
Proof:
1. Extend power lifting to arbitrary rational algebras: choose a preimage of an
   invariant element and a finite-dimensional subcomodule containing it, using
   lem-sfb-comodule-finite-subrepresentation. Its generated subalgebra and its image
   are finite type and stable under the coaction. Over a field tensoring their
   inclusions with k[G] is injective, so invariance restricts. Apply the hypothesis.
2. Put R = E^G. By lem-sfb-affine-action-quasicoherent-descent the specified
   quotient map is qcqs, and on every R-algebra L its base change is the quotient
   of Spec(E tensor_R L), with quasi-coherent algebra descent and section formulas.
   The quotient and atlas use def-sfb-affine-action-quotient-stack and
   lem-sfb-affine-action-stack-presentation, with their left-torsor convention.
3. On every affine etale chart Spec L over Spec R, descend an arbitrary surjection
   of quasi-coherent algebras to equivariant algebras over E tensor_R L. Forget to
   rational k-algebras and apply step 1. The invariant-section identification gives
   power lifting, also for algebras which do not descend from the original stack.
4. The sequence 0 → R → E → E tensor_k k[G], whose last map is coaction minus
   inclusion, is exact and R-linear. By lem-weil-pbc-etale-algebra-flat and
   lem-weil-pbc-flat-tensor-exact it remains exact after tensoring with L. The last
   map becomes coaction minus inclusion on E tensor_R L, so its invariant ring is
   canonically L. Descent identifies this with the structural sheaf map on every
   affine etale chart, naturally in the chart. Thus that sheaf map is an isomorphism.
5. Steps 2--4 are precisely qcqs and the two conditions of
   def-sfb-adequate-moduli-space. -/
theorem power_lifting_adequate_affine_quotient
    (k : Type u) [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [Smooth G.hom] [IsAffineHom G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hpower : ∀ (B C : Type u) [CommRing B] [CommRing C]
      [Algebra k B] [Algebra k C] [Algebra.FiniteType k B] [Algebra.FiniteType k C]
      [ModObj G (affineActionScheme k B)] [ModObj G (affineActionScheme k C)]
      (f : B →ₐ[k] C), Function.Surjective f →
      (∀ b : B,
        Algebra.TensorProduct.map f (AlgHom.id k (affineGroupCoordinates k G))
            (affineTensorCoaction k B G b) = affineTensorCoaction k C G (f b)) →
      ∀ c : affineInvariants k C G,
        ∃ N : ℕ, 0 < N ∧ ∃ b : affineInvariants k B G, f b = (c : C) ^ N)
    (E : Type u) [CommRing E] [Algebra k E] [Algebra.FiniteType k E]
    [ModObj G (affineActionScheme k E)]
    (φ : BasedFunctor (affineActionQuotientStack k E G)
      (discreteModuli (yoneda.obj (affineInvariantSpectrum k E G))))
    (hφ : Nonempty (ModuliTwoIso ((quotientAtlas G (affineActionScheme k E)).comp φ)
      (discreteModuliMap (yoneda.map (affineInvariantProjection k E G))))) :
    IsAdequateModuliSpace (affineActionQuotientStack k E G)
      (affine_action_stack_presentation k E G).1
      (AlgebraicSpace.schemeSpace (affineInvariantSpectrum k E G)) φ := by
  sorry

end AlgebraicGeometry.SchemeAction
