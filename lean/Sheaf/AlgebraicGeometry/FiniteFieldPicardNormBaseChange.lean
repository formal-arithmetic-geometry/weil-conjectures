/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.FieldTheory.FieldTower
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Sheaf.AlgebraicGeometry.FiniteTrivializeInvertibleUpstairs
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Picard norm for a finite field extension

Source: Stacks Project, Divisors, Tags 0BCY, 0BD2 and 0BUT
(blueprint: lem-sfb-finite-field-picard-norm-base-change).

The norm is a simultaneous family on all schemes over the base field. Its
multiplicativity and preservation of the structure sheaf are encoded by `→*`.
The existing `Scheme.Pic.map` is inverse image on isomorphism classes; ordinary
module pullback and tensor inverse image are isomorphic by uniqueness of left
adjoints, so they induce the same map on these classes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Pic

/-- Picard norms for finite field extensions preserve tensor products and the
structure sheaf, send a pulled-back line to its degree power, and commute with
pullback along every morphism of schemes over the base field.

Source: Stacks Project, Divisors, Tags 0BCY, 0BD2 and 0BUT
(blueprint: lem-sfb-finite-field-picard-norm-base-change).

Proof:
1. Fix a k-basis of K, of size d = [K:k]. On an affine open Spec R of Z,
   the projection has coordinate algebra R tensor_k K, free with basis 1 tensor b_a
   (lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-open-fibre-product).
   Thus the projection is finite. The coordinates commute with restriction and
   glue on arbitrary opens; no affine-intersection hypothesis is used.
2. Take the determinant of multiplication in that basis on every open. Restriction
   compatibility, multiplicativity and the identities norm(1) = 1 and norm(a) = a^d
   follow from the determinant expansion and determinant multiplication
   (def-weil-pbc-matrix-determinant, lem-sfb-matrix-cramer-determinant-identities).
3. A line upstairs has frames on inverse images of an open cover downstairs by
   lem-sfb-finite-trivialize-invertible-upstairs. Apply the multiplicative norm to
   its transition units, then glue a line with those transitions by
   lem-sfb-norm-frame-tensor-section-gluing.
4. A frame change e'_i = a_i e_i changes the norm transitions by the coboundary
   norm(a_i). The resulting local isomorphisms and their inverses glue by
   lem-weil-pbc-glue-sheaves-of-modules. Common refinements compare covers;
   transporting frames through an isomorphism proves dependence only on the class.
5. Tensor-product frames have product transitions. Their norms are products, so
   the glued norm preserves tensor products. The global frame 1 gives the unit.
   Use lem-weil-pbc-invertible-pullback-tensor and the symmetric monoidal module
   tensor of lem-weil-pbc-module-tensor-symmetric-monoidal for these frame maps.
6. For a line A downstairs with transitions alpha_ij, the pulled-back transitions
   have norm alpha_ij^d. They are precisely the transitions of A tensor-powered d
   times (lem-sfb-norm-frame-tensor-section-gluing). Matching frames and gluing
   gives the degree formula on Picard classes.
7. For h : W -> Z, multiplication matrices in the same fixed k-basis are carried
   entrywise by h on every affine chart. The determinant polynomial commutes with
   any ring map, including nonflat maps; the sheaf axiom gives the identity on
   all opens (def-weil-pbc-matrix-determinant).
8. Pull back the chosen upstairs frames along h_K. Their norm transitions equal
   the pullbacks of the norm transitions by step 7. Glue the matching frame
   isomorphisms by lem-weil-pbc-glue-sheaves-of-modules. This gives the base-change
   equation. Empty schemes, degree one, nilpotents and inseparability cause no
   exception to these calculations. -/
theorem exists_finiteFieldNorm_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K] :
    ∃ Nm : ∀ Z : Over (Spec (CommRingCat.of k)),
      (pullback Z.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Pic →*
        Z.left.Pic,
      (∀ (Z : Over (Spec (CommRingCat.of k))) (A : Z.left.Pic),
        Nm Z (map (pullback.fst Z.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) A) =
            A ^ Module.finrank k K) ∧
      (∀ (W Z : Over (Spec (CommRingCat.of k))) (h : W ⟶ Z)
          (F : (pullback Z.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Pic),
        map h.left (Nm Z F) =
          Nm W (map (((Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map h).left) F)) := by
  sorry

end AlgebraicGeometry.Scheme.Pic
