/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Étale locality and the affine criterion for adequate moduli spaces

Source: Alper, arXiv:1005.2398v3, Lemma 4.1.8(3), Definition 5.1.1,
Propositions 4.2.1(3),(4) and 5.2.9(1),(2)
(blueprint: lem-sfb-adequate-moduli-etale-locality).

The two statements use actual fibred-groupoid base changes and arbitrary
quasi-coherent algebra sheaves. In the affine criterion, the canonical map on
functions is specified by its pullback on every object, using the existing
structure presheaf's universe transport. Unique scalar preimages express that
this canonical ring map is an isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- Adequacy can be tested on any jointly surjective chartwise étale family of
algebraic spaces. The algebraicity witness is existentially bound on the right,
so no additional hypothesis on a base-changed stack is required. The order of
factors is chosen so that the existing first projection is the map to the new base.
Source: Alper, arXiv:1005.2398v3, Propositions 5.2.9(1),(2) and 4.2.1(3),(4)
(blueprint: lem-sfb-adequate-moduli-etale-locality).

Proof: use DAG steps 2--6. Algebraic-stack fibre products and étale-local qcqs
permanence give the algebraicity and qcqs conditions. In the forward direction,
chartwise étale permanence identifies every affine étale test with a test of the
original map, including all algebras on that test stack. The structure maps agree
by the direct-image formula. In the reverse direction, their unique local inverses
glue by the sheaf axiom. For each arbitrary algebra surjection on an affine test,
refine the induced cover by finitely many affine étale schemes, using
lem-weil-pbc-etale-covering-sieve-finite-affine-refinement. Their coproduct is the
spectrum of the product ring, by lem-weil-pbc-finite-affine-coproduct-spectrum.
Étale flatness, finite-product flatness and surjective spectra give faithful
flatness. Choose a common positive multiple of the local power exponents and
combine the lifts over this disjoint union. Flat scalar sections identify the
base-changed map with tensor extension of the original map. Tensor right
exactness and faithful-flat universal injectivity kill the class of the power
in its cokernel already before base change. For the empty test use exponent one
and the zero section. The structural isomorphism and these tests give adequacy.
The algebras used here need not descend from the original stack. -/
theorem adequateModuliSpace_iff_etale_family
    {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (Y : AlgebraicSpace (Spec (CommRingCat.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} φ)
    (hqs : IsQuasiSeparatedAlgebraicModuliMap φ)
    (I : Type z) (Yᵢ : I → AlgebraicSpace (Spec (CommRingCat.of k)))
    (p : ∀ i : I, Yᵢ i ⟶ Y)
    (hp : ∀ i : I, IsChartwiseEtale (p i))
    (hsurj : IsJointlySurjective (fun i : I ↦ (p i).hom.hom)) :
    IsAdequateModuliSpace F hF Y φ ↔
      ∀ i : I,
        ∃ hFi : IsAlgebraicModuliStack
            (moduliTwoFiberProduct (discreteModuliMap (p i).hom.hom) φ),
          IsAdequateModuliSpace
            (moduliTwoFiberProduct (discreteModuliMap (p i).hom.hom) φ) hFi (Yᵢ i)
            (moduliTwoFiberFst (discreteModuliMap (p i).hom.hom) φ) := by
  sorry

/-- Over an affine target, adequacy is equivalent to the canonical isomorphism on
functions and global power lifting for every quasi-coherent algebra surjection.
The first conjunct says that every global function has a unique scalar preimage
under pullback along the given morphism; this is bijectivity of the canonical
ring homomorphism, expressed on the compatible families defining global sections.
Source: Alper, arXiv:1005.2398v3, Lemma 4.1.8(3) and Definition 5.1.1
(blueprint: lem-sfb-adequate-moduli-etale-locality).

Proof: use DAG step 1. Adequacy evaluated on the identity affine étale test gives
both global conditions. Conversely, for any affine étale Spec D over Spec C,
the base-changed stack is algebraic. Its projection is affine, by
lem-sfb-stack-affine-algebra-direct-image, so direct image preserves arbitrary
quasi-coherent algebra surjections and identifies global section rings, naturally
with their algebra maps and powers. Apply global power lifting to that direct
image to obtain the required lift on the test stack. Étale flatness and
lem-sfb-stack-flat-scalar-sections identify the structural map on Spec D with
the tensor extension of the given canonical isomorphism on functions; its unit
formula identifies this with the required canonical map. On arbitrary étale
schemes, cover by affine opens and glue the unique inverses of that map.
These two conditions are exactly def-sfb-adequate-moduli-space. No algebra in
this argument is assumed finitely generated. -/
theorem adequateModuliSpace_iff_affine_global_power
    {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (C : Type u) [CommRing C] (c : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of k))
    (φ : BasedFunctor F (discreteModuli (yoneda.obj (Over.mk c))))
    (hqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} φ)
    (hqs : IsQuasiSeparatedAlgebraicModuliMap φ) :
    IsAdequateModuliSpace F hF (schemeSpace (Over.mk c)) φ ↔
      (∀ t : moduliGlobalSectionsRing (moduliStructureSheaf F hF.1.1),
        ∃! r : C, ∀ x : F.obj,
          t.1 (op x) = ULift.up ((Scheme.Γ.map
            (eqToHom (congrArg (fun T : Over (Spec (CommRingCat.of k)) ↦ T.left)
                (φ.w_obj x)).symm ≫
              (yoneda.preimage (φ.obj x).hom).left).op)
            ((Scheme.ΓSpecIso (CommRingCat.of C)).inv r))) ∧
      ∀ (A B : ModuliAlgebraSheaf F hF.1.1),
        IsQuasicoherentModuliAlgebra A → IsQuasicoherentModuliAlgebra B →
        ∀ (f : A ⟶ B), IsSurjectiveModuliAlgebra f →
          ∀ b : moduliGlobalSectionsRing B.right,
            ∃ n : ℕ, 0 < n ∧ ∃ a : moduliGlobalSectionsRing A.right,
              ∀ x : F.objᵒᵖ, (f.right.hom.app x) (a.1 x) = (b.1 x) ^ n := by
  sorry

end CategoryTheory
