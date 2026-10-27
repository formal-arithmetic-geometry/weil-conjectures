module

public import Sheaf.AlgebraicGeometry.GroupScheme.RingAlgebraCoaction
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded

/-! # Universal invariant power lifting for reductive group schemes

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Theorem 9.7.5, Proposition 9.3.1(i), Lemma 9.2.5, pp.522--528.
(blueprint: lem-sfb-reductive-ring-invariant-power-lifting)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Reductive geometric fibres give power lifting of invariants after arbitrary base change.
Source: Alper, Theorem 9.7.5, Proposition 9.3.1(i), Lemma 9.2.5(2),(3), pp.522--528.
(blueprint: lem-sfb-reductive-ring-invariant-power-lifting)

Proof:
1. Over a DVR with algebraically closed residue field, apply
   lem-sfb-dvr-primitive-endomorphism-detector to a primitive fixed vector v in a finite
   free module V for a split semisimple simply connected group H. The invariant image
   is c id_W. Its nonzero reduction implies c is outside the maximal ideal, hence a unit;
   rescale the equivariant detector so that it sends v to id_W.
2. For d = rank W > 0, determinant composed with the detector is a homogeneous polynomial
   of degree d on V. Cauchy--Binet (lem-weil-pbc-cauchy-binet) proves invariance under
   conjugation on every algebra, including the universal point, hence coaction invariance.
   The polynomial takes value 1 at v.
3. Smoothness implies flatness by sbc-lem-smooth-criterion. Apply
   lem-sfb-dvr-primitive-polynomial-lifting-criterion and then
   lem-sfb-reductive-symmetric-power-dvr-reduction. Thus every equivariant module
   surjection onto R lifts 1 in a positive symmetric degree, for arbitrary source module.
4. Fix R', E, F, u and b. The affine fibre-product tensor identification
   (lem-weil-pbc-fibre-product-affine-spectra) identifies C' with R' tensor_R C, and
   E tensor_R' C' with E tensor_R C by e tensor (r tensor c) mapped to re tensor c.
   This transfers the coactions, equivariance and invariants. Regard E and F as rational
   G-modules. C is R-flat by smoothness and lem-weil-pbc-flat-morphism-affine-criterion.
   The pullback module M = {(e,r) | u(e) = rb} is the kernel of the equivariant map
   E directSum R -> F given by (e,r) mapped to u(e)-rb. Flat tensor exactness
   (lem-weil-pbc-flat-tensor-exact) restricts the coaction to M and verifies both laws.
   Projection M -> R is equivariant and surjective: if u(e0)=b, then (re0,r) lifts r.
5. Step 3 gives invariant q in Sym^N M, N >= 1, mapping to 1 in Sym^N R. The projection
   M -> E induces an equivariant algebra map Sym M -> E by the symmetric algebra
   universal property. Put a equal to the image of q. On degree-N products its image
   under u is b^N times the image in Sym^N R. Such products span the degree-N part by
   lem-weil-pbc-symmetric-algebra-graded, so u(a)=b^N. Step 4 identifies invariance
   with the given G'-coaction. Neither finite generation nor flatness of E or F is used.
-/
theorem reductive_ring_invariant_power_lifting
    (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom]
    (hgeom : ∀ (Ω : Type u) [Field Ω] [Algebra R Ω] [IsAlgClosed Ω],
      ReductiveTorusCentralizer.IsReductive
        (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).mapGrp).obj G))
    (R' : CommRingCat.{u}) [Algebra R R']
    (E : Type v) [CommRing E] [Algebra R' E]
    (F : Type w) [CommRing F] [Algebra R' F]
    (ρE : AffineGroupAction.Coaction R'
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).mapGrp).obj G) E)
    (ρF : AffineGroupAction.Coaction R'
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).mapGrp).obj G) F)
    (f : E →ₐ[R'] F) (hf : Function.Surjective f)
    (heq : f.toLinearMap.rTensor
        Γ((((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).mapGrp).obj G).X.left,
          ⊤) ∘ₗ ρE.map.toLinearMap = ρF.map.toLinearMap ∘ₗ f.toLinearMap)
    (b : F) (hb : ρF.map b = b ⊗ₜ[R'] 1) :
    ∃ (N : ℕ) (a : E), 1 ≤ N ∧ ρE.map a = a ⊗ₜ[R'] 1 ∧ f a = b ^ N := by
  sorry

end AlgebraicGeometry
