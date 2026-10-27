module

public import Sheaf.AlgebraicGeometry.AlgebraicPicardSubgroup
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Picard.Degree
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-! # Algebraically trivial lines on an affine product

Source: the auxiliary Picard argument extracted from Guo, Proposition 5.2,
Claim 5.2.1, printed pp. 12-13, in the historical alteration/Picard branch of
`det-thm-sf-ctf-stability-direct-images`, proof (3).
(blueprint: lem-sfb-affine-product-algebraic-equivalence)

The Picard group uses multiplication for tensor product, so the sum of the two
pullback subgroups is their supremum. The final clause is on actual invertible modules
and uses the tensor-pullback construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- On a smooth geometrically integral affine finite-type product, the subgroup of
algebraically trivial line classes is the sum of the pullback subgroups from the factors.
Every line in this subgroup is an external tensor product of algebraically trivial lines.
Source: Guo, Proposition 5.2, proof of Claim 5.2.1, pp. 12-13, auxiliary Picard argument;
Milne, Abelian Varieties, I Theorem 3.4, Theorem 5.16 and Corollary 5.18.
(blueprint: lem-sfb-affine-product-algebraic-equivalence)

Proof:
1. Put T = X times Y. Smooth base change and composition, geometric irreducibility of
   products and geometric reducedness of smooth schemes make T smooth geometrically
   integral. Affineness gives separatedness; finite type is stable under products.
   Density of rational points supplies x0 and y0. It suffices to treat the family
   differences generating the algebraically trivial subgroup. These are the tools
   lem-pc-proper-base-change, lem-trf-smooth-composition,
   lem-sc-geometrically-irreducible-product, lem-trf-smooth-geometrically-normal,
   lem-sfb-finite-type-composition-base-change, lem-pc-rational-points-dense and
   lem-weil-pbc-affine-source-morphism-separated.
2. By lem-sfb-line-family-projective-curve-interpolation, replace a generator by the
   difference of fibres E_b and E_a of a line E on T times a smooth projective
   geometrically integral curve C, at rational points a and b.
3. Restrict E to both axes and their intersection, obtaining E_X, E_Y and E_0.
   Normalize E by tensoring with the inverse pullbacks of E_X and E_Y and the pullback
   of E_0. The resulting line H is trivial on both axes times C, by tensor-pullback
   functoriality and lem-weil-pbc-invertible-pullback-tensor.
4. Viewed as a family on C over connected T, H has degree zero by
   lem-pd-degree-locally-constant. The Picard functor and
   thm-sc-jacobian-representability give a morphism T to the Jacobian of C.
   Its restrictions to both axes vanish; lem-sfb-abelian-product-axis-rigidity makes
   it zero. Thus each rational T-fibre is the trivial line on C.
5. Apply lem-sfb-rigidified-product-seesaw to get H pulled back from H_a on T.
   Hence H_b and H_a have the same Picard class. Expanding the normalization expresses
   the original generator as the sum of the differences from X and Y. The fibres of
   E_0 are lines over k and contribute trivial classes. C is an allowed parameter
   for both factor differences. This proves the difficult inclusion.
6. For the reverse inclusion pull every defining family on a factor back to T; its
   fibres are the pulled-back fibres. Subgroup generation proves the inclusion.
   Finally express a class in the sum as the product of two pulled-back factor classes.
   Equality in Pic means isomorphism of invertible modules, giving the asserted
   external tensor product with both factor classes algebraically trivial.
-/
theorem algebraicPicardSubgroup_affine_product
    {k : Type u} [Field k] [IsAlgClosed k]
    (X Y : Over (Spec (.of k)))
    [Smooth X.hom] [GeometricallyIntegral X.hom] [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [Smooth Y.hom] [GeometricallyIntegral Y.hom] [IsAffine Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    algebraicPicardSubgroup (X ⊗ Y) =
      (algebraicPicardSubgroup X).map (Pic.mapHom (fst X Y).left) ⊔
      (algebraicPicardSubgroup Y).map (Pic.mapHom (snd X Y).left) ∧
    ∀ (N : (X ⊗ Y).left.Modules) [Modules.IsInvertible N],
      Pic.ofIsInvertible N ∈ algebraicPicardSubgroup (X ⊗ Y) →
      ∃ (A : X.left.Modules) (B : Y.left.Modules)
        (hA : Modules.IsInvertible A) (hB : Modules.IsInvertible B),
        @Pic.ofIsInvertible X.left A hA ∈ algebraicPicardSubgroup X ∧
        @Pic.ofIsInvertible Y.left B hB ∈ algebraicPicardSubgroup Y ∧
        Nonempty (N ≅ (Modules.tensorPullback (fst X Y).left).obj A ⊗
          (Modules.tensorPullback (snd X Y).left).obj B) := by
  sorry

end AlgebraicGeometry.Scheme
