module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.RingTheory.LocalDomainDimOnePrincipalLocalization

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry

/-- The affine-local function-field square is a pullback of the diagonal, without
assuming separatedness.
Source: Stacks Project, Varieties Lemma 09NB, first paragraph of the proof
(blueprint: lem-sc-affine-local-function-field-diagonal-pullback).
Proof: Put A = Γ(X,U), B = O_{X,x}, and K = k(X). The canonical map Spec B → X
identifies its points with the generalizations of x and their local rings with the
corresponding stalks of X. A one-dimensional local domain B has just the zero prime
and its maximal ideal: a nonzero prime strictly below the maximal ideal would give
a chain of length two. Since x is outside U and the generic point is in every
nonempty open, the inverse image of U is precisely the zero prime. Choose a nonzero
element t of the maximal ideal (B cannot be a field since its dimension is one).
This inverse image is D(t). Its coordinate ring B[1/t] is K: it is a domain with
only the zero prime, hence a field, and its canonical inclusion into the fraction
field K is an isomorphism. Thus Spec K, with the germ and stalk-specialization
maps, is the fibre product Spec A ×_X Spec B. The product Spec A × Spec B is
Spec (A ⊗[ℤ] B), since this tensor product is the coproduct of commutative rings.
Under this identification the map from Spec K is the spectrum of the tensor lift:
its compositions with the two projections are the germ map and the stalk map.
Finally the square from any fibre product Y ×_X Z to Y × Z and the diagonal
X → X × X is cartesian, by the universal properties of products and pullbacks.
These identifications give exactly the displayed square. No separatedness is
used in this calculation; it is the separate closedness step in the parent proof. -/
theorem Scheme.isPullback_affine_local_functionField_diagonal
    (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (x : X) (hx : x ∉ U)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    let A : Type u := Γ(X, U)
    let B : Type u := X.presheaf.stalk x
    let K : Type u := X.functionField
    let φ : TensorProduct ℤ A B →ₐ[ℤ] K :=
      Algebra.TensorProduct.lift
        (X.germToFunctionField U).hom.toIntAlgHom
        (algebraMap B K).toIntAlgHom
        (fun _ _ => Commute.all _ _)
    IsPullback (X.fromSpecStalk (genericPoint X))
      (Spec.map (CommRingCat.ofHom φ.toRingHom))
      (prod.lift (𝟙 X) (𝟙 X))
      (prod.lift
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct ℤ A B)) ≫
          hU.fromSpec)
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : B →+* TensorProduct ℤ A B)) ≫
          X.fromSpecStalk x)) := by
  sorry

end AlgebraicGeometry
