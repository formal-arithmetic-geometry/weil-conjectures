module

public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Algebra coactions over a commutative base ring

Source: Alper, Adequate moduli spaces, Lemma 9.2.5, pp.522--523.
(blueprint: def-sfb-ring-algebra-coaction)

The coordinate Hopf algebra is the canonical one of the given affine group scheme.
The existing HopfAction.AlgebraCoaction only accepts a field as its base.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace RingHopfAction

/-- A right algebra coaction over an arbitrary commutative ring.
Source: Alper, Lemma 9.2.5, affine action convention.
(blueprint: def-sfb-ring-algebra-coaction) -/
structure AlgebraCoaction (R : Type u) [CommRing R] (C : Type v) [CommRing C]
    [HopfAlgebra R C] (E : Type w) [CommRing E] [Algebra R E] where
  /-- The algebra map dual to the action. -/
  map : E →ₐ[R] E ⊗[R] C
  /-- The identity section acts as the identity. -/
  counit : (TensorProduct.rid R E).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := C)).lTensor E ∘ₗ map.toLinearMap = LinearMap.id
  /-- The multiplication diagram, in right-coaction convention. -/
  coassoc : (TensorProduct.assoc R E C C).toLinearMap ∘ₗ
    map.toLinearMap.rTensor C ∘ₗ map.toLinearMap =
      (Coalgebra.comul (R := R) (A := C)).lTensor E ∘ₗ map.toLinearMap

end RingHopfAction

namespace AlgebraicGeometry.AffineGroupAction

/-- Affineness of scalar extension, exposing the canonical pullback projection.
Source: Alper, Proposition 9.3.1(i); Mathlib stability under base change.
(blueprint: def-sfb-ring-algebra-coaction) -/
instance baseChange_isAffineHom (R S : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    [IsAffineHom G.X.hom] (f : Spec S ⟶ Spec R) :
    IsAffineHom (((Over.pullback f).mapGrp).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom f))

/-- Expose the existing canonical coordinate Hopf structure for a bundled group.
Source: Alper, Lemma 9.2.5; def-sfb-affine-coordinate-hopf-algebra.
(blueprint: def-sfb-ring-algebra-coaction) -/
instance coordinateHopf (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    [IsAffineHom G.X.hom] : HopfAlgebra R Γ(G.X.left, ⊤) :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  @HopfAction.affineCoordinateHopfAlgebra R G.X.left
    (OverClass.fromOver G.X) (inferInstanceAs (GrpObj G.X)) inferInstance

/-- Algebra coactions of the actual coordinate Hopf algebra of an affine group scheme.
Source: Alper, Lemma 9.2.5; Mathlib Group/Affine.
(blueprint: def-sfb-ring-algebra-coaction) -/
abbrev Coaction (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    [IsAffineHom G.X.hom] (E : Type w) [CommRing E] [Algebra R E] :=
  RingHopfAction.AlgebraCoaction R Γ(G.X.left, ⊤) E

end AlgebraicGeometry.AffineGroupAction
