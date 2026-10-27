module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Sheaf.FieldTheory.UniqueSubfieldOfClosure

/-! # Rational points on connected-group torsors over finite fields

Source: Milne, Algebraic Groups (2017), Corollary 17.98, printed p.383;
Definition 2.66 and Proposition 2.69, p.60; Proposition 3.50, p.80
(blueprint: lem-sfb-finite-field-connected-group-torsor-point).

The Cartesian tensor product in `Over (Spec (.of k))` is the chosen scheme fibre
product. Its unit is `Spec k` with its identity structure map. Thus the final
Hom set consists of rational points, and the torsor map is `(y,h) ↦ (y,yh)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- A torsor under a smooth geometrically connected affine finite-type group over a
finite field has a rational point.

Source: Milne, Algebraic Groups (2017), Corollary 17.98 and proof, printed p.383,
with Definition 2.66 and Proposition 2.69, p.60, and Proposition 3.50, p.80
(blueprint: lem-sfb-finite-field-connected-group-torsor-point).

Proof plan:
1. Choose an algebraic closure K of k. Surjectivity is preserved by base change
   (`lem-weil-pbc-base-change-image`), so Y_K is nonempty. Local finite presentation
   gives local finite type, preserved by base change (`lem-weil-pbc-lft-base-change`).
   The Jacobson property (`lem-sc-lft-over-field-jacobson-space`) supplies a closed
   point, whose residue field is K (`lem-weil-pbc-closed-point-residue-field-base`).
   Hence there is a point y in Y(K).
2. Put q = |k| and let sigma be q-power Frobenius. Its action on points commutes
   with the right action. The torsor isomorphism gives a unique a in H(K) with
   sigma(y) = y a, without choosing any k-point of Y.
3. Apply `lem-sfb-lang-finite-field-group-surjectivity` to obtain g with
   g⁻¹ sigma(g) = a. Geometric connectedness gives connectedness over k.
   For z = y g⁻¹, associativity gives sigma(z) = y a (g a)⁻¹ = z.
4. Factor z through an affine open Spec A in Y. Its ring map v : A → K satisfies
   v(b)^q = v(b) for every b. By `lem-weil-unique-subfield-of-closure` with n = 1,
   these elements lie exactly in the image of k. Corestrict v and invert k's
   embedding to obtain a k-algebra map A → k. Taking spectra and the open immersion
   yields the required k-point. This needs no affine or separated hypothesis on Y. -/
theorem finiteField_connectedGroup_torsor_nonempty
    (k : Type u) [Field k] [Finite k]
    (H : Over (Spec (.of k))) [GrpObj H]
    [IsAffine H.left] [Smooth H.hom] [GeometricallyConnected H.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (Y : Over (Spec (.of k)))
    [Flat Y.hom] [Surjective Y.hom] [LocallyOfFinitePresentation Y.hom]
    (act : Y ⊗ H ⟶ Y)
    (unit : lift (𝟙 Y) (toUnit Y ≫ MonObj.one (X := H)) ≫ act = 𝟙 Y)
    (assoc : (act ▷ H) ≫ act =
      (α_ Y H H).hom ≫ (Y ◁ MonObj.mul (X := H)) ≫ act)
    [IsIso (lift (fst Y H) act)] :
    Nonempty (Over.mk (𝟙 (Spec (.of k))) ⟶ Y) := by
  sorry

end AlgebraicGeometry
