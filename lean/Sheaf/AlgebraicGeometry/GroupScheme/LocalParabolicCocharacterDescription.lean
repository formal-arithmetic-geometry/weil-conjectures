module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.FiniteType
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry

/-! # Local parabolics as cocharacter limit subgroups

Source: Conrad, Reductive group schemes, Proposition 5.2.3 and proof, pp.152--153.
(blueprint: lem-sfb-local-parabolic-cocharacter-description)

The orbit extension is stated on Laurent and polynomial spectra over every test algebra.
Maps to G over A are equivalent to maps to G_B over B by the pullback universal property.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- The generic Laurent coordinate, with coefficients extended from A to B.
Source: Conrad, Proposition 5.2.3, pp.152--153, and Section 4.1.
(blueprint: lem-sfb-local-parabolic-cocharacter-description) -/
def localParabolicLaurentPoint (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (algSpec (.of A)).obj (op (CommAlgCat.of A (LaurentPolynomial B))) ⟶
      (RingGroupSchemes.multiplicative A).X :=
  (algSpec (.of A)).map
    (CommAlgCat.ofHom (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId A B))).op

/-- The canonical punctured-line inclusion, from B[t,t⁻¹] ← B[t].
Source: Conrad, Section 4.1, definition of the dynamic subgroup.
(blueprint: lem-sfb-local-parabolic-cocharacter-description) -/
def localParabolicPuncture (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (algSpec (.of A)).obj (op (CommAlgCat.of A (LaurentPolynomial B))) ⟶
      (algSpec (.of A)).obj (op (CommAlgCat.of A (Polynomial B))) :=
  (algSpec (.of A)).map
    (CommAlgCat.ofHom (Polynomial.toLaurentAlg.restrictScalars A)).op

/-- The projection from the punctured affine line to Spec B, for constant B-points.
Source: Conrad, Section 4.1 and Proposition 5.2.3, pp.152--153.
(blueprint: lem-sfb-local-parabolic-cocharacter-description) -/
def localParabolicLaurentProjection (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    (algSpec (.of A)).obj (op (CommAlgCat.of A (LaurentPolynomial B))) ⟶
      (algSpec (.of A)).obj (op (CommAlgCat.of A B)) :=
  (algSpec (.of A)).map
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom A B (LaurentPolynomial B))).op

/-- A parabolic containing a specified split maximal torus over a Noetherian local
ring is the limit subgroup of a cocharacter of that torus, on every test algebra.

Source: Conrad, Proposition 5.2.3 and proof, pp.152--153.
(blueprint: lem-sfb-local-parabolic-cocharacter-description)

Proof plan:
1. Over an algebraic closure of the residue field, convert the Borel-containing
   hypothesis to the proper-quotient convention. Use
   lem-sfb-algebraic-group-homogeneous-quotient, lem-sfb-borel-quotient-proper-geometry,
   lem-sfb-nested-homogeneous-quotient-geometry and lem-weil-pbc-image-universally-closed.
2. Apply lem-sfb-split-parabolic-root-sign-cone on that fibre. By
   lem-sfb-relative-diagonalizable-character-duality its cocharacter is an integer
   tuple. Lift the tuple through the specified split torus by Laurent monomials.
3. The tangent inclusion of H in G is injective and equivariant. Apply
   lem-sfb-relative-tangent-weight-base-change to decompose both finite projective
   tangent modules into full-torus weights, compatibly with base change. The
   lem-sfb-relative-dynamic-subgroups Lie formula identifies the fibre weights:
   inclusion is an isomorphism at nonnegative cocharacter degree, and H is zero
   at negative degree. Faithful field extension descends this to the residue field.
4. Apply lem-weil-pbc-nakayama-local-generators weight by weight: negative pieces
   vanish and nonnegative inclusions surject. Thus Lie H is the nonnegative part
   of Lie G. These equalities persist under arbitrary scalar extension.
5. Form P_H(lambda) by lem-sfb-relative-dynamic-subgroups. Its Lie algebra is all
   of Lie H. On geometric fibres lem-sfb-smooth-subgroup-tangent-generation gives
   equality, and lem-sfb-flat-geometric-fibre-open-criterion gives P_H(lambda)=H.
   Finite presentation follows from lem-weil-pbc-finite-type-algebra-noetherian.
6. Composing the extending H-orbits with H → G factors H through P_G(lambda).
   This is a closed immersion, with the same Lie algebra on every geometric fibre.
   The same tangent-generation and fibrewise criteria give H=P_G(lambda). Its
   defining functor gives the displayed equivalence, also for nonreduced algebras. -/
theorem exists_localParabolic_cocharacter
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (G H T : Grp (Over (Spec (.of A))))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [Smooth H.X.hom]
    (i : H ⟶ G) [IsClosedImmersion i.hom.hom.left]
    (j : T ⟶ H) [IsClosedImmersion j.hom.hom.left]
    (r : ℕ) (e : T ≅ RingGroupSchemes.splitTorus A r)
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω),
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj G))
    (hpar : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω),
      ConnectedSpace
          (((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj H).X.left) ∧
      ∃ (B : Grp (Over (Spec (.of Ω))))
        (b : B ⟶ ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj H)),
        IsBorelGroupScheme
          ((b ≫ (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map i).hom.hom))
    (hmax : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω),
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map (j ≫ i))) :
    ∃ lam : RingGroupSchemes.multiplicative A ⟶ T,
      ∀ (B : Type u) [CommRing B] [Algebra A B]
        (g : (algSpec (.of A)).obj (op (CommAlgCat.of A B)) ⟶ G.X),
        (∃ h : (algSpec (.of A)).obj (op (CommAlgCat.of A B)) ⟶ H.X,
          h ≫ i.hom.hom = g) ↔
        ∃ a : (algSpec (.of A)).obj (op (CommAlgCat.of A (Polynomial B))) ⟶ G.X,
          localParabolicPuncture A B ≫ a =
            (localParabolicLaurentPoint A B ≫ (lam ≫ j ≫ i).hom.hom) *
              (localParabolicLaurentProjection A B ≫ g) *
              (localParabolicLaurentPoint A B ≫ (lam ≫ j ≫ i).hom.hom)⁻¹ := by
  sorry

end AlgebraicGeometry
