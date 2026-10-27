module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Sheaf.RingTheory.ReducedIntegralPolynomialGeneralizedInverse
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.RelativelyClosedConstantsUnitsFG
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.NoetherianSpace

/-!
# Uniqueness of the scalar-field integral closure

Source: Stacks Project, Varieties, Tags 04MI and 04MK.
(blueprint: lem-sfb-connected-reduced-scalar-field-uniqueness)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- For a nonempty connected reduced scheme locally of finite type over two fields,
the scalar maps into global sections are injective, their integral closures agree
as subrings of global sections, and this common subring is a field.

Source: Stacks Project, Varieties, Tag 04MK (proposition-unique-base-field), together
with Tag 04MI (lemma-integral-closure-ground-field).
(blueprint: lem-sfb-connected-reduced-scalar-field-uniqueness)

Proof:
1. Choose a point of `X`. Its local ring is nonzero, so the germ of the identity
   shows that the global-sections ring `A` is nonzero. Each unital scalar map from
   a field into `A` is injective: if a nonzero scalar vanished, its inverse would
   give `1 = 0`. Reducedness makes `A` reduced, and
   lem-pc-scheme-connected-iff-idempotents makes its only idempotents zero and one.
2. For either scalar field, let `C` be its integral closure. For nonzero `c` in `C`,
   lem-sfb-reduced-integral-polynomial-generalized-inverse gives `y = q(c)` with
   `c^2 * y = c`. Since `y` is a polynomial in `c`, it belongs to `C`.
   Then `e = c * y` is idempotent and nonzero (otherwise `c = c * e = 0`),
   hence `e = 1`. Thus every nonzero element of `C` has an inverse in `C`.
3. By lem-sfb-integral-element-tower-descent, each `C` is integrally closed in `A`.
   The inclusion `C` into `A` gives `X` a morphism to `Spec C` by
   lem-weil-pbc-morphism-into-affine-scheme. It factors the original scalar map
   and is locally of finite type: the generators on each original finite-type
   affine chart still generate over the larger coefficient field `C`.
4. If `X` is quasi-compact, lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-noetherian-finitely-many-components give finitely many irreducible
   components. By lem-sfb-relatively-closed-constants-units-fg, the unit quotient
   for either new scalar field `C_i` is finitely generated. Their intersection `F`
   is a field, since inverses in the two subfields agree in `A`.
   Apply lem-sfb-subfield-units-quotient-finite in both orders: each `C_i/F` is
   finite. Thus every element of either field is integral over the other;
   their integral closedness in `A` gives both inclusions and hence equality.
5. In general, cover `X` by finite-type affine charts. They are quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs and Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Using
   lem-weil-pbc-noetherian-scheme-closed-subsets-minimal,
   lem-sfb-noetherian-connected-components-open, and
   lem-sfb-noetherian-space-compact-subsets, their nonempty connected components
   form an open cover by connected reduced quasi-compact schemes `U_j`.
   The two scalar morphisms remain locally of finite type by
   lem-weil-pbc-lft-affine-pairs. The quasi-compact case gives a common field `K_j`
   of integral constants on every `U_j`.
6. For `f` integral over the first field, its restrictions `f_j` lie in `K_j`.
   Choose one `U_j` and one monic polynomial `P` over the second field vanishing
   on `f_j`. On any nonempty overlap the restriction maps from both fields `K_j`
   into the ring of sections are injective: a point of the overlap makes the
   latter ring nonzero. Restriction respects polynomial evaluation.
7. Consequently `P(f_j) = 0` propagates across any nonempty overlap. The union
   of successful opens and the union of unsuccessful opens are disjoint opens
   covering `X`. The first is nonempty, so connectedness forces the second empty.
   Each `U_j` is nonempty, hence all indices are successful.
8. The sheaf uniqueness axiom gives `P(f) = 0` globally. Hence `f` is integral
   over the second field. Interchange the fields for the reverse inclusion.
   Together with step 2, this proves all conclusions. -/
theorem connected_reduced_scalar_field_integralClosure_unique
    (X : Scheme.{u}) [ConnectedSpace X] [IsReduced X]
    (k₁ k₂ : Type u) [Field k₁] [Field k₂]
    (a₁ : X ⟶ Spec (CommRingCat.of k₁)) (a₂ : X ⟶ Spec (CommRingCat.of k₂))
    [LocallyOfFiniteType a₁] [LocallyOfFiniteType a₂] :
    Function.Injective (((ΓSpecIso (CommRingCat.of k₁)).inv ≫ a₁.appTop).hom) ∧
    Function.Injective (((ΓSpecIso (CommRingCat.of k₂)).inv ≫ a₂.appTop).hom) ∧
    (@Subalgebra.toSubring k₁ Γ(X, ⊤) _ _
      (((ΓSpecIso (CommRingCat.of k₁)).inv ≫ a₁.appTop).hom.toAlgebra)
      (@integralClosure k₁ Γ(X, ⊤) _ _
        (((ΓSpecIso (CommRingCat.of k₁)).inv ≫ a₁.appTop).hom.toAlgebra))) =
      (@Subalgebra.toSubring k₂ Γ(X, ⊤) _ _
        (((ΓSpecIso (CommRingCat.of k₂)).inv ≫ a₂.appTop).hom.toAlgebra)
        (@integralClosure k₂ Γ(X, ⊤) _ _
          (((ΓSpecIso (CommRingCat.of k₂)).inv ≫ a₂.appTop).hom.toAlgebra))) ∧
    IsField (@Subalgebra.toSubring k₁ Γ(X, ⊤) _ _
      (((ΓSpecIso (CommRingCat.of k₁)).inv ≫ a₁.appTop).hom.toAlgebra)
      (@integralClosure k₁ Γ(X, ⊤) _ _
        (((ΓSpecIso (CommRingCat.of k₁)).inv ≫ a₁.appTop).hom.toAlgebra))) := by
  sorry

end AlgebraicGeometry.Scheme
