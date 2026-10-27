module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension

/-! # The smooth open of proper curves with isolated lci singularities

Source: Stacks Project, moduli-curves.tex, Tag 0DZX, clauses (1) and (3)
(blueprint: lem-sfb-isolated-lci-curve-smooth-open).

Families are the existing algebraic-space families, with cartesian arrows. The base is
`Spec (ULift ℤ)`, the universe-polymorphic spectrum of the integers.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperCurveModuli

/-- Membership of a proper scheme's classifying point in the full open over the integers.
The isomorphism identifies the structure map over the specified field, not just the
underlying algebraic spaces. Source: Stacks, moduli-curves.tex, Tag 0DZX(3)
(blueprint: lem-sfb-isolated-lci-curve-smooth-open). -/
def IntegerSchemePointIn
    (L : OpenModuliSubstack (category (Spec (.of (ULift.{u} ℤ)))))
    (K : Type u) [Field K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) : Prop :=
  ∃ X : ProperCurveFamily (Over.mk (specULiftZIsTerminal.from (Spec (.of K)))),
    ∃ e : X.space.obj.obj ≅ yoneda.obj
        (Over.mk (f ≫ specULiftZIsTerminal.from (Spec (.of K)))),
      e.hom ≫ yoneda.map (Over.homMk
        (U := Over.mk (f ≫ specULiftZIsTerminal.from (Spec (.of K))))
        (V := Over.mk (specULiftZIsTerminal.from (Spec (.of K)))) f rfl) = X.projection ∧
      L.property ⟨Over.mk (specULiftZIsTerminal.from (Spec (.of K))), X⟩

/-- The isolated-lci locus is an open substack smooth over the integers, with exactly
the stated field points. No nonemptiness, connectedness, purity or perfectness is assumed.
Source: Stacks Project, moduli-curves.tex, Tag 0DZX(1),(3)
(blueprint: lem-sfb-isolated-lci-curve-smooth-open).

Proof:
1. For any proper flat finitely presented space family, use
   lem-sfb-space-lci-base-open to obtain the universal base open of lci fibres.
   Properness supplies the closed-map hypothesis; this open commutes with base change.
2. Use lem-sfb-space-flat-smooth-locus to form the closed nonsmooth subset. Apply
   lem-sfb-space-closed-subset-finite-fibre-open to obtain the universal base open on
   which its fibres are finite, also invariant under arbitrary base change.
3. Intersect the two opens. The full subgroupoid of families whose good open is the
   whole base is stable under pullback and etale descent. Its pullback to any scheme
   test is represented by that good open, including the specified projection.
4. Over any field, the good open is the whole base exactly when the scheme is lci
   and smooth away from finitely many points. Empty and disconnected schemes are allowed.
5. Every field-valued space object is a scheme by
   lem-sfb-separated-space-dimension-one-scheme. Use
   lem-weil-pbc-dimension-preserved-field-extension on affine etale charts to pass the
   geometric dimension bound to the original object. Apply
   lem-sfb-isolated-lci-curve-unobstructed with the coefficient ring supplied by
   lem-sfb-curve-smooth-locus-deformation-test. That criterion places each good field
   object in the smooth open of the entire algebraic curve stack, over the integers.
6. On every scheme test the pullback of that smooth open contains all residue-field
   points, hence is the whole test scheme. The good open is therefore contained in
   the smooth open. Restrict its smooth atlas; its composite to Spec Z remains smooth.
-/
theorem exists_isolated_lci_curve_smooth_open
    (halgebraic : IsAlgebraicModuliStack (category (Spec (.of (ULift.{u} ℤ))))) :
    ∃ L : OpenModuliSubstack (category (Spec (.of (ULift.{u} ℤ)))),
      IsSmoothModuliStack L.category ∧
      ∀ (K : Type u) [Field K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)),
        IsProper f → topologicalKrullDim C ≤ 1 →
          (IntegerSchemePointIn L K C f ↔
            (∃ (I : Type u) (A : I → CommRingCat.{u})
              (aA : ∀ i, Algebra K (A i)) (ft : ∀ i, Algebra.FiniteType K (A i))
              (φ : ∀ i, Spec (A i) ⟶ C),
              (∀ i, IsOpenImmersion (φ i)) ∧
              (∀ i, φ i ≫ f =
                Spec.map (CommRingCat.ofHom (@algebraMap K (A i) _ _ (aA i)))) ∧
              (∀ x : C, ∃ i, ∃ y : Spec (A i), φ i y = x) ∧
              (∀ i, @Algebra.IsLocalCompleteIntersection K (A i) _ _ (aA i) (ft i))) ∧
            ∃ S : Set C, S.Finite ∧
              ∀ x ∉ S, ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) := by
  sorry

end AlgebraicGeometry.ProperCurveModuli
