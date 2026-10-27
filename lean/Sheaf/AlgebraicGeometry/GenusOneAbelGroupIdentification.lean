/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.DivisorModule
public import Sheaf.AlgebraicGeometry.DivisorClassCurve
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
import WeilConjectures.AlgebraicGeometry.Hilbert.Curve
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf
import Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
import Sheaf.AlgebraicGeometry.HilbertToPicardMorphism
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.SymmetricAbelImageGeometry

/-! # The elliptic group law and the pointed genus-one Abel identification

Source: Stacks Project, moduli-curves.tex, Tag 0DSV, example-pos-dim, genus-one
paragraph; Milne, Abelian Varieties, III Proposition 2.3 and Theorem 5.1(a)
(blueprint: lem-sfb-genus-one-abel-group-identification).

Group operations are written multiplicatively, including tensor product in Pic.
A group object in schemes over Spec k supplies the multiplication and inverse as
k-morphisms, together with their scheme identities. The equivalence on rational
points is characterized by the actual divisor module O(P-O), rather than by an
unspecified abstract isomorphism of groups.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonObj TopologicalSpace

namespace AlgebraicGeometry

/-- A smooth projective connected genus-one curve with a specified origin has a
commutative scheme group law, and its pointed Abel map identifies its rational
points with the degree-zero Picard group.

Source: Stacks Project, moduli-curves.tex, Tag 0DSV, example-pos-dim, genus-one
paragraph; Milne, Abelian Varieties, III Proposition 2.3 and Theorem 5.1(a)
(blueprint: lem-sfb-genus-one-abel-group-identification).

Proof:
1. Smooth-connected-curve-local-rings gives integrality; projective-proper gives
   properness. The pointed curve is geometrically integral by prop-pc-xk-integral.
   Genus-agrees-sc and curve-base-change-relative-dimension-one supply the genus
   and relative dimension for thm-sc-jacobian-representability. This yields a
   Jacobian J with a group-compatible representation of the Picard-zero functor.
2. By thm-pc-hilb-curves, Hilb^1 is represented. A finite locally free rank-one
   algebra Rb has 1=ub and b*b=vb; b=1*b implies uv=1. Thus its unit is an
   isomorphism and every degree-one family is the graph of a unique section.
   Conversely graphs are closed by proper-base-change and
   section-separated-closed-immersion. These inverse constructions commute with
   every base change, including nonreduced bases, so representable-unique gives
   Hilb^1=Y.
3. Symmetric-abel-image-geometry at genus one gives a closed immersion e:Y -> J
   whose scheme-theoretic image is all J. Hilb-to-pic-morphism identifies its
   formula on the universal graph with O(P-O), as an equality of scheme maps.
   By scheme-theoretic-image the kernel ideal is zero; a closed immersion is
   locally Spec(R/I) -> Spec R, so e is an isomorphism and e(O)=0.
4. Transport multiplication and inverse from J using e: m=e^-1 m_J (e times e)
   and i=e^-1 i_J e. On every test scheme the group identities and commutativity
   follow by cancellation of e, since J represents the abelian Picard functor.
   Yoneda gives the identities of scheme maps; the identity section is O.
5. The pointwise map is the composite of e with the inverse of the representing
   group isomorphism Pic^0(Y) -> J(k). It is bijective and respects tensor product.
   Divisor-class-curve identifies its class with the specified divisor module.
   Its image is precisely picZero, and it sends O to the trivial class. -/
theorem exists_genus_one_abel_group_identification
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (hg : f.genus = 1)
    (O : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk f) :
    ∃ (_ : GrpObj (Over.mk f)),
      IsCommMonObj (Over.mk f) ∧
      CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (.of k)))) ≫
        η[Over.mk f] = O ∧
      ∃ (G : Subgroup Y.Pic), (G : Set Y.Pic) = f.picZero ∧
        ∃ α : (Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk f) ≃* G,
          α O = 1 ∧
          ∀ P : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk f,
            ∃ p o : closedPoints Y,
              (∀ s : Spec (.of k), p.val = P.left.base s ∧ o.val = O.left.base s) ∧
              Nonempty ((fromSkeleton Y.Modules).obj (α P).val.val ≅
                Scheme.Divisor.moduleOfSmoothConnectedCurve k Y f
                  (Finsupp.single p (1 : ℤ) - Finsupp.single o (1 : ℤ))) := by
  sorry

end AlgebraicGeometry
