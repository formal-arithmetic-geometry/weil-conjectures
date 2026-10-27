/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.AffinePGLAction
public import Mathlib.RingTheory.FiniteType

/-!
# Affine PGL quotients with finite geometric stabilizers

Source: Alper, arXiv:1005.2398v3, Theorems 9.1.4, 9.7.6, 5.3.1,
8.3.2 and 7.2.1, and §8.1
(blueprint: lem-sfb-affine-pgl-finite-stabilizer-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AffinePGL

/-- The canonical invariant spectrum is a surjective categorical quotient for
all algebraic-space targets and is a geometric orbit quotient. Closed orbits
are expressed by a closed subset of the geometric base change whose geometric
points are exactly the orbit. Dimension-zero stabilizers are expressed by the
finite set of PGL classes fixing the geometric point; this is equivalent for a
finite-type stabilizer over an algebraically closed field and permits nilpotents.
Source: Alper, arXiv:1005.2398v3, Theorems 9.1.4, 9.7.6, 5.3.1, 8.3.2,
7.2.1 and §8.1 (blueprint: lem-sfb-affine-pgl-finite-stabilizer-quotient).
Proof:
1. Put Y = Spec(E^G) and X = [Spec E / PGL]. The action-groupoid presentation
   (def-sfb-affine-action-quotient-stack, lem-sfb-affine-action-stack-presentation)
   gives a smooth surjective atlas and a finite-type stack with affine diagonal.
   Its geometric diagonal fibres are translates of stabilizers, so the
   dimension-zero hypothesis gives a quasi-finite separated diagonal. This
   concerns the full stabilizer scheme, including its nilpotents.
2. By lem-sfb-pgl-geometric-reductivity, invariant elements lift after a positive
   power along equivariant finite-type algebra surjections. Apply
   lem-sfb-power-lifting-adequate-affine-quotient to obtain the canonical adequate
   map X → Y. PGL is geometrically reductive in every characteristic, also for r=1.
3. Apply lem-sfb-adequate-quasifinite-diagonal-finite with affine target Y: the
   diagonal and consequently the inertia are finite. Pointwise stabilizer
   finiteness alone is not used to assert uniform finiteness of inertia.
4. By lem-sfb-finite-inertia-adequate-coarse-space, X has an adequate coarse
   space Q with a surjective map, universal for every algebraic space and
   bijective on geometric isomorphism classes. Its finite diagonal makes Q
   separated. This argument does not assume the stack is Deligne--Mumford.
5. Apply lem-sfb-adequate-locally-separated-universality to the separated Q and
   the scheme Y. It gives maps Y → Q and Q → Y compatible with the stack maps.
   Injectivity of the same universal bijections makes their composites the
   identities. Thus the canonical adequate map to Y is the coarse map.
6. Maps from the quotient stack to an algebraic space are exactly invariant
   maps from its atlas. Over an algebraically closed field every PGL torsor
   is trivial, so stack isomorphism classes are exactly the PGL orbits. Transfer
   both coarse properties along Y ≅ Q. Surjectivity follows by composing the
   surjective atlas and coarse map. Invariance follows because the two
   pullbacks of an invariant coordinate function agree. -/
theorem affine_pgl_finite_stabilizer_quotient
    (k : Type u) [Field k] (r : ℕ) (hr : 1 ≤ r)
    (E : Type u) [CommRing E] [Algebra k E] [Algebra.FiniteType k E]
    (D : Action k E r)
    (hclosed : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : PGLLinearization.fieldTest k Ω ⟶ affineOver k E),
      ∃ C : Set (pullback (C := Scheme.{u}) (affineOver k E).hom
        (PGLLinearization.fieldTest k Ω).hom), IsClosed C ∧
        ∀ y : PGLLinearization.fieldTest k Ω ⟶ affineOver k E,
          ((∃ g : Matrix.GeneralLinearGroup (Fin r) Ω,
            D.act _ (PGLLinearization.fieldMatrix Ω g) x = y) ↔
            PGLLinearization.geometricImage Ω y ∈ C))
    (hstabilizer : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : PGLLinearization.fieldTest k Ω ⟶ affineOver k E),
      Set.Finite (Matrix.ProjGenLinGroup.mk ''
        {g : Matrix.GeneralLinearGroup (Fin r) Ω |
          D.act _ (PGLLinearization.fieldMatrix Ω g) x = x})) :
    Surjective D.quotientMap.left ∧
    (∀ (T : Over (Spec (.of k))) (g : PGLLinearization.Matrices k r T)
      (x : T ⟶ affineOver k E), D.act T g x ≫ D.quotientMap = x ≫ D.quotientMap) ∧
    (∀ (B : AlgebraicSpace (Spec (.of k)))
      (f : yoneda.obj (affineOver k E) ⟶ B.obj.obj), D.IsInvariantMap B f →
      ∃! a : yoneda.obj D.quotientOver ⟶ B.obj.obj, yoneda.map D.quotientMap ≫ a = f) ∧
    (∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω],
      Function.Surjective
        (fun x : PGLLinearization.fieldTest k Ω ⟶ affineOver k E ↦ x ≫ D.quotientMap) ∧
      ∀ x y : PGLLinearization.fieldTest k Ω ⟶ affineOver k E,
        (x ≫ D.quotientMap = y ≫ D.quotientMap ↔
          ∃ g : Matrix.GeneralLinearGroup (Fin r) Ω,
            D.act _ (PGLLinearization.fieldMatrix Ω g) x = y)) := by
  sorry

end AlgebraicGeometry.AffinePGL
