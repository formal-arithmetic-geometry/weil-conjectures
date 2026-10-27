/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Closed unipotent orbits in affine schemes

Source: Milne, Algebraic Groups (2017), Theorem 17.64 (Kostant--Rosenlicht),
printed pp.373--374 (blueprint: lem-sfb-kostant-rosenlicht-affine-orbits).

The image is the range of the underlying map of the orbit morphism on all scheme points.
A reduced closed immersion with precisely that range describes its reduced induced structure.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every orbit of a smooth connected unipotent affine algebraic group acting on an affine
finite-type scheme is closed and has its reduced induced closed subscheme structure.
No reducedness of the ambient scheme or characteristic hypothesis is required.

Source: Milne, Algebraic Groups (2017), Theorem 17.64, printed pp.373--374
(blueprint: lem-sfb-kostant-rosenlicht-affine-orbits).

Proof, following the five steps of the node:
1. Affineness makes Y separated (lem-weil-pbc-affine-source-morphism-separated).
   Apply lem-sfb-smooth-group-orbit-geometry: the orbit O is locally closed, its
   orbit map is faithfully flat, and its closure and boundary are invariant.
   Give the closure X and boundary Z their reduced structures using
   lem-weil-pbc-reduced-induced-closed-subscheme. Then X = Spec A is reduced affine
   finite type and O is open dense in X, while Z is proper closed.
2. The radical ideal I defining Z is nonzero, since y is outside Z. If Z is empty
   we are done. Otherwise it suffices to find a nonzero scalar in I.
3. The right action x.v = inverse(v)x induces the coaction on A. The affine spectrum
   dictionary, lem-weil-pbc-algebra-tensor-pushout-universal-property and
   lem-sfb-rational-representation-comodule-dictionary give the rational action
   (v.f)(x) = f(inverse(v)x). Invariance of Z makes I a rational submodule:
   the kernel of A tensor k[V] -> (A/I) tensor k[V] is I tensor k[V], using a vector-space
   complement (lem-weil-pbc-vector-space-free and def-weil-pbc-module-tensor-product).
   Choose nonzero h in I and use lem-sfb-comodule-finite-subrepresentation to put h
   in a nonzero finite-dimensional rational submodule W of I.
4. Choose a basis of W and use the representation/comodule dictionary. The faithful
   closed matrix representation in def-sfb-solvable-group-structure is injective on
   all algebra-valued points, and its geometric unipotence holds on k-points. Apply
   lem-sfb-unipotent-rational-representation-fixed-vector to obtain nonzero f in W
   fixed by V(k). Thus f(vy) = f(y) for every v in V(k).
5. By lem-sc-lft-over-field-jacobson-space and
   lem-weil-pbc-closed-point-residue-field-base, V(k) is dense in V. Continuity of the
   orbit map makes its rational image dense in X. Therefore f-f(y) vanishes on X;
   reducedness of A makes f the nonzero scalar f(y). This puts 1 in I, contradicting
   nonemptiness of Z. Hence O is closed. Finally apply
   lem-weil-pbc-reduced-induced-closed-subscheme for its reduced closed immersion. -/
theorem kostant_rosenlicht_affine_orbits
    {k : Type u} [Field k] [IsAlgClosed k]
    (V : Grp (Over (Spec (.of k))))
    [IsAffine V.X.left] [Smooth V.X.hom] [ConnectedSpace V.X.left]
    [LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]
    (hV : SolvableGroupStructure.IsUnipotent V)
    (Y : Over (Spec (.of k))) [IsAffine Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [ModObj V.X Y]
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    IsClosed (Set.range (lift (𝟙 V.X) (toUnit V.X ≫ y) ≫ γ[V.X, Y]).left) ∧
      ∃ (O : Scheme.{u}) (j : O ⟶ Y.left),
        IsReduced O ∧ IsClosedImmersion j ∧
          Set.range j = Set.range (lift (𝟙 V.X) (toUnit V.X ≫ y) ≫ γ[V.X, Y]).left := by
  sorry

end AlgebraicGeometry
