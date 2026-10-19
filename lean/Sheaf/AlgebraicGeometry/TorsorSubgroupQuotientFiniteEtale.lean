/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.GroupTheory.Index
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import Sheaf.AlgebraicGeometry.FreeFiniteGroupAffineQuotient

/-!
# The given subgroup quotient of a connected Galois cover

Source: Stacks Project, Groupoids, Tag 03BK (3), Spaces, Tag 07S7, and
Descent, Tags 02LA and 02VN; ILO XVI 3.7, printed p. 255
(blueprint: lem-per-torsor-subgroup-quotient-finite-etale).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The specified finite categorical quotient by a subgroup is connected finite etale,
with geometric fibre cardinality the subgroup index.
Source: Stacks Project, Tags 03BK (3), 07S7, 02LA and 02VN; ILO XVI 3.7, p. 255
(blueprint: lem-per-torsor-subgroup-quotient-finite-etale).

Proof:
1. The Galois-cover hypothesis gives a surjective finite etale G-torsor. The map
from the coproduct of G copies of E to E times_U E is an isomorphism: over E it is
a map of finite etale schemes, and simple transitivity makes its geometric fibre
a bijection. The conservative fibre functor of `lem-fet-galois-category` detects
this isomorphism, using `def-galois-category` and `lem-weil-pbc-scheme-coproduct-family`.
2. Restrict to H. Its torsor relation is a monomorphism, and E is affine over U
because c is finite. Apply `lem-per-free-finite-group-affine-quotient` to obtain
the surjective fppf orbit quotient q : E -> Q, categorical over U and compatible
with arbitrary base change on U.
3. The categorical properties of q and the given pi give maps Q -> Z and Z -> Q.
Uniqueness makes these mutually inverse and compatible with the quotient maps.
The inverse is over U by uniqueness for maps from E to U. Hence pi is surjective.
4. Base change along c. The torsor becomes the coproduct of G copies of E,
and H acts on the labels by left multiplication. The orbit sheaf is therefore
the coproduct of copies of E indexed by right cosets H\\G, with its fold map.
On each affine open this is the product of identity algebras, hence finite etale.
5. The singleton c is an fpqc covering: it is flat, surjective and affine, and
the inverse image of each affine open is affine and maps onto that open.
Apply `lem-weil-pbc-fpqc-descend-finite` and `lem-galois-fpqc-descend-etale` to
the split quotient to descend finiteness and etaleness of v.
6. Lift any algebraically closed geometric point of U to E and pull back the
split quotient. Its fibre has one point for each right H-coset; inversion
identifies these with the left cosets counted by H.index. The surjective image
of connected E is connected, so Z is connected. This includes H = 1 and H = G. -/
theorem Scheme.GaloisCoverAction.torsor_subgroup_quotient_finite_etale
    {U : Scheme.{u}} [ConnectedSpace U]
    {G : Type v} [Group G] [Finite G]
    (c : Scheme.GaloisCoverAction G U) [ConnectedSpace c.Z]
    (H : Subgroup G) (Z : Scheme.{u}) (π : c.Z ⟶ Z) (v : Z ⟶ U)
    (_hπv : π ≫ v = c.π) [IsFinite π]
    (hπ : ∀ h : H, c.smul h.val ≫ π = π)
    (_hsheaf : ∀ W : Z.Opens, Function.Injective (π.app W) ∧
      ∀ s : Γ(c.Z, π ⁻¹ᵁ W),
        (∀ h : H, (c.smul h.val).app (π ⁻¹ᵁ W) s =
          c.Z.presheaf.map
            (eqToHom (congrArg (fun f : c.Z ⟶ Z ↦ f ⁻¹ᵁ W) (hπ h))).op s) ↔
          ∃ t : Γ(Z, W), π.app W t = s)
    (_hquotient : ∀ (T : Scheme.{u}) (f : c.Z ⟶ T),
      (∀ h : H, c.smul h.val ≫ f = f) → ∃! q : Z ⟶ T, π ≫ q = f) :
    Surjective π ∧ IsFinite v ∧ Etale v ∧ ConnectedSpace Z ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = H.index := by
  sorry

end AlgebraicGeometry
