/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.FiniteSupportProjection
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Identifying the support scalar mate with the projection map

Source: Stacks Project, Cohomology on Sites (Tag 07A6), More on Etale Cohomology
(Tag 0GL6), and the coefficient argument in `ExceptionalAdjointAdmissibility`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- Realization into the fixed coefficient category, using the ring structure underlying
its monoidal coefficient structure. This is the usual realization inverse; the explicit
instance prevents repeated conversion through the two ring structures on `ULift`.
Source: Stacks Tag 00YV (blueprint: lem-sf-support-scalar-projection-identification). -/
@[irreducible]
noncomputable def projectionRealizationInverse (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleDerivedCategory T A ⥤ DerivedCategory
      (Sheaf (ProEt.topology T)
        (@ModuleCat.{u + 1} (ULift.{u + 1, u} A) CommRing.toRing)) :=
  (sfIntrinsicDerivedEquivalence T A).inverse

/-- The fixed coefficient realization is the published intrinsic realization inverse.
Source: Stacks Tag 00YV (blueprint: lem-sf-support-scalar-projection-identification). -/
theorem projectionRealizationInverse_eq (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    projectionRealizationInverse T A = (sfIntrinsicDerivedEquivalence T A).inverse := by
  unfold projectionRealizationInverse
  rfl

instance projectionRealizationInverse_reflects (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (projectionRealizationInverse T A).ReflectsIsomorphisms := by
  rw [projectionRealizationInverse_eq]
  infer_instance

/-- The scalar mate, after exact restriction and realization, is the compact-support
projection arrow, up to its scalar/tensor boundary identifications.

Source: Stacks Tags 07A6 and 0GL6, scalar-extension/projection-formula identification.
(blueprint: lem-sf-support-scalar-projection-identification).

Proof: restriction of extension along A to B is tensor with the restricted constant
B sheaf. The ordinary balancing isomorphism sends b tensor m to b tensor m; apply
it to flat-term K-flat resolutions, and descend using the universal derived counits.
The derived scalar unit becomes m mapped to 1 tensor m. Uniqueness of left adjoints
transports this identification to the supplied scalar adjunctions. Realization and
its inverse commute with restriction by the identity on underlying abelian sheaves.
The given compact-support restriction square is the exact open square followed by
the K-injective-normalized proper square. Transpose its scalar mate through the
scalar adjunctions. For the proper factor the defining K-injective comparison
identifies this transpose with the geometric counit; this is exactly the transpose
of the proper projection map. For the open factor, left-adjoint uniqueness fixes
the comparison by the open unit, giving the inverse open projection isomorphism.
Compose these two equalities and the canonical inverse-image composition comparison.
The resulting square has the scalar/tensor identifications as invertible boundary
maps and the displayed arrows as its horizontal maps; it is the required arrow
isomorphism. This identification uses no compact-support right adjoint and does
not assume either horizontal map invertible. It includes zero rings and arbitrary
unbounded K, since K-flat and K-injective resolutions exist in the ambient categories. -/
theorem support_scalar_projection_identification
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (LX : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory X B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aX : LX ⊣ (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (K : proEtaleDerivedCategory X A) :
    letI : Algebra (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) := φ.ulift.toAlgebra
    let N := ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} B)
    Nonempty (Arrow.mk ((projectionRealizationInverse Y A).map
      ((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((((mateEquiv aX aY).symm
          (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans).app K))) ≅
      Arrow.mk (ProEtale.compactSupportProjectionComponent
        (@ModuleCat.{u + 1} (ULift.{u + 1, u} A) CommRing.toRing) c
          ((projectionRealizationInverse X A).obj K)
            ((DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf (ProEt.topology Y)
                (@ModuleCat.{u + 1} (ULift.{u + 1, u} A) CommRing.toRing)).obj N)))) := by
  sorry

end WeilConjectures
