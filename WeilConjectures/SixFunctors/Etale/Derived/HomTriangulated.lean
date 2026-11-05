/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Exactness of the derived internal hom of étale sheaves in each variable

Let `A` be a monoidal closed Grothendieck abelian coefficient category as in
`WeilConjectures.SixFunctors.Etale.Derived.Hom` and `X` a scheme. This file records that the
derived internal hom `RHom(-, -)` of `D(X_ét, A)` is exact in each variable (blueprint
`lem-sf-hom-triangulated`):

* for a distinguished triangle `K' ⟶ K ⟶ K'' ⟶ K'[1]` and any `M`, the induced maps
  `RHom(K'', M) ⟶ RHom(K, M) ⟶ RHom(K', M)` extend to a distinguished triangle
  (`AlgebraicGeometry.Etale.exists_distTriang_derivedHom_left`); this is the specialisation of
  `DerivedCategory.exists_distinguished_ihom_pre`, proved on the model given by the internal hom
  complex into a K-injective complex;
* for a distinguished triangle `M' ⟶ M ⟶ M'' ⟶ M'[1]` and any `K`, the induced maps
  `RHom(K, M') ⟶ RHom(K, M) ⟶ RHom(K, M'')` extend to a distinguished triangle
  (`AlgebraicGeometry.Etale.exists_distTriang_derivedHom_right`), `RHom(K, -)` being a
  triangulated functor as the right adjoint of the triangulated functor `K ⊗ᴸ -`.

The corollaries `AlgebraicGeometry.Etale.derivedHom_mem_of_distTriang_left` and
`AlgebraicGeometry.Etale.derivedHom_mem_of_distTriang_right` are the forms used for dévissage:
membership of `RHom(K, M)` in a triangulated subcategory follows from that of the two other
terms.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}}

/-- Blueprint `lem-sf-hom-triangulated`: Exactness of the internal Hom in each variable, first
variable. For a distinguished triangle `K' ⟶ K ⟶ K'' ⟶ K'[1]` of `D(X_ét, A)` and any `M`, the
maps `RHom(K'', M) ⟶ RHom(K, M) ⟶ RHom(K', M)` induced by `K ⟶ K''` and `K' ⟶ K` extend to a
distinguished triangle `RHom(K'', M) ⟶ RHom(K, M) ⟶ RHom(K', M) ⟶ RHom(K'', M)[1]`. -/
theorem exists_distTriang_derivedHom_left
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) :
    ∃ w, Triangle.mk (((RHom(X)[A]).map T.mor₂.op).app M)
      (((RHom(X)[A]).map T.mor₁.op).app M) w ∈ distTriang _ :=
  DerivedCategory.exists_distinguished_ihom_pre T hT M

/-- Blueprint `lem-sf-hom-triangulated`: Exactness of the internal Hom in each variable, second
variable. For a distinguished triangle `M' ⟶ M ⟶ M'' ⟶ M'[1]` of `D(X_ét, A)` and any `K`, the
maps `RHom(K, M') ⟶ RHom(K, M) ⟶ RHom(K, M'')` extend to a distinguished triangle
`RHom(K, M') ⟶ RHom(K, M) ⟶ RHom(K, M'') ⟶ RHom(K, M')[1]`: the functor `RHom(K, -)` is
triangulated, being right adjoint to the triangulated functor `K ⊗ᴸ -`. -/
theorem exists_distTriang_derivedHom_right
    (K : (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ)
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) :
    ∃ w, Triangle.mk (((RHom(X)[A]).obj K).map T.mor₁)
      (((RHom(X)[A]).obj K).map T.mor₂) w ∈ distTriang _ := by
  have := (derivedTensorHomAdjunction A K.unop).isTriangulated_rightAdjoint
  exact ⟨_, ((RHom(X)[A]).obj K).map_distinguished T hT⟩

/-- Blueprint `lem-sf-hom-triangulated`, dévissage in the first variable: if
`K' ⟶ K ⟶ K'' ⟶ K'[1]` is a distinguished triangle and `RHom(K', M)`, `RHom(K'', M)` lie in a
subcategory `P` of `D(X_ét, A)` closed under isomorphisms and extensions, then so does
`RHom(K, M)`. -/
theorem derivedHom_mem_of_distTriang_left
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) (h₁ : P (((RHom(X)[A]).obj (op T.obj₁)).obj M))
    (h₃ : P (((RHom(X)[A]).obj (op T.obj₃)).obj M)) :
    P (((RHom(X)[A]).obj (op T.obj₂)).obj M) := by
  obtain ⟨w, hw⟩ := exists_distTriang_derivedHom_left M T hT
  exact P.ext_of_isTriangulatedClosed₂ _ hw h₃ h₁

end Etale

end AlgebraicGeometry
