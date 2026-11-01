/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bertini.BertiniUniversalFamily
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.ZetaSeries
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.PointCount
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The canonical polynomial coordinates of the singular fibre

Source: Stacks Project, Varieties, Tag 0FD6, the universal-family diagram.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Polynomial affine space commutes with extension of the coefficient ring.
Source: Stacks Project, Schemes, lemma-fibre-product-affine-schemes.
(blueprint: lem-zl-bertini-singular-fibre-coordinates). -/
theorem bertini_polynomial_baseChange_square
    {k K : Type u} [CommRing k] [CommRing K] (α : k →+* K) (I : Type u) :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := I) α)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial I K)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
      (Spec.map (CommRingCat.ofHom α)) := by
  let : Algebra k K := α.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := I) (R := k) (S := K)
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout k (MvPolynomial I k) K (MvPolynomial I K))

/-- The coefficient projection of the singular fibre, before adjoining residue-field scalars.
Source: Stacks Project, Tag 0FD6.
(blueprint: lem-zl-bertini-singular-fibre-coordinates). -/
noncomputable def bertiniSingularFibreCoefficient
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    (bertiniSingularToSource f L s ∣_ U).fiber z ⟶ Spec (.of (MvPolynomial I k)) :=
  (bertiniSingularToSource f L s ∣_ U).fiberι z ≫
    ((bertiniSingularToSource f L s) ⁻¹ᵁ U).ι ≫
    (bertiniSingularIdeal f L s).subschemeι ≫ bertiniUniversalProjection f L s

/-- The coefficient and residue-field projections of the singular fibre agree over `k`.
Source: Stacks Project, Tag 0FD6, the universal-family diagram.
(blueprint: lem-zl-bertini-singular-fibre-coordinates). -/
theorem bertini_singular_fibre_coefficient_fac
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    bertiniSingularFibreCoefficient f L s U z ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)) =
      (bertiniSingularToSource f L s ∣_ U).fiberToSpecResidueField z ≫
        Spec.map (CommRingCat.ofHom ((U.ι ≫ f).residueFieldAlgebraMap z)) := by
  rw [Scheme.Hom.specMap_residueFieldAlgebraMap, ← Category.assoc,
    ← Scheme.Hom.fiber_fac]
  simp only [Category.assoc, morphismRestrict_ι_assoc]
  simp only [bertiniSingularFibreCoefficient, bertiniUniversalProjection,
    bertiniSingularToSource, Category.assoc, pullback.condition]

/-- The canonical map of the singular fibre into polynomial affine space over its residue field.
It is the unique lift of the two actual projections, rather than an existentially chosen model.
Source: Stacks Project, Tag 0FD6, base change of the universal-family diagram.
(blueprint: lem-zl-bertini-singular-fibre-coordinates). -/
noncomputable def bertiniSingularFibreCoordinates
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    (bertiniSingularToSource f L s ∣_ U).fiber z ⟶
      Spec (.of (MvPolynomial I ((U : Scheme).residueField z))) :=
  (bertini_polynomial_baseChange_square ((U.ι ≫ f).residueFieldAlgebraMap z) I).lift
    (bertiniSingularFibreCoefficient f L s U z)
    ((bertiniSingularToSource f L s ∣_ U).fiberToSpecResidueField z)
    (bertini_singular_fibre_coefficient_fac f L s U z)

/-- The actual polynomial coordinate homomorphism on the singular fibre.
Source: Stacks Project, Tag 0FD6, affine coordinates of the fibre.
(blueprint: lem-zl-bertini-singular-fibre-coordinates). -/
noncomputable def bertiniSingularFibreRingMap
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    MvPolynomial I ((U : Scheme).residueField z) →+*
      Γ((bertiniSingularToSource f L s ∣_ U).fiber z, ⊤) :=
  ((Scheme.ΓSpecIso (.of (MvPolynomial I ((U : Scheme).residueField z)))).inv ≫
    (bertiniSingularFibreCoordinates f L s U z).appTop).hom

end AlgebraicGeometry
