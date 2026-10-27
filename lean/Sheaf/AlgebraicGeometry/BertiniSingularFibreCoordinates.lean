/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
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

@[reassoc (attr := simp)]
theorem bertiniSingularFibreCoordinates_map
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    bertiniSingularFibreCoordinates f L s U z ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.map (σ := I) ((U.ι ≫ f).residueFieldAlgebraMap z))) =
      bertiniSingularFibreCoefficient f L s U z :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem bertiniSingularFibreCoordinates_C
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    bertiniSingularFibreCoordinates f L s U z ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : (U : Scheme).residueField z →+*
            MvPolynomial I ((U : Scheme).residueField z))) =
      (bertiniSingularToSource f L s ∣_ U).fiberToSpecResidueField z :=
  IsPullback.lift_snd _ _ _ _

/-- The actual singular fibre is a closed subscheme of coefficient affine space over `κ(z)`.
Source: Stacks Project, Tags 0FD6 and 01J9: compose the two closed inclusions, then base change.
(blueprint: lem-zl-bertini-singular-fibre-coordinates). -/
theorem bertini_singular_fibre_coordinates_isClosedImmersion
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    IsClosedImmersion (bertiniSingularFibreCoordinates f L s U z) := by
  let c := Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))
  let cK := Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : (U : Scheme).residueField z →+*
      MvPolynomial I ((U : Scheme).residueField z)))
  let m := Spec.map (CommRingCat.ofHom
    (MvPolynomial.map (σ := I) ((U.ι ≫ f).residueFieldAlgebraMap z)))
  let β := (U : Scheme).fromSpecResidueField z ≫ U.ι
  let i := (bertiniSingularIdeal f L s).subschemeι ≫
    (bertiniUniversalIdeal f L s).subschemeι
  let p := bertiniSingularToSource f L s
  let t := (p ∣_ U).fiberι z ≫ (p ⁻¹ᵁ U).ι
  let h := bertiniSingularFibreCoordinates f L s U z
  have hbase : IsPullback m cK c (β ≫ f) := by
    simpa only [β, Category.assoc, ← Scheme.Hom.specMap_residueFieldAlgebraMap] using
      bertini_polynomial_baseChange_square ((U.ι ≫ f).residueFieldAlgebraMap z) I
  let a : Spec (.of (MvPolynomial I ((U : Scheme).residueField z))) ⟶ pullback c f :=
    pullback.lift m (cK ≫ β) (by simpa only [Category.assoc] using hbase.w)
  have ha : IsPullback a cK (pullback.snd c f) β := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback c f)
    · simpa only [a, pullback.lift_fst] using hbase
    · exact pullback.lift_snd _ _ _
  have ht : IsPullback t ((p ∣_ U).fiberToSpecResidueField z) p β :=
    (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_morphismRestrict p U).flip
  have hhC : h ≫ cK = (p ∣_ U).fiberToSpecResidueField z :=
    bertiniSingularFibreCoordinates_C f L s U z
  have hip : i ≫ pullback.snd c f = p := by
    simp only [i, p, c, bertiniSingularToSource, Category.assoc]
  have hti : t ≫ i = h ≫ a := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [show a ≫ pullback.fst c f = m from pullback.lift_fst _ _ _]
      exact (bertiniSingularFibreCoordinates_map f L s U z).symm
    · simp only [Category.assoc]
      rw [show a ≫ pullback.snd c f = cK ≫ β from pullback.lift_snd _ _ _]
      rw [← Category.assoc h cK β, hhC]
      simpa only [i, p, c, bertiniSingularToSource, Category.assoc] using ht.w
  have htop : IsPullback t h i a := by
    apply IsPullback.of_bot (t := ha)
    · rw [hhC, hip]
      exact ht
    · exact hti
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback htop
    (inferInstance : IsClosedImmersion i)

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

/-- The coordinate homomorphism is surjective since the coordinate map is a closed immersion.
Source: Stacks Project, Tags 0FD6 and 01QN.
(blueprint: lem-zl-bertini-singular-fibre-coordinates). -/
theorem bertini_singular_fibre_ringMap_surjective
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    Function.Surjective (bertiniSingularFibreRingMap f L s U z) := by
  have := bertini_singular_fibre_coordinates_isClosedImmersion f L s U z
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    (bertiniSingularFibreCoordinates f L s U z)).2.comp
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective

/-- Affine reconstruction of the coordinate map from its actual ring homomorphism.
Source: Stacks Project, Tag 01I1, applied to the coordinate morphism of Tag 0FD6.
(blueprint: lem-zl-bertini-singular-fibre-coordinates). -/
theorem bertini_singular_fibre_ringMap_spec
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (U : Y.Opens) (z : U) :
    ((bertiniSingularToSource f L s ∣_ U).fiber z).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (bertiniSingularFibreRingMap f L s U z)) =
      bertiniSingularFibreCoordinates f L s U z := by
  change _ ≫ Spec.map ((Scheme.ΓSpecIso _).inv ≫
    (bertiniSingularFibreCoordinates f L s U z).appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end AlgebraicGeometry
