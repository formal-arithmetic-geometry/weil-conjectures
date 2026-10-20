/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import Sheaf.AlgebraicGeometry.BertiniUniversalBaseChange
import Sheaf.AlgebraicGeometry.BertiniTrivializedZeroIdeal
import Sheaf.AlgebraicGeometry.BertiniAffineAmbient
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Polynomial quotient charts for the universal incidence scheme

Source: Stacks Project, More on Morphisms, Tag 0G4F, affine incidence charts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme.Modules

private noncomputable def affineSubschemeIso {X : Scheme.{u}} [IsAffine X]
    (J : X.IdealSheafData) :
    J.subscheme ≅ Spec (.of (Γ(X, ⊤) ⧸ J.ideal ⟨⊤, isAffineOpen_top X⟩)) := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have h : Surjective (J.subschemeCover.f U) := by
    constructor
    intro x
    have hx : x ∈ (J.subschemeCover.f U).opensRange := by
      rw [J.opensRange_subschemeCover_map]
      exact Set.mem_univ x
    exact hx
  have : IsIso (J.subschemeCover.f U) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, h⟩
  exact (asIso (J.subschemeCover.f U)).symm

private theorem affineSubschemeIso_inv_ι {X : Scheme.{u}} [IsAffine X]
    (J : X.IdealSheafData) :
    (affineSubschemeIso J).inv ≫ J.subschemeι =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩))) ≫ X.isoSpec.inv := by
  change J.subschemeCover.f ⟨⊤, isAffineOpen_top X⟩ ≫ J.subschemeι = _
  rw [J.subschemeCover_map_subschemeι, J.glueDataObjι_ι]
  congr 1
  exact IsAffineOpen.fromSpec_top

/-- On an affine scheme with a chosen generator of its line bundle, the universal incidence
scheme is isomorphic to the spectrum of the expected polynomial quotient. The inverse
isomorphism carries the universal projection to the coefficient-change quotient map.

Source: Stacks Project, More on Morphisms, Tag 0G4F, affine incidence presentation.
(blueprint: lem-zl-bertini-affine-incidence-chart).

Proof: Identify the ambient product with Spec A[x_i] by the polynomial tensor-product
pushout. Pull back the universal ideal through this isomorphism. The tensor-unit coefficient
formula identifies its ideal of global sections with the principal incidence equation,
transported by the canonical global-sections isomorphism. The affine closed subscheme is
Spec of this quotient. Transport the quotient through the global-sections isomorphism and
the ambient isomorphism. The affine cover inclusion and quotient-map identities identify
the projection to coefficient space. No irreducibility or reducedness is assumed. -/
theorem exists_bertiniAffineIncidenceChart
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (L : (Spec (.of A)).Modules) [L.IsInvertible]
    {e : Γ(L, ⊤)} (he : IsFreeGenerator e)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    ∃ e : (bertiniUniversalIdeal
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) L s).subscheme ≅
        Spec (.of (MvPolynomial I A ⧸ Ideal.span
          {∑ i, MvPolynomial.C ((Scheme.ΓSpecIso (.of A)).hom (he.coeff (s i))) *
            MvPolynomial.X i})),
      e.inv ≫ bertiniUniversalProjection
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) L s =
        Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap k A)))) := by
  classical
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let P := MvPolynomial I A
  let B := pullback (Spec.map
    (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f
  let hp := isPullback_bertiniAffineAmbient k A I
  let g : Spec (.of P) ⟶ B := hp.isoPullback.hom
  have hg₁ : g ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := I) (algebraMap k A))) :=
    hp.isoPullback_hom_fst
  have hg₂ : g ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : A →+* P)) :=
    hp.isoPullback_hom_snd
  let J := (bertiniUniversalIdeal f L s).comap g
  let F : P := ∑ i, MvPolynomial.C ((Scheme.ΓSpecIso (.of A)).hom
    (he.coeff (s i))) * MvPolynomial.X i
  have hJ : J.ideal ⟨⊤, isAffineOpen_top (Spec (.of P))⟩ =
      Ideal.span {(Scheme.ΓSpecIso (.of P)).inv F} := by
    dsimp only [J]
    rw [bertiniUniversalIdeal_comap]
    rw [ideal_zeroLocus_tensorSectionsUnit_sum _ L he]
    congr 1
    apply congrArg Set.singleton
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hg₁, hg₂, Scheme.specMap_appTop_ΓSpecIso_inv]
    simp only [CommRingCat.hom_ofHom, MvPolynomial.map_X]
    have hc : (Spec.map (CommRingCat.ofHom (MvPolynomial.C : A →+* P))).appTop
        (he.coeff (s i)) = (Scheme.ΓSpecIso (.of P)).inv
          (MvPolynomial.C ((Scheme.ΓSpecIso (.of A)).hom (he.coeff (s i)))) := by
      have h := Scheme.specMap_appTop_ΓSpecIso_inv
        (CommRingCat.ofHom (MvPolynomial.C : A →+* P))
        ((Scheme.ΓSpecIso (.of A)).hom (he.coeff (s i)))
      simpa using h
    rw [hc, ← map_mul, mul_comm]
  have hK : Ideal.span {F} =
      (J.ideal ⟨⊤, isAffineOpen_top (Spec (.of P))⟩).map
        (Scheme.ΓSpecIso (.of P)).hom.hom := by
    rw [hJ, Ideal.map_span, Set.image_singleton]
    simp
  let eqv := Ideal.quotientEquiv _ _
    (Scheme.ΓSpecIso (.of P)).commRingCatIsoToRingEquiv hK
  let eJ := affineSubschemeIso J ≪≫
    Scheme.Spec.mapIso eqv.toCommRingCatIso.symm.op
  have hg : IsIso g := by dsimp only [g]; infer_instance
  let j : J.subscheme ⟶ (bertiniUniversalIdeal f L s).subscheme :=
    ((bertiniUniversalIdeal f L s).comapIso g).hom ≫
      pullback.snd g (bertiniUniversalIdeal f L s).subschemeι
  have : IsIso j := by dsimp only [j]; infer_instance
  refine ⟨(asIso j).symm ≪≫ eJ, ?_⟩
  have hj : j ≫ (bertiniUniversalIdeal f L s).subschemeι = J.subschemeι ≫ g := by
    dsimp only [j]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  change eJ.inv ≫ j ≫ (bertiniUniversalIdeal f L s).subschemeι ≫
    pullback.fst _ _ = _
  rw [← Category.assoc j, hj]
  change (Spec.map eqv.toCommRingCatIso.hom ≫ (affineSubschemeIso J).inv) ≫
    J.subschemeι ≫ g ≫ pullback.fst _ _ = _
  rw [Category.assoc, ← Category.assoc (affineSubschemeIso J).inv,
    affineSubschemeIso_inv_ι, Scheme.isoSpec_Spec_inv]
  have hring : (Scheme.ΓSpecIso (.of P)).inv ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top _⟩)) ≫
      eqv.toCommRingCatIso.hom = CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {F})) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change (Ideal.Quotient.mk (Ideal.span {F}))
      ((Scheme.ΓSpecIso (.of P)).hom ((Scheme.ΓSpecIso (.of P)).inv p)) = _
    simp
  have hs : Spec.map eqv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (J.ideal ⟨⊤, isAffineOpen_top _⟩))) ≫
      Spec.map (Scheme.ΓSpecIso (.of P)).inv =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {F}))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc, hring]
  simp only [← Category.assoc] at hs ⊢
  rw [hs]
  rw [Category.assoc, hg₁, ← Spec.map_comp]
  rfl

end AlgebraicGeometry
