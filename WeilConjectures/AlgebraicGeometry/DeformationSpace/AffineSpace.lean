/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# The deformation to the normal cone of the zero section of affine space

For the standard pair `(𝔸^n_B ⟶ B, 0)`, the deformation space of the zero section is
`𝔸^n_{𝔸¹_B} = 𝔸^n_B ×_B 𝔸¹_B`, with coordinates `u_k = x_k / t`, so that `x_k = t u_k`. This is
blueprint `sk-lem-geometry` (4).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.deformationSpaceToAffineSpace`: the morphism
  `D_0 𝔸^n_B ⟶ 𝔸^n_{𝔸¹_B}`
  given by the coordinates `u_k = x_k t⁻¹`.
-/

@[expose] public section

universe u

open CategoryTheory Limits LaurentPolynomial

namespace AlgebraicGeometry.Scheme.Hom

open AffineZariskiSite

variable (n : Type u) (B : Scheme.{u})

/-- The coordinate `x_k` of `𝔸^n_B`, restricted to an affine open. -/
noncomputable def coordRes (U : (𝔸(n; B)).AffineZariskiSite) (k : n) : Γ(𝔸(n; B), U.1) :=
  (𝔸(n; B)).presheaf.map (homOfLE le_top).op (AffineSpace.coord B k)

lemma coordRes_mem (U : (𝔸(n; B)).AffineZariskiSite) (k : n) :
    coordRes n B U k ∈ (AffineSpace.zeroSection n B).ker.siteIdeal U := by
  rw [IdealSheafData.siteIdeal, Scheme.Hom.ker_apply, RingHom.mem_ker, coordRes,
    ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  change (B.presheaf.map _).hom ((AffineSpace.zeroSection n B).appTop _) = 0
  rw [AffineSpace.zeroSection_appTop_coord, map_zero]

/-- The coordinate `u_k = x_k t⁻¹` on the chart of the deformation space over `U`. -/
noncomputable def uCoord (U : (𝔸(n; B)).AffineZariskiSite) (k : n) :
    (AffineSpace.zeroSection n B).ker.reesPresheaf.obj (.op U) :=
  ⟨LaurentPolynomial.C (coordRes n B U k) * T (-1),
    Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (coordRes_mem n B U k)⟩

lemma map_uCoord {U U' : (𝔸(n; B)).AffineZariskiSite} (i : U ⟶ U') (k : n) :
    ((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op).hom (uCoord n B U' k) =
      uCoord n B U k := by
  apply Subtype.ext
  change Ideal.laurentMap _ (LaurentPolynomial.C (coordRes n B U' k) * T (-1)) =
    LaurentPolynomial.C (coordRes n B U k) * T (-1)
  rw [map_mul, Ideal.laurentMap_C, Ideal.laurentMap_T]
  congr 2
  change ((𝔸(n; B)).presheaf.map _ ≫ (𝔸(n; B)).presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

/-- The chart `Spec Γ(U)[t, I t⁻¹] ⟶ 𝔸^n_{𝔸¹_B}` of the coordinates `u_k = x_k t⁻¹`. -/
noncomputable def deformationSpaceToAffineSpaceChart (U : (𝔸(n; B)).AffineZariskiSite) :
    (relativeGluingData (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor.obj
      U ⟶ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) :=
  AffineSpace.homOfVector
    (colimit.ι (relativeGluingData
      (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor U ≫
      deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))
    fun k ↦ (ΓSpecIso _).inv (uCoord n B U k)

set_option backward.isDefEq.respectTransparency false in
lemma map_comp_deformationSpaceToAffineSpaceChart {U U' : (𝔸(n; B)).AffineZariskiSite}
    (i : U ⟶ U') :
    (relativeGluingData (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor.map
      i ≫ deformationSpaceToAffineSpaceChart n B U' = deformationSpaceToAffineSpaceChart n B U := by
  rw [deformationSpaceToAffineSpaceChart, deformationSpaceToAffineSpaceChart,
    AffineSpace.comp_homOfVector, ← Category.assoc, colimit.w]
  congr 1
  funext k
  have h := congr($(Scheme.ΓSpecIso_inv_naturality
    ((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op)) (uCoord n B U' k))
  refine h.symm.trans ?_
  change (ΓSpecIso _).inv (((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op).hom
    (uCoord n B U' k)) = _
  rw [map_uCoord]
  rfl

/-- **The standard pair.** The morphism `D_0 𝔸^n_B ⟶ 𝔸^n_{𝔸¹_B}` from the deformation space of
the zero section, given by the coordinates `u_k = x_k t⁻¹` over `𝔸¹_B`. -/
noncomputable def deformationSpaceToAffineSpace :
    (AffineSpace.zeroSection n B).ker.deformationSpace ⟶ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) :=
  colimit.desc _
    { pt := _
      ι := { app U := deformationSpaceToAffineSpaceChart n B U
             naturality _ _ i := (map_comp_deformationSpaceToAffineSpaceChart n B i).trans
              (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
lemma ι_deformationSpaceToAffineSpace (U : (𝔸(n; B)).AffineZariskiSite) :
    colimit.ι (relativeGluingData
      (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor U ≫
      deformationSpaceToAffineSpace n B = deformationSpaceToAffineSpaceChart n B U :=
  colimit.ι_desc _ _

@[reassoc (attr := simp)]
lemma deformationSpaceToAffineSpace_over :
    deformationSpaceToAffineSpace n B ≫ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) ↘ _ =
      deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B) :=
  colimit.hom_ext fun U ↦ by
    rw [ι_deformationSpaceToAffineSpace_assoc, deformationSpaceToAffineSpaceChart,
      AffineSpace.homOfVector_over]

set_option backward.isDefEq.respectTransparency false in
lemma reesToQuotientPolynomial_comp_deformationSpaceToAffineSpace :
    relativeGluingMap (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf
      (AffineSpace.zeroSection n B).ker.coequifibered_toQuotientPolynomialAlgebra
      (AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial ≫
        deformationSpaceToAffineSpace n B =
      (relativeGluingMap (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf
        (AffineSpace.zeroSection n B).ker.coequifibered_toQuotientPolynomialAlgebra
        (AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial ≫
          deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B)) ≫
        AffineSpace.zeroSection n _ := by
  refine colimit.hom_ext fun U ↦ AffineSpace.hom_ext ?_ fun k ↦ ?_
  · simp only [Category.assoc, deformationSpaceToAffineSpace_over, AffineSpace.zeroSection_over,
      Category.comp_id]
  · conv_rhs => simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.zeroSection_appTop_coord, map_zero]
    rw [ι_relativeGluingMap_assoc, ι_deformationSpaceToAffineSpace,
      deformationSpaceToAffineSpaceChart, AffineSpace.comp_homOfVector,
      AffineSpace.homOfVector_appTop_coord, Function.comp_apply]
    have h := congr($(Scheme.ΓSpecIso_inv_naturality
      ((AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial.app (.op U))) (uCoord n B U k))
    refine h.symm.trans ?_
    change (ΓSpecIso ((AffineSpace.zeroSection n B).ker.quotientPolynomialAlgebra.obj (.op U))).inv
      (Ideal.extendedReesAlgebraToPolynomial _ _ Ideal.mk_ker.ge
      ⟨_, Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (coordRes_mem n B U k)⟩) = 0
    exact (congrArg _ (Ideal.extendedReesAlgebraToPolynomial_C_mul_T_neg_one
      (I := (AffineSpace.zeroSection n B).ker.siteIdeal U) _ Ideal.mk_ker.ge
      (coordRes_mem n B U k))).trans (map_zero _)

/-- The section `s̃` of the deformation space of the zero section is the zero section of
`𝔸^n_{𝔸¹_B}` in the coordinates `u_k`. -/
lemma deformationSpaceSection_comp_deformationSpaceToAffineSpace :
    (AffineSpace.zeroSection n B).deformationSpaceSection ≫ deformationSpaceToAffineSpace n B =
      AffineSpace.zeroSection n _ := by
  rw [deformationSpaceSection, Category.assoc,
    reesToQuotientPolynomial_comp_deformationSpaceToAffineSpace, ← Category.assoc,
    ← Category.assoc, ← deformationSpaceSection,
    deformationSpaceSection_deformationSpaceProj (AffineSpace.zeroSection_over n B),
    Category.id_comp]

end AlgebraicGeometry.Scheme.Hom
