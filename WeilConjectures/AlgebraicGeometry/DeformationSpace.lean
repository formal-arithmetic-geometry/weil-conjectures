/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.PolynomialAlgebra
public import WeilConjectures.Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra

/-!
# The deformation space of a closed subscheme

For a quasi-coherent ideal `I` of a scheme `X`, the *deformation space* is the relative spectrum

`D_I X = Spec_X (⨁_{n ∈ ℤ} I^{-n} tⁿ)`

of the extended Rees algebra `𝒪_X[t, I t⁻¹]` (with `I^m = 𝒪_X` for `m ≤ 0`). It lies over the
relative affine line `Spec_X 𝒪_X[t]`. Inverting `t` gives `𝒪_X[t, t⁻¹]`, so over the punctured
line the deformation space is trivial, and setting `t = 0` gives the *normal cone*

`N_I X = Spec_X (𝒪_X[t, I t⁻¹] / t) = Spec_X (⨁_{r ≥ 0} I^r / I^{r+1})`.

This is the deformation to the normal cone `Bl_{V(I) × 0} (X × 𝔸¹) ∖ (strict transform of X × 0)`
of `V(I) ⊆ X`, in its Rees-algebra form.

All the schemes here are relative spectra of quasi-coherent `𝒪_X`-algebras, given on the affine
opens of `X` (`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`), and the relations
between them come from pushout squares of algebras through
`AlgebraicGeometry.Scheme.AffineZariskiSite.isPullback_relativeGluingMap`.

## Main definitions

- `AlgebraicGeometry.Scheme.polynomialSpec`: the relative affine line `Spec_X 𝒪_X[t]`.
- `AlgebraicGeometry.Scheme.IdealSheafData.deformationSpace`: the deformation space `D_I X`,
  with its morphism `deformationSpaceToPolynomialSpec` to the relative affine line.
- `AlgebraicGeometry.Scheme.IdealSheafData.normalCone`: the normal cone `N_I X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial LaurentPolynomial

namespace AlgebraicGeometry.Scheme

open AffineZariskiSite

variable (X : Scheme.{u})

/-- The structure sheaf of `X` on its affine opens. -/
abbrev affineStructurePresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  (toOpensFunctor X).op ⋙ X.presheaf

/-! ### Quotients of quasi-coherent algebras -/

section Quotient

variable {X} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : X.affineStructurePresheaf ⟶ F} (H : α.Coequifibered)
  (𝔞 : ∀ U, Ideal (F.obj U))
  (h𝔞 : ∀ ⦃U V⦄ (i : U ⟶ V), (𝔞 U).map (F.map i).hom = 𝔞 V)

include h𝔞 in
lemma le_comap_quotientPresheaf ⦃U V⦄ (i : U ⟶ V) : 𝔞 U ≤ (𝔞 V).comap (F.map i).hom := by
  rw [← Ideal.map_le_iff_le_comap, h𝔞]

/-- The quotient of a presheaf of rings `F` by a compatible family of ideals `𝔞`. -/
@[simps]
noncomputable def quotientPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of (F.obj U ⧸ 𝔞 U)
  map {U V} i := CommRingCat.ofHom
    (Ideal.quotientMap (𝔞 V) (F.map i).hom (le_comap_quotientPresheaf 𝔞 h𝔞 i))
  map_id U := by
    ext x
    simp
  map_comp i j := by
    ext x
    simp

/-- The quotient map `F ⟶ F / 𝔞`. -/
@[simps]
noncomputable def toQuotientPresheaf : F ⟶ quotientPresheaf 𝔞 h𝔞 where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (𝔞 U))
  naturality U V i := by
    ext x
    exact (Ideal.quotientMap_mk (f := (F.map i).hom) (H := le_comap_quotientPresheaf 𝔞 h𝔞 i)
      (x := x)).symm

end Quotient

/-! ### The relative affine line -/

/-! ### The deformation space and the normal cone -/

namespace IdealSheafData

variable {X} (I : X.IdealSheafData)

/-- The ideal `I(U)` over an affine open `U`, indexed by the small affine Zariski site. -/
abbrev siteIdeal (U : X.AffineZariskiSite) : Ideal Γ(X, U.1) :=
  I.ideal ⟨U.1, U.2⟩

lemma map_siteIdeal ⦃U V : X.AffineZariskiSiteᵒᵖ⦄ (i : U ⟶ V) :
    (I.siteIdeal U.unop).map (X.affineStructurePresheaf.map i).hom = I.siteIdeal V.unop :=
  I.map_ideal' (U := ⟨V.unop.1, V.unop.2⟩) (V := ⟨U.unop.1, U.unop.2⟩) _

/-- The extended Rees algebra `𝒪_X[t, I t⁻¹]` as a quasi-coherent algebra. -/
@[simps]
noncomputable def reesPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of (I.siteIdeal U.unop).extendedReesAlgebra
  map {U V} i := CommRingCat.ofHom <| (I.siteIdeal U.unop).extendedReesAlgebraMap
    (X.affineStructurePresheaf.map i).hom _ (I.map_siteIdeal i).le
  map_id U := CommRingCat.hom_ext <| RingHom.ext fun x ↦ Subtype.ext <| by
    change LaurentPolynomial.mapRingHom (X.affineStructurePresheaf.map (𝟙 U)).hom x.1 = x.1
    rw [CategoryTheory.Functor.map_id, CommRingCat.hom_id]
    exact LaurentPolynomial.mapRingHom_id _
  map_comp i j := CommRingCat.hom_ext <| RingHom.ext fun x ↦ Subtype.ext <| by
    change LaurentPolynomial.mapRingHom (X.affineStructurePresheaf.map (i ≫ j)).hom x.1 =
      LaurentPolynomial.mapRingHom (X.affineStructurePresheaf.map j).hom
        (LaurentPolynomial.mapRingHom (X.affineStructurePresheaf.map i).hom x.1)
    rw [CategoryTheory.Functor.map_comp, CommRingCat.hom_comp]
    exact (LaurentPolynomial.mapRingHom_mapRingHom _ _ _).symm

/-- The structure map `𝒪_X ⟶ 𝒪_X[t, I t⁻¹]`. -/
@[simps]
noncomputable def toReesPresheaf : X.affineStructurePresheaf ⟶ I.reesPresheaf where
  app _ := CommRingCat.ofHom (algebraMap _ _)
  naturality _ _ i := CommRingCat.hom_ext (RingHom.ext fun x ↦
    (Ideal.extendedReesAlgebraMap_algebraMap _ _ (I.map_siteIdeal i).le x).symm)

/-! ### The closed subscheme and its relative affine line -/

/-! ### The fibres of the deformation space -/

end IdealSheafData

/-! ### The relative affine line is the affine line -/

/-! ### The zero section -/

/-! ### The punctured line -/

/-! ### The relative spectrum of `𝒪_X` -/

namespace IdealSheafData

variable {X} (I : X.IdealSheafData)

end IdealSheafData

end AlgebraicGeometry.Scheme
