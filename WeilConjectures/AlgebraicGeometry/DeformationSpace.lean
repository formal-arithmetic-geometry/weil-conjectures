/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.PolynomialAlgebra
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
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

- `AlgebraicGeometry.Scheme.affineLine`: the relative affine line `Spec_X 𝒪_X[t]`.
- `AlgebraicGeometry.Scheme.IdealSheafData.deformationSpace`: the deformation space `D_I X`,
  with its morphism `deformationSpaceToAffineLine` to the relative affine line.
- `AlgebraicGeometry.Scheme.IdealSheafData.normalCone`: the normal cone `N_I X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial LaurentPolynomial

/-! ### Polynomial and Laurent polynomial functors -/

namespace CommRingCat

/-- The functor `R ↦ R[t]`. -/
@[simps]
noncomputable def polynomialFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of R[X]
  map f := ofHom (mapRingHom f.hom)
  map_id R := by ext : 1; exact mapRingHom_id
  map_comp f g := by ext : 1; exact (mapRingHom_comp _ _).symm

/-- The inclusion of constants `R ⟶ R[t]`. -/
@[simps]
noncomputable def polynomialC : 𝟭 CommRingCat.{u} ⟶ polynomialFunctor where
  app R := ofHom C
  naturality _ _ f := by ext : 1; exact (mapRingHom_comp_C _).symm

lemma coequifibered_polynomialC : polynomialC.{u}.Coequifibered := by
  intro R S f
  algebraize [f.hom]
  let := Polynomial.algebra (R := R) (A := S)
  exact CommRingCat.isPushout_of_isPushout R S R[X] S[X]

/-- The functor `R ↦ R[t, t⁻¹]`. -/
@[simps]
noncomputable def laurentFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of R[T;T⁻¹]
  map f := ofHom (Ideal.laurentMap f.hom)
  map_id R := by ext : 1; exact AddMonoidAlgebra.mapRingHom_id
  map_comp f g := by ext : 1; exact AddMonoidAlgebra.mapRingHom_comp _ _

/-- The inclusion of constants `R ⟶ R[t, t⁻¹]`. -/
@[simps]
noncomputable def laurentC : 𝟭 CommRingCat.{u} ⟶ laurentFunctor where
  app R := ofHom LaurentPolynomial.C
  naturality _ _ f := by
    ext x
    exact (Ideal.laurentMap_C f.hom x).symm

open scoped AlgebraMonoidAlgebra in
lemma coequifibered_laurentC : laurentC.{u}.Coequifibered := by
  intro R S f
  algebraize [f.hom]
  exact CommRingCat.isPushout_of_isPushout R S R[T;T⁻¹] S[T;T⁻¹]

/-- The inclusion `R[t] ⟶ R[t, t⁻¹]`. -/
@[simps]
noncomputable def polynomialToLaurent : polynomialFunctor.{u} ⟶ laurentFunctor where
  app R := ofHom toLaurent
  naturality _ _ f := by
    ext p
    exact (Ideal.laurentMap_toLaurent f.hom p).symm

end CommRingCat

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

include h𝔞 in
lemma coequifibered_toQuotientPresheaf : (toQuotientPresheaf 𝔞 h𝔞).Coequifibered := by
  intro U V i
  have e : 𝔞 V = (𝔞 U).map (F.map i).hom := (h𝔞 i).symm
  refine (CommRingCat.isPushout_quotient (F.map i) (𝔞 U)).flip.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Ideal.quotEquivOfEq e.symm).toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp
  · ext x; rfl
  · ext x
    rfl

include H in
lemma coequifibered_comp_toQuotientPresheaf : (α ≫ toQuotientPresheaf 𝔞 h𝔞).Coequifibered :=
  NatTrans.Coequifibered.comp H (coequifibered_toQuotientPresheaf 𝔞 h𝔞)

end Quotient

/-! ### The relative affine line -/

/-- The quasi-coherent algebra `𝒪_X[t]`. -/
noncomputable abbrev polynomialPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  X.affineStructurePresheaf ⋙ CommRingCat.polynomialFunctor

/-- The structure map `𝒪_X ⟶ 𝒪_X[t]`. -/
noncomputable abbrev toPolynomialPresheaf : X.affineStructurePresheaf ⟶ X.polynomialPresheaf :=
  X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialC

lemma coequifibered_toPolynomialPresheaf : X.toPolynomialPresheaf.Coequifibered :=
  CommRingCat.coequifibered_polynomialC.whiskerLeft _

/-- The quasi-coherent algebra `𝒪_X[t, t⁻¹]`. -/
noncomputable abbrev laurentPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  X.affineStructurePresheaf ⋙ CommRingCat.laurentFunctor

/-- The structure map `𝒪_X ⟶ 𝒪_X[t, t⁻¹]`. -/
noncomputable abbrev toLaurentPresheaf : X.affineStructurePresheaf ⟶ X.laurentPresheaf :=
  X.affineStructurePresheaf.whiskerLeft CommRingCat.laurentC

lemma coequifibered_toLaurentPresheaf : X.toLaurentPresheaf.Coequifibered :=
  CommRingCat.coequifibered_laurentC.whiskerLeft _

/-- The relative affine line `𝔸¹_X = Spec_X 𝒪_X[t]`. -/
noncomputable abbrev affineLine : Scheme.{u} :=
  (relativeGluingData X.coequifibered_toPolynomialPresheaf).glued

/-- The projection `𝔸¹_X ⟶ X`. -/
noncomputable abbrev affineLineProj : X.affineLine ⟶ X :=
  (relativeGluingData X.coequifibered_toPolynomialPresheaf).toBase

/-- The punctured relative affine line `𝔾_{m,X} = Spec_X 𝒪_X[t, t⁻¹]`. -/
noncomputable abbrev punctured : Scheme.{u} :=
  (relativeGluingData X.coequifibered_toLaurentPresheaf).glued

/-- The inclusion `𝔾_{m,X} ⟶ 𝔸¹_X`. -/
noncomputable def puncturedToAffineLine : X.punctured ⟶ X.affineLine :=
  relativeGluingMap _ _ (X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialToLaurent)

end AlgebraicGeometry.Scheme
