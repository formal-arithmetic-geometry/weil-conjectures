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

/-- The zero section of `𝔸¹_X` as a quasi-coherent algebra: `𝒪_X[t] / t`. -/
noncomputable abbrev polynomialZeroPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  quotientPresheaf (F := X.polynomialPresheaf) (fun _ ↦ Ideal.span {Polynomial.X}) fun U V i ↦ by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p ↦ Ideal.span {p}) (Polynomial.map_X _)

lemma coequifibered_toPolynomialZeroPresheaf : (X.toPolynomialPresheaf ≫
    toQuotientPresheaf _ _ : _ ⟶ X.polynomialZeroPresheaf).Coequifibered :=
  coequifibered_comp_toQuotientPresheaf X.coequifibered_toPolynomialPresheaf _ _

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
    change Ideal.laurentMap (X.affineStructurePresheaf.map (𝟙 U)).hom x.1 = x.1
    rw [CategoryTheory.Functor.map_id, CommRingCat.hom_id]
    exact Ideal.laurentMap_id _
  map_comp i j := CommRingCat.hom_ext <| RingHom.ext fun x ↦ Subtype.ext <| by
    change Ideal.laurentMap (X.affineStructurePresheaf.map (i ≫ j)).hom x.1 =
      Ideal.laurentMap (X.affineStructurePresheaf.map j).hom
        (Ideal.laurentMap (X.affineStructurePresheaf.map i).hom x.1)
    rw [CategoryTheory.Functor.map_comp, CommRingCat.hom_comp]
    exact (Ideal.laurentMap_laurentMap _ _ _).symm

/-- The structure map `𝒪_X ⟶ 𝒪_X[t, I t⁻¹]`. -/
@[simps]
noncomputable def toReesPresheaf : X.affineStructurePresheaf ⟶ I.reesPresheaf where
  app U := CommRingCat.ofHom (algebraMap _ _)
  naturality U V i := CommRingCat.hom_ext (RingHom.ext fun x ↦
    (Ideal.extendedReesAlgebraMap_algebraMap _ _ (I.map_siteIdeal i).le x).symm)

set_option backward.isDefEq.respectTransparency false in
lemma coequifibered_toReesPresheaf : I.toReesPresheaf.Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U f ↦ ?_
  have := U.2.isLocalization_basicOpen f
  exact Ideal.isLocalization_away_extendedReesAlgebraMap _ f this _
    (I.map_ideal_basicOpen ⟨U.1, U.2⟩ f)

/-- The deformation space `D_I X = Spec_X 𝒪_X[t, I t⁻¹]`. -/
noncomputable abbrev deformationSpace : Scheme.{u} :=
  (relativeGluingData I.coequifibered_toReesPresheaf).glued

/-- The structure morphism `D_I X ⟶ X`. -/
noncomputable abbrev deformationSpaceProj : I.deformationSpace ⟶ X :=
  (relativeGluingData I.coequifibered_toReesPresheaf).toBase

/-- The inclusion `𝒪_X[t] ⟶ 𝒪_X[t, I t⁻¹]`. -/
@[simps]
noncomputable def polynomialToRees : X.polynomialPresheaf ⟶ I.reesPresheaf where
  app U := CommRingCat.ofHom (I.siteIdeal U.unop).toExtendedReesAlgebra
  naturality U V i := by
    refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    exact congr($(Ideal.extendedReesAlgebraMap_comp_toExtendedReesAlgebra _ _
      (I.map_siteIdeal i).le) p).symm

lemma toPolynomialPresheaf_comp_polynomialToRees :
    X.toPolynomialPresheaf ≫ I.polynomialToRees = I.toReesPresheaf := by
  ext U x
  exact Ideal.toExtendedReesAlgebra_C x

/-- The morphism `g̃ : D_I X ⟶ 𝔸¹_X` given by the coordinate `t`. -/
noncomputable def deformationSpaceToAffineLine : I.deformationSpace ⟶ X.affineLine :=
  relativeGluingMap _ _ I.polynomialToRees

/-- The inclusion `𝒪_X[t, I t⁻¹] ⟶ 𝒪_X[t, t⁻¹]`. -/
@[simps]
noncomputable def reesToLaurent : I.reesPresheaf ⟶ X.laurentPresheaf where
  app U := CommRingCat.ofHom (I.siteIdeal U.unop).extendedReesAlgebra.val.toRingHom
  naturality U V i := by ext x; rfl

lemma polynomialToRees_comp_reesToLaurent :
    I.polynomialToRees ≫ I.reesToLaurent =
      X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialToLaurent := by
  ext U p
  rfl

/-- The trivialisation of the deformation space over the punctured line:
`𝔾_{m,X} ⟶ D_I X`. -/
noncomputable def puncturedToDeformationSpace : X.punctured ⟶ I.deformationSpace :=
  relativeGluingMap _ _ I.reesToLaurent

/-- The ideal `(t)` of the extended Rees algebra. -/
noncomputable abbrev tIdeal (U : X.AffineZariskiSiteᵒᵖ) : Ideal (I.reesPresheaf.obj U) :=
  Ideal.span {(I.siteIdeal U.unop).extendedReesAlgebraT}

lemma map_tIdeal ⦃U V : X.AffineZariskiSiteᵒᵖ⦄ (i : U ⟶ V) :
    (I.tIdeal U).map (I.reesPresheaf.map i).hom = I.tIdeal V := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun t ↦ Ideal.span {t})
    (Ideal.extendedReesAlgebraMap_T _ _ (I.map_siteIdeal i).le)

/-- The associated graded algebra `𝒪_X[t, I t⁻¹] / t = ⨁_{r ≥ 0} I^r / I^{r+1}`. -/
noncomputable abbrev normalConePresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  quotientPresheaf I.tIdeal I.map_tIdeal

lemma coequifibered_toNormalConePresheaf :
    (I.toReesPresheaf ≫ toQuotientPresheaf I.tIdeal I.map_tIdeal).Coequifibered :=
  coequifibered_comp_toQuotientPresheaf I.coequifibered_toReesPresheaf _ _

/-- The normal cone `N_I X = Spec_X (⨁_{r ≥ 0} I^r / I^{r+1})`, the fibre of the deformation space
over the zero section `t = 0`. -/
noncomputable abbrev normalCone : Scheme.{u} :=
  (relativeGluingData I.coequifibered_toNormalConePresheaf).glued

/-- The inclusion `N_I X ⟶ D_I X` of the normal cone as the fibre over `t = 0`. -/
noncomputable def normalConeToDeformationSpace : I.normalCone ⟶ I.deformationSpace :=
  relativeGluingMap _ _ (toQuotientPresheaf I.tIdeal I.map_tIdeal)

/-- The map `𝒪_X[t] / t ⟶ 𝒪_X[t, I t⁻¹] / t`. -/
@[simps]
noncomputable def polynomialZeroToNormalCone :
    X.polynomialZeroPresheaf ⟶ I.normalConePresheaf where
  app U := CommRingCat.ofHom (Ideal.quotientMap _ (I.polynomialToRees.app U).hom (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_span]
    rw [Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton_iff.mpr Ideal.toExtendedReesAlgebra_X)))
  naturality U V i := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    change Ideal.Quotient.mk _ ((I.polynomialToRees.app V).hom ((X.polynomialPresheaf.map i).hom x)) =
      Ideal.Quotient.mk _ ((I.reesPresheaf.map i).hom ((I.polynomialToRees.app U).hom x))
    exact congrArg _ (I.polynomialToRees.naturality_apply i x)

/-! ### The closed subscheme and its relative affine line -/

/-- The quasi-coherent algebra `𝒪_X / I`. -/
noncomputable abbrev quotientAlgebra : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  quotientPresheaf (F := X.affineStructurePresheaf) (fun U ↦ I.siteIdeal U.unop) I.map_siteIdeal

/-- The quotient map `𝒪_X ⟶ 𝒪_X / I`. -/
noncomputable abbrev toQuotientAlgebra : X.affineStructurePresheaf ⟶ I.quotientAlgebra :=
  toQuotientPresheaf _ I.map_siteIdeal

lemma coequifibered_toQuotientAlgebra : I.toQuotientAlgebra.Coequifibered :=
  coequifibered_toQuotientPresheaf _ _

/-- The closed subscheme `V(I) = Spec_X (𝒪_X / I)`, as a relative spectrum. -/
noncomputable abbrev quotientSpec : Scheme.{u} :=
  (relativeGluingData I.coequifibered_toQuotientAlgebra).glued

/-- The quasi-coherent algebra `(𝒪_X / I)[t]`. -/
noncomputable abbrev quotientPolynomialAlgebra : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  I.quotientAlgebra ⋙ CommRingCat.polynomialFunctor

/-- The structure map `𝒪_X ⟶ (𝒪_X / I)[t]`. -/
noncomputable abbrev toQuotientPolynomialAlgebra :
    X.affineStructurePresheaf ⟶ I.quotientPolynomialAlgebra :=
  I.toQuotientAlgebra ≫ I.quotientAlgebra.whiskerLeft CommRingCat.polynomialC

lemma coequifibered_toQuotientPolynomialAlgebra : I.toQuotientPolynomialAlgebra.Coequifibered :=
  NatTrans.Coequifibered.comp I.coequifibered_toQuotientAlgebra
    (CommRingCat.coequifibered_polynomialC.whiskerLeft _)

/-- The relative affine line `𝔸¹_{V(I)} = Spec_X (𝒪_X / I)[t]`. -/
noncomputable abbrev quotientAffineLine : Scheme.{u} :=
  (relativeGluingData I.coequifibered_toQuotientPolynomialAlgebra).glued

/-- The map `𝒪_X[t, I t⁻¹] ⟶ (𝒪_X / I)[t]`, `t ↦ t`, `x t⁻¹ ↦ 0` for `x ∈ I`. -/
@[simps]
noncomputable def reesToQuotientPolynomial : I.reesPresheaf ⟶ I.quotientPolynomialAlgebra where
  app U := CommRingCat.ofHom ((I.siteIdeal U.unop).extendedReesAlgebraToPolynomial
    (Ideal.Quotient.mk _) Ideal.mk_ker.ge)
  naturality U V i := by
    refine CommRingCat.hom_ext ?_
    exact Ideal.extendedReesAlgebraToPolynomial_comp_extendedReesAlgebraMap _ _
      (I.map_siteIdeal i).le _ Ideal.mk_ker.ge _ Ideal.mk_ker.ge _
      (Ideal.quotientMap_comp_mk (le_comap_quotientPresheaf _ I.map_siteIdeal i))

/-- `t ↦ 0`: the restriction of `(𝒪_X / I)[t]` to the zero section. -/
@[simps]
noncomputable def quotientPolynomialEvalZero : I.quotientPolynomialAlgebra ⟶ I.quotientAlgebra where
  app U := CommRingCat.ofHom (Polynomial.evalRingHom 0)
  naturality U V i := by
    refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    exact Polynomial.eval_zero_map _ p

lemma toExtendedReesAlgebraT_mem_tIdeal (U : X.AffineZariskiSiteᵒᵖ) :
    (I.siteIdeal U.unop).extendedReesAlgebraT ∈ I.tIdeal U :=
  Ideal.subset_span rfl

/-- The projection `⨁_{r ≥ 0} I^r / I^{r+1} ⟶ 𝒪_X / I` to the degree-zero part. -/

noncomputable def normalConeToQuotient : I.normalConePresheaf ⟶ I.quotientAlgebra where
  app U := CommRingCat.ofHom (Ideal.Quotient.lift _
    ((Polynomial.evalRingHom 0).comp (I.reesToQuotientPolynomial.app U).hom)
    fun _ ha ↦ Ideal.span_T_le_ker_extendedReesAlgebraToPolynomial (Ideal.Quotient.mk _)
      Ideal.mk_ker.ge ha)
  naturality U V i := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    change Polynomial.eval 0 ((I.reesToQuotientPolynomial.app V).hom ((I.reesPresheaf.map i).hom x)) =
      (I.quotientAlgebra.map i).hom (Polynomial.eval 0 ((I.reesToQuotientPolynomial.app U).hom x))
    exact (congrArg (Polynomial.eval 0) (I.reesToQuotientPolynomial.naturality_apply i x)).trans
      (Polynomial.eval_zero_map _ _)

/-! ### The fibres of the deformation space -/

lemma toPolynomialPresheaf_comp_polynomialToLaurent :
    X.toPolynomialPresheaf ≫ X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialToLaurent =
      X.toLaurentPresheaf := by
  ext U x
  exact Polynomial.toLaurent_C x

lemma toReesPresheaf_comp_reesToLaurent : I.toReesPresheaf ≫ I.reesToLaurent = X.toLaurentPresheaf := by
  ext U x
  exact Ideal.coe_algebraMap_extendedReesAlgebra (I := I.siteIdeal U.unop) x

/-- **The punctured trivialisation.** Over the punctured line `𝔾_{m,X} ⊆ 𝔸¹_X` the deformation
space is trivial: `D_I X ×_{𝔸¹_X} 𝔾_{m,X} = 𝔾_{m,X}`, since inverting `t` in `𝒪_X[t, I t⁻¹]` gives
`𝒪_X[t, t⁻¹]`. -/
theorem isPullback_puncturedToDeformationSpace :
    IsPullback I.puncturedToDeformationSpace (𝟙 X.punctured) I.deformationSpaceToAffineLine
      X.puncturedToAffineLine := by
  have := isPullback_relativeGluingMap X.coequifibered_toPolynomialPresheaf
    I.coequifibered_toReesPresheaf X.coequifibered_toLaurentPresheaf
    X.coequifibered_toLaurentPresheaf I.polynomialToRees
    (X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialToLaurent) I.reesToLaurent (𝟙 _)
    toPolynomialPresheaf_comp_polynomialToLaurent I.toReesPresheaf_comp_reesToLaurent
    fun U ↦ Ideal.isPushout_toExtendedReesAlgebra (I.siteIdeal U)
  rwa [relativeGluingMap_id] at this

lemma isPushout_polynomialToRees_toQuotientPresheaf (U : X.AffineZariskiSiteᵒᵖ) :
    IsPushout (I.polynomialToRees.app U)
      ((toQuotientPresheaf (F := X.polynomialPresheaf) (fun _ ↦ Ideal.span {Polynomial.X})
        fun U V i ↦ by
          rw [Ideal.map_span, Set.image_singleton]
          exact congrArg (fun p ↦ Ideal.span {p}) (Polynomial.map_X _)).app U)
      ((toQuotientPresheaf I.tIdeal I.map_tIdeal).app U) (I.polynomialZeroToNormalCone.app U) := by
  have e : (Ideal.span {Polynomial.X}).map (I.polynomialToRees.app U).hom = I.tIdeal U := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun t ↦ Ideal.span {t}) Ideal.toExtendedReesAlgebra_X
  refine (CommRingCat.isPushout_quotient (I.polynomialToRees.app U)
    (Ideal.span {Polynomial.X})).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Ideal.quotEquivOfEq e).toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp
  · ext x; rfl
  · ext x; rfl

/-- The zero section `t = 0` of `𝔸¹_X`, as the relative spectrum of `𝒪_X[t] / t`. -/
noncomputable abbrev _root_.AlgebraicGeometry.Scheme.affineLineZero : Scheme.{u} :=
  (relativeGluingData X.coequifibered_toPolynomialZeroPresheaf).glued

/-- The inclusion of the zero section `Spec_X (𝒪_X[t] / t) ⟶ 𝔸¹_X`. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.affineLineZeroToAffineLine :
    X.affineLineZero ⟶ X.affineLine :=
  relativeGluingMap _ _ (toQuotientPresheaf _ _)

/-- The projection of the normal cone to the zero section of `𝔸¹_X`. -/
noncomputable def normalConeToAffineLineZero : I.normalCone ⟶ X.affineLineZero :=
  relativeGluingMap _ _ I.polynomialZeroToNormalCone

/-- **The fibre over `t = 0`.** The normal cone is the fibre of the deformation space over the
zero section of `𝔸¹_X`: `𝒪_X[t, I t⁻¹] ⊗_{𝒪_X[t]} 𝒪_X[t]/t = 𝒪_X[t, I t⁻¹] / t`. -/
theorem isPullback_normalConeToDeformationSpace :
    IsPullback I.normalConeToDeformationSpace I.normalConeToAffineLineZero
      I.deformationSpaceToAffineLine X.affineLineZeroToAffineLine :=
  isPullback_relativeGluingMap X.coequifibered_toPolynomialPresheaf
    I.coequifibered_toReesPresheaf X.coequifibered_toPolynomialZeroPresheaf
    I.coequifibered_toNormalConePresheaf I.polynomialToRees _ _ I.polynomialZeroToNormalCone
    rfl rfl fun U ↦ I.isPushout_polynomialToRees_toQuotientPresheaf (.op U)

end IdealSheafData

end AlgebraicGeometry.Scheme
