/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Paper.DivisibleExtensionDerivedReduction
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Modulus change of normalized derived reduction

Source: blueprint main-20261015, sk-lem-geo-cartier, proof paragraph 4 and its
auxiliary exponent comparison; Stacks Tags 06YY, 0D6D, 07A6 and 0152
(blueprint: lem-geo-cartier-exponent-independence).

The coefficient comparison is constructed by uniqueness of normalized left adjoints.
Its composite-unit characterization is the one of successive derived quotient
normalization. Kernel and quotient presentations and their normalized identifications
are the recorded DivisibleReduction constructions. The extension in a presentation
is auxiliary: for arbitrary B and F one may always take the split extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wZ wM wN
open CategoryTheory CategoryTheory.Limits

-- Sheafification is used through its functor API. Unfolding its chosen left adjoint
-- while comparing the two coefficient rings is prohibitively expensive.
attribute [local irreducible] constantSheaf presheafToSheaf

set_option backward.isDefEq.respectTransparency false in
private theorem exact_single_hom {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (N : A) : (G.mapDerivedCategorySingleFunctor 0).hom.app N =
      G.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj N) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app N) := by
  apply (cancel_epi (G.mapDerivedCategoryFactors.inv.app
    ((HomologicalComplex.single A (.up ℤ) 0).obj N))).1
  erw [Iso.inv_hom_id_app_assoc]
  exact G.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app N

set_option backward.isDefEq.respectTransparency false in
private theorem exact_comparison_single {A B D : Type*}
    [Category* A] [Category* B] [Category* D] [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    (R : A ⥤ B) (S : B ⥤ D) (T : A ⥤ D)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : R ⋙ S ≅ T) (M : A) :
    ((Functor.mapDerivedCategoryCompIso R S).symm ≪≫
      Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      (T.mapDerivedCategorySingleFunctor 0).hom.app M =
    S.mapDerivedCategory.map ((R.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (S.mapDerivedCategorySingleFunctor 0).hom.app (R.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (e.hom.app M) := by
  let P := (HomologicalComplex.single A (.up ℤ) 0).obj M
  rw [exact_single_hom T, exact_single_hom R, exact_single_hom S]
  simp only [Functor.map_comp, Category.assoc, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  erw [Functor.mapDerivedCategoryNatIso_fac_assoc e P]
  have hc := Functor.mapDerivedCategoryCompIso_fac R S P
  have hc' := congrArg
    (fun z ↦ (Functor.mapDerivedCategoryCompIso R S).inv.app (DerivedCategory.Q.obj P) ≫ z)
    hc
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hc'
  erw [← reassoc_of% hc', S.mapDerivedCategoryFactors_hom_naturality_assoc]
  have he :
      (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ S)) (.up ℤ)).hom.app P ≫
        (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P ≫
          (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).hom.app M =
      (S.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).hom.app (R.obj M) ≫
          (HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app M) := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp only [P, Functor.comp_obj, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom, NatTrans.id_app,
        NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        Functor.mapHomologicalComplex_map_f, HomologicalComplex.single_map_f_self,
        HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
        eqToIso.hom, eqToIso.inv, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      change 𝟙 _ ≫ e.hom.app M ≫ T.map (𝟙 M) =
        S.map (R.map (𝟙 M)) ≫ S.map (𝟙 (R.obj M)) ≫ e.hom.app M
      erw [T.map_id, R.map_id, S.map_id]
      simp only [Category.id_comp, Category.comp_id]
    · exact (S.map_isZero (R.map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi))).eq_of_src _ _
  have hmap : (DerivedCategory.singleFunctor D 0).map (e.hom.app M) =
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map
        (e.hom.app M)) := rfl
  rw [hmap]
  have hz := congrArg
    (fun z ↦ S.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app P) ≫
      S.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map z) he
  simp only [Functor.map_comp] at hz
  exact hz

private def exact_single_shift {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (M : A) :
    R.mapDerivedCategory.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor B 0).obj (R.obj M))⟦(1 : ℤ)⟧ :=
  (R.mapDerivedCategory.commShiftIso (1 : ℤ)).app
      ((DerivedCategory.singleFunctor A 0).obj M) ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso ((R.mapDerivedCategorySingleFunctor 0).app M)

set_option backward.isDefEq.respectTransparency false in
private theorem exact_single_shift_naturality {A B : Type*}
    [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {M N : A} (f : M ⟶ N) :
    R.mapDerivedCategory.map (((DerivedCategory.singleFunctor A 0).map f)⟦(1 : ℤ)⟧') ≫
      (exact_single_shift R N).hom =
    (exact_single_shift R M).hom ≫
      (((DerivedCategory.singleFunctor B 0).map (R.map f))⟦(1 : ℤ)⟧') := by
  dsimp only [exact_single_shift, Iso.trans_hom, Functor.mapIso_hom]
  erw [R.mapDerivedCategory.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp]
  erw [(R.mapDerivedCategorySingleFunctor 0).hom.naturality]
  simp only [Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exact_comparison_shift_single {A B D : Type*}
    [Category* A] [Category* B] [Category* D] [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    (R : A ⥤ B) (S : B ⥤ D) (T : A ⥤ D)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : R ⋙ S ≅ T) (M : A) :
    ((Functor.mapDerivedCategoryCompIso R S).symm ≪≫
      Functor.mapDerivedCategoryNatIso e).hom.app
        (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
      (exact_single_shift T M).hom =
    S.mapDerivedCategory.map (exact_single_shift R M).hom ≫
      (exact_single_shift S (R.obj M)).hom ≫
        ((DerivedCategory.singleFunctor D 0).map (e.hom.app M))⟦(1 : ℤ)⟧' := by
  let d := (Functor.mapDerivedCategoryCompIso R S).symm ≪≫
    Functor.mapDerivedCategoryNatIso e
  have hd : NatTrans.CommShift d.hom ℤ := by
    dsimp only [d, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have hs := congrArg (fun z ↦ z⟦(1 : ℤ)⟧') (exact_comparison_single R S T e M)
  simp only [Functor.map_comp] at hs
  change d.hom.app _ ≫ _ = _
  dsimp only [exact_single_shift, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc]
  erw [← NatTrans.shift_app_comm d.hom]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]
  erw [hs]
  erw [← S.mapDerivedCategory.commShiftIso_hom_naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem adjunct_shift {A B : Type*} [Category* A] [Category* B]
    [HasShift A ℤ] [HasShift B ℤ] {L : A ⥤ B} {R : B ⥤ A}
    [L.CommShift ℤ] [R.CommShift ℤ] (a : L ⊣ R) [a.CommShift ℤ]
    (X : A) (Y : B) (f : L.obj X ⟶ Y) :
    a.homEquiv _ _ ((L.commShiftIso (1 : ℤ)).hom.app X ≫ f⟦(1 : ℤ)⟧') ≫
      (R.commShiftIso (1 : ℤ)).hom.app Y = (a.homEquiv _ _ f)⟦(1 : ℤ)⟧' := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [R.commShiftIso_hom_naturality f (1 : ℤ)]
  have hu := a.unit_app_commShiftIso_hom_app ℤ (1 : ℤ) X
  simp only [Functor.commShiftIso_comp_hom_app] at hu
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ (R.map f)⟦(1 : ℤ)⟧') hu

set_option backward.isDefEq.respectTransparency false in
private theorem single_boundary_injective {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {S : ShortComplex A} (hS : S.ShortExact) (N : A)
    (hz : ∀ f : S.X₂ ⟶ N, f = 0) :
    Function.Injective (fun g : ((DerivedCategory.singleFunctor A 0).obj S.X₁)⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor A 0).obj N)⟦(1 : ℤ)⟧ ↦ hS.singleδ ≫ g) := by
  intro f g hfg
  let G := DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ (1 : ℤ)
  change hS.singleδ ≫ f = hS.singleδ ≫ g at hfg
  have he : hS.singleδ ≫ (f - g) = 0 := by
    rw [Preadditive.comp_sub, hfg, sub_self]
  obtain ⟨t, ht⟩ := hS.singleTriangle.rotate.yoneda_exact₃
    (CategoryTheory.Pretriangulated.rot_of_distTriang _ hS.singleTriangle_distinguished)
    (f - g) he
  have ht0 : t = 0 := by
    rw [← G.map_preimage t, hz (G.preimage t), G.map_zero]
  apply sub_eq_zero.mp
  rw [ht, ht0, comp_zero]

private theorem comparison_iso {A B : Type*} [Category* A] [Category* B]
    (G : A ⥤ B) [G.Full] [G.Faithful] {M N : A} {X : B}
    (s : X ≅ G.obj M) (c : X ≅ G.obj N) :
    ∃ e : M ≅ N, c.hom = s.hom ≫ G.map e.hom := by
  let e := G.preimageIso (s.symm ≪≫ c)
  refine ⟨e, ?_⟩
  dsimp only [e]
  rw [Functor.preimageIso_hom, G.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

private theorem normalized_composite_square {X Y Z : Type*}
    [Category* X] [Category* Y] [Category* Z]
    {Lm : X ⥤ Y} {Ln : X ⥤ Z} {S : Y ⥤ X} {R : Z ⥤ Y} {T : Z ⥤ X}
    (am : Lm ⊣ S) (an : Ln ⊣ T) (d : R ⋙ S ⟶ T)
    {X₀ X₁ B₀ B' B₁ : X} {M M' : Y} {N : Z}
    (α : Lm.obj X₀ ≅ M) (γ : Ln.obj X₁ ≅ N)
    (c : M ⟶ R.obj N) (cr : R.obj N ⟶ M')
    (cs : S.obj M ⟶ B₀) (cs' : S.obj M' ⟶ B') (ct : T.obj N ⟶ B₁)
    (g : M ⟶ M') (b : B₀ ⟶ B') (e : B' ⟶ B₁)
    (p : X₀ ⟶ B₀) (q : X₁ ⟶ B₁) (f : X₀ ⟶ X₁)
    (hu : am.unit.app X₀ ≫ S.map α.hom ≫ cs = p)
    (hv : an.unit.app X₁ ≫ T.map γ.hom ≫ ct = q)
    (hb : c ≫ cr = g) (hc : S.map g ≫ cs' = cs ≫ b)
    (hd : d.app N ≫ ct = S.map cr ≫ cs' ≫ e)
    (ht : am.homEquiv _ _ (α.hom ≫ c) ≫ d.app N =
      an.homEquiv _ _ (Ln.map f ≫ γ.hom)) : p ≫ b ≫ e = f ≫ q := by
  have h := congrArg (fun z ↦ z ≫ ct) ht
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at h
  rw [hd] at h
  rw [← S.map_comp_assoc c cr, hb, reassoc_of% hc] at h
  rw [reassoc_of% hu] at h
  rw [← Category.assoc (an.unit.app X₀)] at h
  erw [← an.unit.naturality f] at h
  simp only [Category.assoc] at h
  rw [hv] at h
  exact h

private theorem section_nsmul {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} (f : M ⟶ N) (k : ℕ)
    (U : Cᵒᵖ) (x : M.val.obj U) : (k • f).val.app U x = k • f.val.app U x := by
  let E := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U
  have hh : E.map (k • f) = k • E.map f := E.map_nsmul
  exact ConcreteCategory.congr_hom hh x

namespace SheafOfModules.GeoCartierExponent

open DivisibleReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {m n : ℕ}

/-- The constant coefficient map induced by reduction from Z/m to Z/n.
Source: Cartier exponent comparison, Stacks 0D6D
(blueprint: lem-geo-cartier-exponent-independence). -/
def residueProjection (h : n ∣ m) : residues J m ⟶ residues J n :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom h (ZMod n)).comp ULift.ringEquiv.toRingHom)))

set_option linter.unusedSectionVars false in
/-- The actual constant coefficient projections form the required triangle.
Source: Stacks 0D6D, Cartier exponent comparison
(blueprint: lem-geo-cartier-exponent-independence).
Proof: both ring homomorphisms send each integer to its residue modulo n.
Integer casts determine homomorphisms out of Z. ULift transports that equality,
and functoriality of constant sheafification preserves the composite. -/
theorem projection_comp (h : n ∣ m) :
    projection J m ≫ residueProjection (J := J) h = projection J n := by
  unfold projection residueProjection
  rw [← Functor.map_comp]
  congr 1
  ext x
  rcases x with ⟨x⟩
  change (ZMod.castHom h (ZMod n)) (x : ZMod m) = (x : ZMod n)
  exact map_intCast _ _

/-- Scalar restriction along the modulus map, retaining the underlying sections.
Source: Stacks 03D7 and 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
abbrev residueRestriction (h : n ∣ m) : Residue J n ⥤ Residue J m :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
    (residueProjection (J := J) h))

/-- The identity-on-sections composition comparison for ordinary restriction.
Source: Stacks 03D7 and 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
def restrictionComp (h : n ∣ m) :
    residueRestriction (J := J) h ⋙ restriction J m ≅ restriction J n :=
  NatIso.ofComponents (fun M ↦
    (fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App
          ((projection J m).hom.app U).hom
          ((residueProjection (J := J) h).hom.app U).hom
          ((projection J n).hom.app U).hom
          (congrArg (fun a ↦ (a.hom.app U).hom) (projection_comp (J := J) h)).symm
          (M.val.obj U)).symm) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

variable [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wM} (Residue J m)] [HasDerivedCategory.{wN} (Residue J n)]

/-- The canonical composition comparison for termwise derived restriction.
Source: Stacks 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
def derivedRestrictionComp (h : n ∣ m) :
    (residueRestriction (J := J) h).mapDerivedCategory ⋙ derivedRestriction m ≅
      derivedRestriction n :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionComp (J := J) h)

/-- The canonical transitivity isomorphism. Normalized adjunctions determine it by
sending the composite scalar-extension unit to the direct scalar-extension unit.
This is exactly the unit characterization of
lem-sfb-successive-derived-quotient-normalization, not a chosen objectwise isomorphism.
Source: Stacks 0D6D and 07A6 (blueprint: lem-geo-cartier-exponent-independence). -/
def transitivity (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h)) :
    Dm.T ⋙ Dmn.T ≅ Dn.T :=
  Adjunction.leftAdjointUniq
    (((sheafScalarDerivedAdjunction (projection J m) Dm).comp
      (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn)).ofNatIsoRight
        (derivedRestrictionComp (J := J) h))
    (sheafScalarDerivedAdjunction (projection J n) Dn)

/-- The canonical K-flat computation on a degree-zero flat module, written as a morphism
so that no flatness proof is hidden in its data. It is invertible for flat M.
Source: Stacks 06YY and 06YQ (blueprint: lem-geo-cartier-exponent-independence). -/
def ordinarySingle (h : n ∣ m)
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) :
    Dmn.T.obj ((DerivedCategory.singleFunctor (Residue J m) 0).obj M) ⟶
      (DerivedCategory.singleFunctor (Residue J n) 0).obj
        (changeOfRings (residueProjection (J := J) h) M) :=
  Dmn.ε.app ((CochainComplex.singleFunctor (Residue J m) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex Dmn.E (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctor (Residue J n) 0).map (eqToHom (Dmn.obj_eq M))

omit [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wM} (Residue J m)] in
set_option backward.isDefEq.respectTransparency false in
private theorem single_kflat (M : Residue J m)
    (hM : IsFlatOnSite (R := residues J m) M) :
    CochainComplex.IsKFlatIndependentCoefficients (R := residues J m)
      ((CochainComplex.singleFunctor (Residue J m) 0).obj M) := by
  let R := residues J m
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  apply isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ 0
  intro i
  by_cases hi : i = 0
  · subst i
    change IsFlatOnSite (R := residues J m) M
    exact hM
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
    have hf := CategoryTheory.ObjectProperty.flat_of_isZero hz
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm hf.2

omit [HasDerivedCategory.{wZ} (Integral J)] in
private theorem ordinarySingle_isIso (h : n ∣ m)
    (D : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (hM : IsFlatOnSite (R := residues J m) M) :
    IsIso (ordinarySingle h D M) := by
  have := D.computes _ (single_kflat M hM)
  unfold ordinarySingle
  infer_instance

omit [HasDerivedCategory.{wZ} (Integral J)] in
set_option backward.isDefEq.respectTransparency false in
private theorem ordinarySingle_unit (h : n ∣ m)
    (D : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (hM : IsFlatOnSite (R := residues J m) M) :
    (sheafScalarDerivedAdjunction (residueProjection (J := J) h) D).unit.app
        ((DerivedCategory.singleFunctor (Residue J m) 0).obj M) ≫
      (residueRestriction (J := J) h).mapDerivedCategory.map (ordinarySingle h D M) ≫
      ((residueRestriction (J := J) h).mapDerivedCategorySingleFunctor 0).hom.app
        (changeOfRings (residueProjection (J := J) h) M) =
    (DerivedCategory.singleFunctor (Residue J m) 0).map
      ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) D).unit.app M ≫
        (residueRestriction (J := J) h).map (eqToHom (D.obj_eq M))) := by
  let a := sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) D
  let R := residueRestriction (J := J) h
  let P := (CochainComplex.singleFunctor (Residue J m) 0).obj M
  have hu := (Classical.choose_spec
    (Classical.choose_spec
      (sheafDerivedScalarAdjunction_exists (residueProjection (J := J) h) D)).2)
      P (single_kflat M hM)
  change (sheafScalarDerivedAdjunction _ D).unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (D.ε.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((D.E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) at hu
  unfold ordinarySingle
  simp only [Functor.map_comp, Category.assoc]
  rw [show R.mapDerivedCategory.map
      ((DerivedCategory.singleFunctor (Residue J n) 0).map (eqToHom (D.obj_eq M))) ≫
      (R.mapDerivedCategorySingleFunctor 0).hom.app _ =
    (R.mapDerivedCategorySingleFunctor 0).hom.app (D.E.obj M) ≫
      (DerivedCategory.singleFunctor (Residue J m) 0).map
        (R.map (eqToHom (D.obj_eq M))) from
      (R.mapDerivedCategorySingleFunctor 0).hom.naturality (eqToHom (D.obj_eq M))]
  have hc : R.mapDerivedCategory.map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex D.E (.up ℤ) 0).hom.app M)) ≫
        (R.mapDerivedCategorySingleFunctor 0).hom.app (D.E.obj M) =
      R.mapDerivedCategoryFactors.hom.app ((D.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((R.mapHomologicalComplex (.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex D.E (.up ℤ) 0).hom.app M) ≫
            (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app
              (D.E.obj M)) := by
    rw [Functor.map_comp]
    rw [← R.mapDerivedCategoryFactors_hom_naturality_assoc]
    congr 1
    apply (cancel_epi (R.mapDerivedCategoryFactors.inv.app
      ((HomologicalComplex.single (Residue J n) (.up ℤ) 0).obj (D.E.obj M)))).1
    erw [Iso.inv_hom_id_app_assoc]
    exact R.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app _
  erw [reassoc_of% hc, reassoc_of% hu]
  rw [← Category.assoc]
  congr 1
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = DerivedCategory.Q.map _
  rw [← Functor.map_comp]
  congr 1
  ext U x
  rfl

omit [HasDerivedCategory.{wZ} (Integral J)] in
set_option backward.isDefEq.respectTransparency false in
private theorem ordinarySingle_adjunct (h : n ∣ m)
    (D : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (N : Residue J n) (hM : IsFlatOnSite (R := residues J m) M)
    (f : changeOfRings (residueProjection (J := J) h) M ⟶ N) :
    (sheafScalarDerivedAdjunction (residueProjection (J := J) h) D).homEquiv _ _
        (ordinarySingle h D M ≫ (DerivedCategory.singleFunctor (Residue J n) 0).map f) ≫
      ((residueRestriction (J := J) h).mapDerivedCategorySingleFunctor 0).hom.app N =
    (DerivedCategory.singleFunctor (Residue J m) 0).map
      ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) D).unit.app M ≫
        (residueRestriction (J := J) h).map (eqToHom (D.obj_eq M) ≫ f)) := by
  let R := residueRestriction (J := J) h
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn : R.mapDerivedCategory.map
      ((DerivedCategory.singleFunctor (Residue J n) 0).map f) ≫
      (R.mapDerivedCategorySingleFunctor 0).hom.app N =
    (R.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor (Residue J m) 0).map (R.map f) :=
    (R.mapDerivedCategorySingleFunctor 0).hom.naturality f
  erw [hn]
  erw [reassoc_of% ordinarySingle_unit h D M hM]
  simp only [Functor.map_comp, Category.assoc]
  rfl

omit [HasDerivedCategory.{wZ} (Integral J)] in
set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_unit_pure (h : n ∣ m)
    (D : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) D).unit.app M ≫
      (residueRestriction (J := J) h).map (eqToHom (D.obj_eq M))).val.app U x =
      SuccessiveDerivedQuotient.pure (residueProjection (J := J) h) M U 1 x := by
  have hu := (Classical.choose_spec
    (sheafDerivedScalarAdjunction_exists (residueProjection (J := J) h) D)).1 M U x
  change (eqToHom (D.obj_eq M)).val.app U
    (((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) D).unit.app M).val.app
      U x) = _
  erw [hu]
  have hh := congrArg (fun f ↦ f.val.app U)
    (show eqToHom (D.obj_eq M).symm ≫ eqToHom (D.obj_eq M) = 𝟙 _ by simp)
  have hh' := ConcreteCategory.congr_hom hh
  exact hh' _

omit [EssentiallySmall.{r} C] [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wM} (Residue J m)] [HasDerivedCategory.{wN} (Residue J n)] in
set_option backward.isDefEq.respectTransparency false in
private theorem pure_smul (h : n ∣ m) (M : Residue J m) (U : Cᵒᵖ)
    (b : (residues J n).obj.obj U) (x : M.val.obj U) :
    SuccessiveDerivedQuotient.pure (residueProjection (J := J) h) M U b x =
      b • SuccessiveDerivedQuotient.pure (residueProjection (J := J) h) M U 1 x := by
  let : CommRing ((derivedChangeRingIndependentCoefficients J (residues J m)).obj.obj U) :=
    inferInstanceAs (CommRing ((residues J m).obj.obj U))
  let : CommRing ((derivedChangeRingIndependentCoefficients J (residues J n)).obj.obj U) :=
    inferInstanceAs (CommRing ((residues J n).obj.obj U))
  let η := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J (residues J n)).obj)).unit.app
      (changeOfRingsPresheaf (residueProjection (J := J) h) M)).app U
  change η _ = b • η _
  rw [← η.hom.map_smul, ModuleCat.ExtendScalars.smul_tmul, mul_one]

omit [HasDerivedCategory.{wM} (Residue J m)] in
set_option backward.isDefEq.respectTransparency false in
private theorem kappa_single (P : Presentation (J := J) n) :
    kappa n P ≫ (exact_single_shift (restriction J n) P.H).hom =
      P.kummer.singleδ := by
  dsimp only [kappa, exact_single_shift, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← (shiftFunctor (DerivedCategory (Integral J)) (1 : ℤ)).map_comp]
  erw [((restriction J n).mapDerivedCategorySingleFunctor 0).inv_hom_id_app]
  erw [(shiftFunctor (DerivedCategory (Integral J)) (1 : ℤ)).map_id]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionComp_single (h : n ∣ m) (M : Residue J n) :
    (derivedRestrictionComp (J := J) h).hom.app
        ((DerivedCategory.singleFunctor (Residue J n) 0).obj M) ≫
      ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app M =
    (derivedRestriction m).map
        (((residueRestriction (J := J) h).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((restriction J m).mapDerivedCategorySingleFunctor 0).hom.app
        ((residueRestriction (J := J) h).obj M) ≫
      (DerivedCategory.singleFunctor (Integral J) 0).map ((restrictionComp h).hom.app M) := by
  exact exact_comparison_single (residueRestriction (J := J) h) (restriction J m)
    (restriction J n) (restrictionComp h) M

set_option backward.isDefEq.respectTransparency false in
private theorem transitivity_adjunct (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (X : DerivedCategory (Integral J)) (Y : DerivedCategory (Residue J n))
    (f : Dn.T.obj X ⟶ Y) :
    (sheafScalarDerivedAdjunction (projection J m) Dm).homEquiv _ _
      ((sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn).homEquiv _ _
        ((transitivity h Dm Dn Dmn).hom.app X ≫ f)) ≫
        (derivedRestrictionComp (J := J) h).hom.app Y =
      (sheafScalarDerivedAdjunction (projection J n) Dn).homEquiv _ _ f := by
  let a := ((sheafScalarDerivedAdjunction (projection J m) Dm).comp
    (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn)).ofNatIsoRight
      (derivedRestrictionComp (J := J) h)
  have ht : a.unit.app X ≫ (derivedRestriction n).map
      ((transitivity h Dm Dn Dmn).hom.app X) =
      (sheafScalarDerivedAdjunction (projection J n) Dn).unit.app X :=
    a.unit_leftAdjointUniq_hom_app (sheafScalarDerivedAdjunction (projection J n) Dn) X
  calc
    _ = a.homEquiv _ _ ((transitivity h Dm Dn Dmn).hom.app X ≫ f) := by
      dsimp only [a]
      rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
      rfl
    _ = _ := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ht]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem transitivity_normalized_adjunct (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (X : DerivedCategory (Integral J)) (M : DerivedCategory (Residue J m))
    (Y : DerivedCategory (Residue J n)) (α : Dm.T.obj X ≅ M)
    (f : Dn.T.obj X ⟶ Y) :
    (sheafScalarDerivedAdjunction (projection J m) Dm).homEquiv _ _
      (α.hom ≫
        (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn).homEquiv _ _
          (Dmn.T.map α.inv ≫ (transitivity h Dm Dn Dmn).hom.app X ≫ f)) ≫
        (derivedRestrictionComp (J := J) h).hom.app Y =
      (sheafScalarDerivedAdjunction (projection J n) Dn).homEquiv _ _ f := by
  rw [← Adjunction.homEquiv_naturality_left]
  rw [← Dmn.T.map_comp_assoc, Iso.hom_inv_id, Dmn.T.map_id, Category.id_comp]
  exact transitivity_adjunct h Dm Dn Dmn X Y f

/-- Changing modulus identifies the actual transitivity maps with ordinary quotient and
torsion scalar extension. The two presentations encode exactly the kernels/cokernels
and epi/mono hypotheses, with the same underlying B and F identified by hB and hF.
Their auxiliary short exact extensions may both be chosen split.

Source: Cartier proof paragraph 4, auxiliary exponent comparison; Stacks 06YY, 0D6D,
07A6 and 0152 (blueprint: lem-geo-cartier-exponent-independence).
Proof:
1. Resolve F by a flat-term K-flat complex. The multiplication-by-q short exact
sequence and its cohomology sequence identify the degree-zero extension unit with
F -> F/qF, for q=m,n (lem-pc-kflat-resolution, def-pc-flat-sheaf-modules,
lem-weil-pbc-complex-ses-triangle, lem-sf-derived-homology-long-exact,
lem-pur-derived-change-of-rings, lem-pur-sheaf-ring-derived-coefficient-adjunction,
lem-weil-pbc-derived-single-fully-faithful).
2. Use the normalized identifications of lem-sfb-divisible-extension-derived-reduction.
The composite-unit identity of lem-sfb-successive-derived-quotient-normalization
identifies the comparison defined above with its canonical transitivity map.
3. The flat single complexes Q_m[0] and H_m[0] are K-flat by
lem-pc-bounded-above-flat-kflat-site. Derived change of rings computes their extensions
by ordinarySingle. The normalized adjunction unit is x -> 1 tensor x, also after
shifting, and the transpose sends b tensor x to b times its image.
4. The quotient projection Q_m -> Q_n composed with F -> Q_m is F -> Q_n.
The two successive normalized adjunction bijections therefore identify the actual
comparison with b tensor (f mod m) -> b(f mod n).
5. Put d=m/n. The morphism between the Kummer sequences for m and n has components
(d on kernels, d on the middle B, identity on the right B). Since nd=m, its boundary
identity is beta[1] kappa_m = kappa_n by naturality of the short exact triangle.
6. Transpose this equality under both scalar adjunctions and cancel alpha_m, not
kappa_m. It gives b tensor h -> b beta(h), where beta(h)=dh. Thus the shifted
ordinary comparison is precisely the actual transitivity map, with its sign fixed.
7. The quotient tensor is Q_m/nQ_m=F/nF. Local integer lifts and tensor balancing
give the inverse f mod n -> 1 tensor (f mod m). This descends through sheafification
(def-pur-sheaf-tensor-product).
8. The map beta:H_m -> H_n is locally onto: lift t in H_n to z with mz=t and set
h=nz. Its kernel is nH_m: if dh=0, lift h=ny, then my=dh=0. Hence beta induces
H_m/nH_m isomorphic to H_n, the displayed ordinary tensor map. For m=n the maps
are identities; for n=1 the targets vanish. Zero sheaves require no exception. -/
theorem geoCartier_exponent_independence [HasTerminal C]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : DivisibleReduction.Presentation (J := J) m)
    (Pn : DivisibleReduction.Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) (hF : Pm.S.X₃ = Pn.S.X₃)
    (hH : IsFlatOnSite (R := residues J m) Pm.H)
    (hQ : IsFlatOnSite (R := residues J m) Pm.Q) :
    ∃ (eF : changeOfRings (residueProjection (J := J) h) Pm.Q ≅ Pn.Q)
      (eH : changeOfRings (residueProjection (J := J) h) Pm.H ≅ Pn.H)
      (beta : Pm.H ⟶ (residueRestriction (J := J) h).obj Pn.H),
      (∀ (U : Cᵒᵖ) (f : Pm.S.X₃.val.obj U) (b : (residues J n).obj.obj U),
        eF.hom.val.app U (SuccessiveDerivedQuotient.pure
          (residueProjection (J := J) h) Pm.Q U b (Pm.p.val.app U f)) =
        b • @id (Pn.Q.val.obj U) (Pn.p.val.app U ((eqToHom hF).val.app U f))) ∧
      (∀ (U : Cᵒᵖ) (x : Pm.H.val.obj U),
        Pn.i.val.app U (beta.val.app U x) =
          (m / n) • (eqToHom hB).val.app U (Pm.i.val.app U x)) ∧
      (∀ (U : Cᵒᵖ) (x : Pm.H.val.obj U) (b : (residues J n).obj.obj U),
        eH.hom.val.app U (SuccessiveDerivedQuotient.pure
          (residueProjection (J := J) h) Pm.H U b x) =
          b • @id (Pn.H.val.obj U) (beta.val.app U x)) ∧
      Dmn.T.map (identifications m Dm hm Pm).alphaF.inv ≫
        (transitivity h Dm Dn Dmn).hom.app
          ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₃) ≫
        Dn.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hF)) ≫
        (identifications n Dn hn Pn).alphaF.hom =
      ordinarySingle h Dmn Pm.Q ≫
        (DerivedCategory.singleFunctor (Residue J n) 0).map eF.hom ∧
      Dmn.T.map (identifications m Dm hm Pm).alphaB.inv ≫
        (transitivity h Dm Dn Dmn).hom.app
          ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₁) ≫
        Dn.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hB)) ≫
        (identifications n Dn hn Pn).alphaB.hom =
      (Dmn.T.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Residue J m) 0).obj Pm.H) ≫
        (ordinarySingle h Dmn Pm.H)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor (Residue J n) 0).map eH.hom)⟦(1 : ℤ)⟧' := by
  classical
  let F : Integral J ⥤ DerivedCategory.{wZ} (Integral J) :=
    DerivedCategory.singleFunctor (Integral J) 0
  let Gm : Residue J m ⥤ DerivedCategory.{wM} (Residue J m) :=
    DerivedCategory.singleFunctor (Residue J m) 0
  let Gn : Residue J n ⥤ DerivedCategory.{wN} (Residue J n) :=
    DerivedCategory.singleFunctor (Residue J n) 0
  let R := residueRestriction (J := J) h
  let Im := identifications m Dm hm Pm
  let In := identifications n Dn hn Pn
  let a := sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn
  let ad := sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn
  have hQiso := ordinarySingle_isIso h Dmn Pm.Q hQ
  have hHiso := ordinarySingle_isIso h Dmn Pm.H hH
  let cF : Dmn.T.obj (Gm.obj Pm.Q) ≅ Gn.obj Pn.Q :=
    (Dmn.T.mapIso Im.alphaF).symm ≪≫
      (transitivity h Dm Dn Dmn).app (F.obj Pm.S.X₃) ≪≫
        Dn.T.mapIso (F.mapIso (eqToIso hF)) ≪≫ In.alphaF
  let cB : Dmn.T.obj ((Gm.obj Pm.H)⟦(1 : ℤ)⟧) ≅ (Gn.obj Pn.H)⟦(1 : ℤ)⟧ :=
    (Dmn.T.mapIso Im.alphaB).symm ≪≫
      (transitivity h Dm Dn Dmn).app (F.obj Pm.S.X₁) ≪≫
        Dn.T.mapIso (F.mapIso (eqToIso hB)) ≪≫ In.alphaB
  obtain ⟨eF, hcF⟩ := comparison_iso
    (M := changeOfRings (residueProjection (J := J) h) Pm.Q) (N := Pn.Q)
    (X := Dmn.T.obj (Gm.obj Pm.Q)) Gn (asIso (ordinarySingle h Dmn Pm.Q)) cF
  let tH : Dmn.T.obj ((Gm.obj Pm.H)⟦(1 : ℤ)⟧) ≅
      (Gn.obj (changeOfRings (residueProjection (J := J) h) Pm.H))⟦(1 : ℤ)⟧ :=
    (Dmn.T.commShiftIso (1 : ℤ)).app (Gm.obj Pm.H) ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso (asIso (ordinarySingle h Dmn Pm.H))
  obtain ⟨eH, hcB'⟩ := comparison_iso
    (M := changeOfRings (residueProjection (J := J) h) Pm.H) (N := Pn.H)
    (X := Dmn.T.obj ((Gm.obj Pm.H)⟦(1 : ℤ)⟧))
    (Gn ⋙ shiftFunctor _ (1 : ℤ)) tH cB
  let beta : Pm.H ⟶ R.obj Pn.H :=
    a.unit.app Pm.H ≫ R.map (eqToHom (Dmn.obj_eq Pm.H) ≫ eH.hom)
  have hcB : cB.hom = (Dmn.T.commShiftIso (1 : ℤ)).hom.app (Gm.obj Pm.H) ≫
      (ordinarySingle h Dmn Pm.H)⟦(1 : ℤ)⟧' ≫ (Gn.map eH.hom)⟦(1 : ℤ)⟧' := by
    change cB.hom = tH.hom ≫ (Gn.map eH.hom)⟦(1 : ℤ)⟧' at hcB'
    simpa only [tH, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom,
      Category.assoc] using hcB'
  let betaQ : Pm.Q ⟶ R.obj Pn.Q :=
    a.unit.app Pm.Q ≫ R.map (eqToHom (Dmn.obj_eq Pm.Q) ≫ eF.hom)
  have hQadj : ad.homEquiv _ _ cF.hom ≫ (R.mapDerivedCategorySingleFunctor 0).hom.app
      Pn.Q = Gm.map betaQ := by
    rw [hcF]
    exact ordinarySingle_adjunct h Dmn Pm.Q Pn.Q hQ eF.hom
  have hQsquare : Pm.p ≫ (restriction J m).map betaQ ≫
      (restrictionComp h).hom.app Pn.Q = eqToHom hF ≫ Pn.p := by
    let Rm := derivedRestriction (J := J) m
    let Rn := derivedRestriction (J := J) n
    let cm := (restriction J m).mapDerivedCategorySingleFunctor 0
    let cn := (restriction J n).mapDerivedCategorySingleFunctor 0
    have ht := transitivity_normalized_adjunct h Dm Dn Dmn
      (F.obj Pm.S.X₃) (Gm.obj Pm.Q) (Gn.obj Pn.Q) Im.alphaF
      (Dn.T.map (F.map (eqToHom hF)) ≫ In.alphaF.hom)
    change (sheafScalarDerivedAdjunction (projection J m) Dm).homEquiv _ _
      (Im.alphaF.hom ≫ ad.homEquiv _ _ cF.hom) ≫
        (derivedRestrictionComp h).hom.app (Gn.obj Pn.Q) = _ at ht
    have hs := normalized_composite_square
      (sheafScalarDerivedAdjunction (projection J m) Dm)
      (sheafScalarDerivedAdjunction (projection J n) Dn) (derivedRestrictionComp h).hom
      Im.alphaF In.alphaF (ad.homEquiv _ _ cF.hom)
      ((R.mapDerivedCategorySingleFunctor 0).hom.app Pn.Q)
      (cm.hom.app Pm.Q) (cm.hom.app (R.obj Pn.Q)) (cn.hom.app Pn.Q)
      (Gm.map betaQ) (F.map ((restriction J m).map betaQ))
      (F.map ((restrictionComp h).hom.app Pn.Q))
      (F.map Pm.p) (F.map Pn.p) (F.map (eqToHom hF))
      Im.quotient_unit In.quotient_unit hQadj (cm.hom.naturality betaQ)
      (restrictionComp_single h Pn.Q) ht
    apply F.map_injective
    simpa only [Functor.map_comp, Category.assoc] using hs
  let bint : (restriction J m).obj Pm.H ⟶ (restriction J n).obj Pn.H :=
    (restriction J m).map beta ≫ (restrictionComp h).hom.app Pn.H
  have hnH : n • 𝟙 ((restriction J n).obj Pn.H) = 0 := by
    have := Pn.kummer.mono_f
    apply (cancel_mono Pn.i).1
    simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.comp_id,
      Category.id_comp, zero_comp] using Pn.wi
  have hmH : m • 𝟙 ((restriction J n).obj Pn.H) = 0 := by
    rw [← Nat.div_mul_cancel h, mul_smul, hnH, smul_zero]
  have hvan (f : Pm.S.X₁ ⟶ (restriction J n).obj Pn.H) : f = 0 := by
    have := Pm.kummer.epi_g
    apply (cancel_epi (m • 𝟙 Pm.S.X₁)).1
    rw [comp_zero]
    calc
      _ = f ≫ (m • 𝟙 _) := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
          Category.comp_id]
      _ = 0 := by rw [hmH, comp_zero]
  have hzero : ((m / n) • (Pm.i ≫ eqToHom hB)) ≫ (n • 𝟙 Pn.S.X₁) = 0 := by
    calc
      _ = (n * (m / n)) • (Pm.i ≫ eqToHom hB) := by
        simp only [Preadditive.comp_nsmul, Category.comp_id, smul_smul]
      _ = m • (Pm.i ≫ eqToHom hB) := by rw [Nat.mul_div_cancel' h]
      _ = (Pm.i ≫ (m • 𝟙 Pm.S.X₁)) ≫ eqToHom hB := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := by rw [Pm.wi, zero_comp]
  let b₀ : (restriction J m).obj Pm.H ⟶ (restriction J n).obj Pn.H :=
    (KernelFork.IsLimit.lift' Pn.kummer.fIsKernel
      ((m / n) • (Pm.i ≫ eqToHom hB)) hzero).1
  have hb₀ : b₀ ≫ Pn.i = (m / n) • (Pm.i ≫ eqToHom hB) :=
    (KernelFork.IsLimit.lift' Pn.kummer.fIsKernel _ hzero).2
  have hb₀δ : Pm.kummer.singleδ ≫ (F.map b₀)⟦(1 : ℤ)⟧' =
      F.map (eqToHom hB) ≫ Pn.kummer.singleδ := by
    let k : ShortComplex.mk Pm.i (m • 𝟙 Pm.S.X₁) Pm.wi ⟶
        ShortComplex.mk Pn.i (n • 𝟙 Pn.S.X₁) Pn.wi :=
      { τ₁ := b₀
        τ₂ := (m / n) • eqToHom hB
        τ₃ := eqToHom hB
        comm₁₂ := by
          rw [hb₀]
          simp only [Preadditive.comp_nsmul]
        comm₂₃ := by
          simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
            Category.id_comp, smul_smul]
          rw [Nat.mul_comm n, Nat.div_mul_cancel h] }
    exact (ShortComplex.ShortExact.singleTriangle.map Pm.kummer Pn.kummer k).comm₃
  have hbintδ : Pm.kummer.singleδ ≫ (F.map bint)⟦(1 : ℤ)⟧' =
      F.map (eqToHom hB) ≫ Pn.kummer.singleδ := by
    have had : ad.CommShift ℤ := ad.commShift_of_rightAdjoint ℤ
    have hBadj : ad.homEquiv _ _ cB.hom ≫ (exact_single_shift R Pn.H).hom =
        (Gm.map beta)⟦(1 : ℤ)⟧' := by
      rw [hcB, ← (shiftFunctor (DerivedCategory (Residue J n)) (1 : ℤ)).map_comp]
      change ad.homEquiv _ _
          ((Dmn.T.commShiftIso (1 : ℤ)).hom.app (Gm.obj Pm.H) ≫
            (ordinarySingle h Dmn Pm.H ≫ Gn.map eH.hom)⟦(1 : ℤ)⟧') ≫
          ((R.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (Gn.obj Pn.H) ≫
            ((R.mapDerivedCategorySingleFunctor 0).hom.app Pn.H)⟦(1 : ℤ)⟧') = _
      rw [← Category.assoc, adjunct_shift]
      rw [← Functor.map_comp]
      erw [ordinarySingle_adjunct h Dmn Pm.H Pn.H hH eH.hom]
    let Rm := derivedRestriction (J := J) m
    let Rn := derivedRestriction (J := J) n
    have hu : eta m Dm Pm.S.X₁ ≫ Rm.map Im.alphaB.hom ≫
        (exact_single_shift (restriction J m) Pm.H).hom = Pm.kummer.singleδ := by
      rw [← Category.assoc, Im.kummer_unit, kappa_single Pm]
    have hv : eta n Dn Pn.S.X₁ ≫ Rn.map In.alphaB.hom ≫
        (exact_single_shift (restriction J n) Pn.H).hom = Pn.kummer.singleδ := by
      rw [← Category.assoc, In.kummer_unit, kappa_single Pn]
    have ht := transitivity_normalized_adjunct h Dm Dn Dmn
      (F.obj Pm.S.X₁) ((Gm.obj Pm.H)⟦(1 : ℤ)⟧) ((Gn.obj Pn.H)⟦(1 : ℤ)⟧) Im.alphaB
      (Dn.T.map (F.map (eqToHom hB)) ≫ In.alphaB.hom)
    change (sheafScalarDerivedAdjunction (projection J m) Dm).homEquiv _ _
      (Im.alphaB.hom ≫ ad.homEquiv _ _ cB.hom) ≫
        (derivedRestrictionComp h).hom.app ((Gn.obj Pn.H)⟦(1 : ℤ)⟧) = _ at ht
    have hs := normalized_composite_square
      (sheafScalarDerivedAdjunction (projection J m) Dm)
      (sheafScalarDerivedAdjunction (projection J n) Dn) (derivedRestrictionComp h).hom
      Im.alphaB In.alphaB (ad.homEquiv _ _ cB.hom)
      (exact_single_shift R Pn.H).hom
      (exact_single_shift (restriction J m) Pm.H).hom
      (exact_single_shift (restriction J m) (R.obj Pn.H)).hom
      (exact_single_shift (restriction J n) Pn.H).hom
      ((Gm.map beta)⟦(1 : ℤ)⟧')
      ((F.map ((restriction J m).map beta))⟦(1 : ℤ)⟧')
      ((F.map ((restrictionComp h).hom.app Pn.H))⟦(1 : ℤ)⟧')
      Pm.kummer.singleδ Pn.kummer.singleδ (F.map (eqToHom hB))
      hu hv hBadj (exact_single_shift_naturality (restriction J m) beta)
      (exact_comparison_shift_single R (restriction J m) (restriction J n)
        (restrictionComp h) Pn.H) ht
    simpa only [bint, Functor.map_comp] using hs
  have hbint : bint = b₀ := by
    apply F.map_injective
    apply (shiftFunctor (DerivedCategory (Integral J)) (1 : ℤ)).map_injective
    apply single_boundary_injective Pm.kummer ((restriction J n).obj Pn.H) hvan
    exact hbintδ.trans hb₀δ.symm
  refine ⟨eF, eH, beta, ?_, ?_, ?_, hcF, hcB⟩
  · intro U f b
    rw [pure_smul, (eF.hom.val.app U).hom.map_smul]
    congr 1
    have he := ConcreteCategory.congr_hom
      (congrArg (fun z ↦ z.val.app U) hQsquare) f
    change betaQ.val.app U (Pm.p.val.app U f) =
      Pn.p.val.app U ((eqToHom hF).val.app U f) at he
    rw [← ordinary_unit_pure h Dmn Pm.Q U (Pm.p.val.app U f)]
    exact he
  · intro U x
    let x' : ((restriction J m).obj Pm.H).val.obj U := x
    have heq : bint ≫ Pn.i = (m / n) • (Pm.i ≫ eqToHom hB) :=
      (congrArg (fun z ↦ z ≫ Pn.i) hbint).trans hb₀
    have he := ConcreteCategory.congr_hom
      (congrArg (fun z ↦ z.val.app U) heq) x'
    rw [section_nsmul] at he
    exact he
  · intro U x b
    rw [pure_smul, (eH.hom.val.app U).hom.map_smul]
    congr 1
    change eH.hom.val.app U
      (SuccessiveDerivedQuotient.pure (residueProjection (J := J) h) Pm.H U 1 x) = _
    rw [← ordinary_unit_pure h Dmn Pm.H U x]
    rfl

end SheafOfModules.GeoCartierExponent
